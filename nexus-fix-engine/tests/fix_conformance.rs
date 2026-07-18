#![cfg(unix)]

use std::io::BufRead;
use std::io::BufReader;
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use nexus_fix_codec::{
    FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{
    CompId, DisconnectReason, FixConnection, FixJournal, Message, SessionConfig, SessionState,
    State,
};

// ── mock dictionary ──────────────────────────────────────────────────────────

struct MockDict;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum MockMsgType {}

struct AdminDecoder<'buf> {
    _buf: &'buf [u8],
}

impl<'buf> FixAdminMsg<'buf> for AdminDecoder<'buf> {
    fn decode(buf: &'buf [u8]) -> Result<Self, nexus_fix_codec::DecodeError> {
        Ok(Self { _buf: buf })
    }
}

impl FixDictionary for MockDict {
    type MsgType = MockMsgType;
    type Header<'buf> = MockHeader<'buf>;
    type Logon<'buf> = AdminDecoder<'buf>;
    type Logout<'buf> = AdminDecoder<'buf>;
    type Heartbeat<'buf> = AdminDecoder<'buf>;
    type TestRequest<'buf> = AdminDecoder<'buf>;
    type ResendRequest<'buf> = AdminDecoder<'buf>;
    type SequenceReset<'buf> = AdminDecoder<'buf>;
    type Reject<'buf> = AdminDecoder<'buf>;
    const BEGIN_STRING: &'static [u8] = b"FIX.4.4";
    fn is_admin(_: MockMsgType) -> bool {
        false
    }
}

struct MockHeader<'buf> {
    buf: &'buf [u8],
}

impl<'buf> FixHeader<'buf> for MockHeader<'buf> {
    fn decode(buf: &'buf [u8]) -> Self {
        Self { buf }
    }

    fn raw_msg_type(&self) -> Option<FieldView<'buf, &'buf [u8]>> {
        find_tag(self.buf, 0, 35).and_then(|s| FieldView::new(s, self.buf))
    }

    fn msg_seq_num(&self) -> Option<FieldView<'buf, u64>> {
        find_tag(self.buf, 0, 34).and_then(|s| FieldView::new(s, self.buf))
    }

    fn sender_comp_id(&self) -> Option<FieldView<'buf, &'buf nexus_fix_codec::AsciiTextStr>> {
        find_tag(self.buf, 0, 49).and_then(|s| FieldView::new(s, self.buf))
    }

    fn target_comp_id(&self) -> Option<FieldView<'buf, &'buf nexus_fix_codec::AsciiTextStr>> {
        find_tag(self.buf, 0, 56).and_then(|s| FieldView::new(s, self.buf))
    }

    fn poss_dup_flag(&self) -> Option<FieldView<'buf, bool>> {
        find_tag(self.buf, 0, 43).and_then(|s| FieldView::new(s, self.buf))
    }

    fn sending_time(&self) -> Option<FieldView<'buf, FixTimestamp>> {
        None
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────

const PEER: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/fix_peer.py");

/// RAII scratch directory. `FixJournal::open` preallocates tens of megabytes
/// into each of these, so they must not outlive the test that made them.
/// `Drop` also runs while unwinding, so a *failing* test cleans up too — which
/// a manual `cleanup(&dir)` at the end of the body would not.
///
/// Bind it to a live local (`let dir = tmp_dir(..)`), never `let _ = ..`, or
/// the directory is removed before the test can use it.
struct TempDir(PathBuf);

impl TempDir {
    fn new(suffix: &str) -> Self {
        let mut p = std::env::temp_dir();
        p.push(format!("nexus_fix_conf_{}_{}", std::process::id(), suffix));
        // A previous run killed by a signal can leave the tree behind, and PIDs
        // get recycled -- start from a clean slate.
        let _ = std::fs::remove_dir_all(&p);
        std::fs::create_dir_all(&p).unwrap();
        Self(p)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn tmp_dir(suffix: &str) -> TempDir {
    TempDir::new(suffix)
}

struct ChildGuard(std::process::Child);

impl Drop for ChildGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
    }
}

impl ChildGuard {
    fn wait(&mut self) -> std::io::Result<std::process::ExitStatus> {
        self.0.wait()
    }
}

fn spawn_peer(scenario: &str) -> (ChildGuard, u16) {
    let mut child = Command::new("python3")
        .arg(PEER)
        .arg(scenario)
        .stdout(Stdio::piped())
        .spawn()
        .expect("python3 not found");
    let stdout = child.stdout.take().unwrap();
    let mut line = String::new();
    BufReader::new(stdout).read_line(&mut line).unwrap();
    let port: u16 = line.trim().parse().unwrap();
    (ChildGuard(child), port)
}

fn connect(port: u16, dir: &Path) -> FixConnection<TcpStream, MockDict> {
    let stream = TcpStream::connect(("127.0.0.1", port)).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    FixConnection::from_parts(
        stream,
        SessionState::new(Duration::from_secs(30)),
        SessionConfig {
            sender: CompId::new(b"ENGINE").unwrap(),
            target: CompId::new(b"PEER").unwrap(),
        },
        FixJournal::open(dir, 0, 256).unwrap(),
    )
}

fn drive(conn: &mut FixConnection<TcpStream, MockDict>) -> DisconnectReason {
    loop {
        if let Some(Message::Disconnected { reason }) = conn.recv(Instant::now()).unwrap() {
            return reason;
        }
    }
}

fn new_order(seq: u32) -> Vec<u8> {
    let mut buf = [0u8; 512];
    let mut seq_buf = [0u8; 10];
    let n = encode_fix_uint(seq, &mut seq_buf);
    let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
    fmt.field(34, &seq_buf[..n]);
    fmt.field(49, b"ENGINE");
    fmt.field(56, b"PEER");
    fmt.field(52, b"20260101-00:00:00.000");
    fmt.field(11, b"ORD-1");
    let (start, len) = fmt.finish().unwrap();
    buf[start..start + len].to_vec()
}

// ── tests ────────────────────────────────────────────────────────────────────

#[test]
fn conformance_logon_logout() {
    let dir = tmp_dir("logon_logout");
    let (mut child, port) = spawn_peer("logon_logout");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_heartbeat() {
    let dir = tmp_dir("heartbeat");
    let (mut child, port) = spawn_peer("heartbeat");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_resend() {
    let dir = tmp_dir("resend");
    let (mut child, port) = spawn_peer("resend");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();

    loop {
        if let Some(Message::Disconnected { reason }) = conn.recv(Instant::now()).unwrap() {
            panic!("disconnected before active: {reason:?}");
        }
        if conn.state().state() == State::Active {
            break;
        }
    }

    let seq = conn.allocate_seq().unwrap();
    conn.send_app(seq, &new_order(seq)).unwrap();

    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_gap_fill() {
    let dir = tmp_dir("gap_fill");
    let (mut child, port) = spawn_peer("gap_fill");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_seq_reset() {
    let dir = tmp_dir("seq_reset");
    let (mut child, port) = spawn_peer("seq_reset");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

// ── battle-test scenarios (Tier 1 sequence-number + Tier 3 liveness) ─────────
//
// See `.claude/fix-battletest-findings.md` for the pass/finding disposition of
// each case and the FIX 4.4 rationale behind every assertion.

/// Like [`connect`] but with a caller-chosen socket read timeout — needed for
/// the timer scenario, where the read must unblock faster than the (fixed 10s)
/// default so `on_timeout` fires promptly.
fn connect_rt(port: u16, dir: &Path, read_timeout: Duration) -> FixConnection<TcpStream, MockDict> {
    let stream = TcpStream::connect(("127.0.0.1", port)).unwrap();
    stream.set_read_timeout(Some(read_timeout)).unwrap();
    FixConnection::from_parts(
        stream,
        SessionState::new(Duration::from_secs(30)),
        SessionConfig {
            sender: CompId::new(b"ENGINE").unwrap(),
            target: CompId::new(b"PEER").unwrap(),
        },
        FixJournal::open(dir, 0, 256).unwrap(),
    )
}

/// Drive `recv` to a disconnect, recording whether `Resending` was ever entered
/// and whether an `Application` message surfaced. A `recv` error mid-scenario is
/// a survivability failure — the engine must resolve every step to a message /
/// suppression / clean disconnect, never a raw error — so it panics (surfacing a
/// finding as a test failure).
fn drive_observe(conn: &mut FixConnection<TcpStream, MockDict>) -> (DisconnectReason, bool, bool) {
    let mut saw_resending = false;
    let mut saw_app = false;
    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { reason })) => return (reason, saw_resending, saw_app),
            Ok(Some(Message::Application { .. })) => saw_app = true,
            Ok(Some(_) | None) => {}
            Err(e) => panic!("recv errored mid-scenario: {e:?}"),
        }
        if conn.state().state() == State::Resending {
            saw_resending = true;
        }
    }
}

/// Drive until the session reaches `Active`, panicking on an early disconnect or
/// error. Used by the resend scenarios that inject app messages once live.
fn drive_to_active(conn: &mut FixConnection<TcpStream, MockDict>) {
    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { reason })) => {
                panic!("disconnected before active: {reason:?}")
            }
            Err(e) => panic!("recv errored before active: {e:?}"),
            _ => {}
        }
        if conn.state().state() == State::Active {
            break;
        }
    }
}

// Tier 1 — sequence-number correctness.

#[test]
fn conformance_app_seq_too_high() {
    let dir = tmp_dir("app_seq_too_high");
    let (mut child, port) = spawn_peer("app_seq_too_high");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    let (_reason, saw_resending, saw_app) = drive_observe(&mut conn);
    assert!(
        saw_resending,
        "an inbound gap must send a ResendRequest and enter Resending"
    );
    assert!(
        !saw_app,
        "an out-of-sequence app must not surface to the application"
    );
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_app_seq_too_low() {
    let dir = tmp_dir("app_seq_too_low");
    let (mut child, port) = spawn_peer("app_seq_too_low");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, DisconnectReason::SeqNumTooLow);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_seq_too_low_poss_dup() {
    let dir = tmp_dir("seq_too_low_poss_dup");
    let (mut child, port) = spawn_peer("seq_too_low_poss_dup");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    // The PossDup duplicate is ignored; the session survives to a clean logout.
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_app_in_order() {
    let dir = tmp_dir("app_in_order");
    let (mut child, port) = spawn_peer("app_in_order");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    let (reason, _, saw_app) = drive_observe(&mut conn);
    assert!(
        saw_app,
        "an in-order app must surface as Message::Application"
    );
    assert_eq!(reason, DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_resend_open_ended() {
    let dir = tmp_dir("resend_open_ended");
    let (mut child, port) = spawn_peer("resend_open_ended");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    drive_to_active(&mut conn);
    let seq = conn.allocate_seq().unwrap();
    conn.send_app(seq, &new_order(seq)).unwrap();
    // The peer asserts the open-ended (EndSeqNo=0) replay covers everything sent.
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_resend_admin_and_app() {
    let dir = tmp_dir("resend_admin_and_app");
    let (mut child, port) = spawn_peer("resend_admin_and_app");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    drive_to_active(&mut conn);
    for _ in 0..2 {
        let seq = conn.allocate_seq().unwrap();
        conn.send_app(seq, &new_order(seq)).unwrap();
    }
    // The peer asserts admin holes gap-fill and app messages replay with PossDup.
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_resend_during_resend() {
    let dir = tmp_dir("resend_during_resend");
    let (mut child, port) = spawn_peer("resend_during_resend");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    // Engine enters Resending on its own gap, then must honor the peer's
    // in-sequence ResendRequest without erroring (drive_observe panics on error).
    let (_reason, saw_resending, _) = drive_observe(&mut conn);
    assert!(
        saw_resending,
        "engine must enter Resending on its own inbound gap"
    );
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_seq_reset_backward() {
    let dir = tmp_dir("seq_reset_backward");
    let (mut child, port) = spawn_peer("seq_reset_backward");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    // A backward SequenceReset-Reset is Reject'd (peer asserts 35=3); the session
    // is NOT torn down — it continues to a clean logout.
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_seq_reset_gap_fill_oos() {
    let dir = tmp_dir("seq_reset_gap_fill_oos");
    let (mut child, port) = spawn_peer("seq_reset_gap_fill_oos");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    let (_reason, saw_resending, _) = drive_observe(&mut conn);
    assert!(
        saw_resending,
        "an out-of-sequence GapFill must be treated as a gap (ResendRequest → Resending)"
    );
    assert_eq!(
        conn.state().next_inbound_seq(),
        2,
        "an out-of-sequence GapFill must not advance next_inbound to NewSeqNo"
    );
    assert!(child.wait().unwrap().success());
}

// Tier 3 — liveness.

#[test]
fn conformance_test_request_long_id() {
    let dir = tmp_dir("test_request_long_id");
    let (mut child, port) = spawn_peer("test_request_long_id");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    // The peer asserts the >64-byte TestReqID is echoed verbatim (no truncation).
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_test_request_timeout() {
    let dir = tmp_dir("test_request_timeout");
    let (mut child, port) = spawn_peer("test_request_timeout");
    // Short read timeout so `on_timeout` is polled well inside the 1s heartbeat.
    let mut conn = connect_rt(port, dir.path(), Duration::from_millis(200));
    conn.connect(Instant::now()).unwrap();
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, DisconnectReason::TestRequestTimeout);
    assert!(child.wait().unwrap().success());
}

// Regression for confirmed engine bug Q1 (see .claude/fix-battletest-findings.md):
// a below-expected SequenceReset-GapFill carrying PossDupFlag=Y must be discarded
// (the session survives), NOT treated as SeqNumTooLow. The engine currently
// disconnects because `on_sequence_reset` hard-codes `poss_dup=false`, so this
// asserts the CORRECT behavior and fails today — kept `#[ignore]`'d until the fix.
#[test]
fn conformance_seq_reset_gap_fill_below_possdup() {
    let dir = tmp_dir("seq_reset_gap_fill_below_possdup");
    let (mut child, port) = spawn_peer("seq_reset_gap_fill_below_possdup");
    let mut conn = connect(port, dir.path());
    conn.connect(Instant::now()).unwrap();
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}
