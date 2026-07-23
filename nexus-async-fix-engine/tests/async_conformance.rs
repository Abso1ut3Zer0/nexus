#![cfg(unix)]

use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

use nexus_async_fix_engine::{AsyncReadAdapter, FixConnection};
use nexus_fix_codec::{
    FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{
    CompId, DisconnectReason, FixJournal, Message, SessionConfig, SessionState, State,
    TransportError,
};
use tokio::net::TcpStream;

// ── mock dictionary (mirrors the sync engine's tests) ────────────────────────

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

const BEGIN: &[u8] = b"FIX.4.4";
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
        p.push(format!(
            "nexus_async_fix_conf_{}_{}",
            std::process::id(),
            suffix
        ));
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

fn spawn_peer(scenario: &str) -> (std::process::Child, u16) {
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
    (child, port)
}

async fn connect(port: u16, dir: &Path) -> FixConnection<AsyncReadAdapter<TcpStream>, MockDict> {
    let stream = TcpStream::connect(("127.0.0.1", port)).await.unwrap();
    FixConnection::from_parts(
        AsyncReadAdapter::new(stream),
        SessionState::new(Duration::from_secs(30)),
        SessionConfig {
            sender: CompId::new(b"ENGINE").unwrap(),
            target: CompId::new(b"PEER").unwrap(),
        },
        FixJournal::open(dir, 0, 256).unwrap(),
    )
}

/// Drive `recv` until the session completes a clean, negotiated logout
/// (`Message::LoggedOut`). Every scenario here ends in a peer-sent Logout, so any
/// error is a failure and panics.
async fn drive(conn: &mut FixConnection<AsyncReadAdapter<TcpStream>, MockDict>) {
    loop {
        match conn.recv().await {
            Ok(Some(Message::LoggedOut { .. })) => return,
            Ok(_) => {}
            Err(e) => panic!("recv errored before clean logout: {e:?}"),
        }
    }
}

fn new_order(seq: u32) -> Vec<u8> {
    let mut buf = [0u8; 512];
    let mut seq_buf = [0u8; 10];
    let n = encode_fix_uint(seq, &mut seq_buf);
    let mut fmt = FrameFormatter::new(&mut buf, BEGIN, b"D");
    fmt.field(34, &seq_buf[..n]);
    fmt.field(49, b"ENGINE");
    fmt.field(56, b"PEER");
    fmt.field(52, b"20260101-00:00:00.000");
    fmt.field(11, b"ORD-1");
    let (start, len) = fmt.finish().unwrap();
    buf[start..start + len].to_vec()
}

// ── tests ────────────────────────────────────────────────────────────────────

#[tokio::test]
async fn conformance_logon_logout() {
    let dir = tmp_dir("logon_logout");
    let (mut child, port) = spawn_peer("logon_logout");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    drive(&mut conn).await;
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_heartbeat() {
    let dir = tmp_dir("heartbeat");
    let (mut child, port) = spawn_peer("heartbeat");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    drive(&mut conn).await;
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_resend() {
    let dir = tmp_dir("resend");
    let (mut child, port) = spawn_peer("resend");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();

    drive_to_active(&mut conn).await;

    let seq = conn.allocate_seq().unwrap();
    conn.send_app(seq, &new_order(seq)).await.unwrap();

    drive(&mut conn).await;
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_gap_fill() {
    let dir = tmp_dir("gap_fill");
    let (mut child, port) = spawn_peer("gap_fill");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    drive(&mut conn).await;
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_seq_reset() {
    let dir = tmp_dir("seq_reset");
    let (mut child, port) = spawn_peer("seq_reset");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    drive(&mut conn).await;
    assert!(child.wait().unwrap().success());
}

// ── battle-test scenarios (Tier 1 sequence-number + Tier 3 liveness) ─────────
//
// Mirror of the sync `fix_conformance.rs` cases over the tokio transport, so the
// two drivers stay in lockstep. See `.claude/fix-battletest-findings.md` for the
// pass/finding disposition and the FIX 4.4 rationale behind each assertion. The
// session holds no timers, so `recv` simply awaits a full frame; the caller runs
// its own liveness timers (not exercised by these scenarios).

type Conn = FixConnection<AsyncReadAdapter<TcpStream>, MockDict>;

/// Drive `recv` to a terminal outcome, recording whether `Resending` was entered
/// and whether an `Application` surfaced. Returns the disconnect reason: `None`
/// for a clean, negotiated logout (`Message::LoggedOut`), or `Some(reason)` for
/// an abnormal end (`TransportError::UnexpectedDisconnect`). Any other `recv`
/// error mid-scenario is a survivability failure, so it panics (surfacing a
/// finding as a test failure).
async fn drive_observe(conn: &mut Conn) -> (Option<DisconnectReason>, bool, bool) {
    let mut saw_resending = false;
    let mut saw_app = false;
    loop {
        match conn.recv().await {
            Ok(Some(Message::LoggedOut { .. })) => return (None, saw_resending, saw_app),
            Ok(Some(Message::Application { .. })) => saw_app = true,
            Ok(Some(_) | None) => {}
            Err(TransportError::UnexpectedDisconnect { reason }) => {
                return (Some(reason), saw_resending, saw_app);
            }
            Err(e) => panic!("recv errored mid-scenario: {e:?}"),
        }
        if conn.state().state() == State::Resending {
            saw_resending = true;
        }
    }
}

/// Drive until the session reaches `Active`, panicking on an early disconnect.
async fn drive_to_active(conn: &mut Conn) {
    loop {
        match conn.recv().await {
            Ok(Some(Message::LoggedOut { .. })) => panic!("logged out before active"),
            Err(e) => panic!("disconnected before active: {e:?}"),
            _ => {}
        }
        if conn.state().state() == State::Active {
            break;
        }
    }
}

// Tier 1 — sequence-number correctness.

#[tokio::test]
async fn conformance_app_seq_too_high() {
    let dir = tmp_dir("app_seq_too_high");
    let (mut child, port) = spawn_peer("app_seq_too_high");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    let (_reason, saw_resending, saw_app) = drive_observe(&mut conn).await;
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

#[tokio::test]
async fn conformance_app_seq_too_low() {
    let dir = tmp_dir("app_seq_too_low");
    let (mut child, port) = spawn_peer("app_seq_too_low");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    let (reason, _, _) = drive_observe(&mut conn).await;
    assert_eq!(reason, Some(DisconnectReason::SeqNumTooLow));
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_seq_too_low_poss_dup() {
    let dir = tmp_dir("seq_too_low_poss_dup");
    let (mut child, port) = spawn_peer("seq_too_low_poss_dup");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    let (reason, _, _) = drive_observe(&mut conn).await;
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_app_in_order() {
    let dir = tmp_dir("app_in_order");
    let (mut child, port) = spawn_peer("app_in_order");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    let (reason, _, saw_app) = drive_observe(&mut conn).await;
    assert!(
        saw_app,
        "an in-order app must surface as Message::Application"
    );
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_resend_open_ended() {
    let dir = tmp_dir("resend_open_ended");
    let (mut child, port) = spawn_peer("resend_open_ended");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    drive_to_active(&mut conn).await;
    let seq = conn.allocate_seq().unwrap();
    conn.send_app(seq, &new_order(seq)).await.unwrap();
    let (reason, _, _) = drive_observe(&mut conn).await;
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_resend_admin_and_app() {
    let dir = tmp_dir("resend_admin_and_app");
    let (mut child, port) = spawn_peer("resend_admin_and_app");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    drive_to_active(&mut conn).await;
    for _ in 0..2 {
        let seq = conn.allocate_seq().unwrap();
        conn.send_app(seq, &new_order(seq)).await.unwrap();
    }
    let (reason, _, _) = drive_observe(&mut conn).await;
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_resend_during_resend() {
    let dir = tmp_dir("resend_during_resend");
    let (mut child, port) = spawn_peer("resend_during_resend");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    let (_reason, saw_resending, _) = drive_observe(&mut conn).await;
    assert!(
        saw_resending,
        "engine must enter Resending on its own inbound gap"
    );
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_seq_reset_backward() {
    let dir = tmp_dir("seq_reset_backward");
    let (mut child, port) = spawn_peer("seq_reset_backward");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    let (reason, _, _) = drive_observe(&mut conn).await;
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn conformance_seq_reset_gap_fill_oos() {
    let dir = tmp_dir("seq_reset_gap_fill_oos");
    let (mut child, port) = spawn_peer("seq_reset_gap_fill_oos");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    let (_reason, saw_resending, _) = drive_observe(&mut conn).await;
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

#[tokio::test]
async fn conformance_test_request_long_id() {
    let dir = tmp_dir("test_request_long_id");
    let (mut child, port) = spawn_peer("test_request_long_id");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    let (reason, _, _) = drive_observe(&mut conn).await;
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

// Regression for confirmed engine bug Q1 (see .claude/fix-battletest-findings.md):
// a below-expected SequenceReset-GapFill carrying PossDupFlag=Y must be discarded
// (the session survives), NOT treated as SeqNumTooLow. Asserts the CORRECT
// behavior and fails today — kept `#[ignore]`'d until the engine fix lands.
#[tokio::test]
async fn conformance_seq_reset_gap_fill_below_possdup() {
    let dir = tmp_dir("seq_reset_gap_fill_below_possdup");
    let (mut child, port) = spawn_peer("seq_reset_gap_fill_below_possdup");
    let mut conn = connect(port, dir.path()).await;
    conn.connect().await.unwrap();
    let (reason, _, _) = drive_observe(&mut conn).await;
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}
