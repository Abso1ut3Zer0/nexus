#![cfg(unix)]

use std::io::BufRead;
use std::io::BufReader;
use std::io::Write;
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

use nexus_fix_codec::{
    FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{
    CompId, DisconnectReason, FixJournal, FixParts, FixSession, Message, MessageReader,
    MessageWriter, SessionConfig, SessionError, SessionState, State, TransportError,
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

/// Test-local bundle over the three-object API: the sans-IO [`FixSession`] brain
/// plus its caller-held `reader`/`writer` and the owned socket. Each method is a
/// one-liner over `session.recv(&mut reader, &mut writer, &mut stream)` and the
/// encode-only send helpers — a preview of the phase-6 bundle, kept in the test
/// so the scenario bodies read the same across the un-nesting.
/// Fixed UTC-unix-nanos clock (2026-06-03 16:55:33.000). The engine stamps every
/// `SendingTime(52)` from this, so the peer asserts it exactly (see `ENGINE_ST` in
/// `fix_peer.py`).
const NOW: i128 = 1_780_505_733_000_000_000;

/// The classification of one recv+reply [`Rig::step`] the drive loops branch on.
enum Step {
    /// Nothing test-visible surfaced (or a no-reply message was handled).
    Continue,
    /// An in-order application message surfaced.
    App,
    /// The session reached a clean logout terminal — either `LoggedOut` (our
    /// initiated logout confirmed) or a peer `LogoutRequest` we just answered.
    Ended,
}

struct Rig {
    session: FixSession<MockDict>,
    reader: MessageReader<MockDict>,
    writer: MessageWriter<MockDict>,
    stream: TcpStream,
}

impl Rig {
    /// Receive the next message and drive its required reply — the user-driven
    /// model: where the engine used to auto-reply, the test now sends the reply
    /// with the send helpers. Same messages on the wire, in the same order; only
    /// who emits them moves from engine to test.
    ///
    /// Destructures `self` so `recv`'s returned `Message` borrows `reader` only,
    /// leaving `session`/`writer`/`stream` free for the reply (contract §5).
    fn step(&mut self) -> Result<Step, TransportError> {
        let Rig {
            session,
            reader,
            writer,
            stream,
        } = self;
        match session.recv(reader, writer, stream, NOW)? {
            Some(Message::LoggedOut { .. }) => Ok(Step::Ended),
            Some(Message::LogoutRequest { .. }) => {
                session.logout(writer, stream, NOW, None)?;
                Ok(Step::Ended)
            }
            Some(Message::TestRequest { id }) => {
                session.heartbeat(writer, stream, NOW, Some(id))?;
                Ok(Step::Continue)
            }
            Some(Message::GapDetected { begin }) => {
                session.resend_request(writer, stream, NOW, begin)?;
                Ok(Step::Continue)
            }
            Some(Message::LogonRequest(d) | Message::LogonResetRequest(d)) => {
                d.accept(session, writer, stream, NOW)?;
                Ok(Step::Continue)
            }
            Some(Message::ResendRequest { cursor }) => {
                // Pump the cursor: reframe each item into `writer`, write it, repeat
                // until Done (same wire output the engine used to auto-drive).
                let mut c = cursor;
                while let Some(bytes) = c.next(session, writer, NOW)? {
                    stream.write_all(bytes).map_err(TransportError::Io)?;
                }
                stream.flush().map_err(TransportError::Io)?;
                Ok(Step::Continue)
            }
            Some(Message::ResendOutOfRange {
                begin,
                low_water,
                high_water,
                ..
            }) => {
                if begin < low_water {
                    session.gap_fill(writer, stream, NOW, begin, high_water + 1)?;
                } else {
                    session.sequence_reset(writer, stream, NOW, high_water + 1)?;
                }
                Ok(Step::Continue)
            }
            Some(Message::Application { .. }) => Ok(Step::App),
            // Heartbeat / Reject / SequenceReset / LogonAcknowledged — no reply
            // required — or nothing surfaced (`None`).
            _ => Ok(Step::Continue),
        }
    }
    fn connect(&mut self) -> Result<(), TransportError> {
        self.session.encode_connect(&mut self.writer, NOW)
    }
    fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), TransportError> {
        self.session.encode_send_app(&mut self.writer, seq, frame)
    }
    fn allocate_seq(&mut self) -> Result<u32, SessionError> {
        self.session.allocate_seq()
    }
    fn state(&self) -> &SessionState {
        self.session.state()
    }
}

fn connect(port: u16, dir: &Path) -> Rig {
    let stream = TcpStream::connect(("127.0.0.1", port)).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    let FixParts {
        session,
        reader,
        writer,
    } = FixSession::builder().build(
        SessionState::new(Duration::from_secs(30)),
        SessionConfig {
            sender: CompId::new(b"ENGINE").unwrap(),
            target: CompId::new(b"PEER").unwrap(),
        },
        FixJournal::open(dir, 0, 256).unwrap(),
    );
    Rig {
        session,
        reader,
        writer,
        stream,
    }
}

/// Drive until the session completes a clean, negotiated logout — either the peer
/// confirms our logout (`LoggedOut`) or the peer initiates one we answer
/// (`LogoutRequest`). Every scenario here ends in a peer-sent Logout, so any error
/// is a failure and panics.
fn drive(conn: &mut Rig) {
    loop {
        match conn.step() {
            Ok(Step::Ended) => return,
            Ok(_) => {}
            Err(e) => panic!("step errored before clean logout: {e:?}"),
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
    conn.connect().unwrap();
    drive(&mut conn);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_heartbeat() {
    let dir = tmp_dir("heartbeat");
    let (mut child, port) = spawn_peer("heartbeat");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();
    drive(&mut conn);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_resend() {
    let dir = tmp_dir("resend");
    let (mut child, port) = spawn_peer("resend");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();

    drive_to_active(&mut conn);

    let seq = conn.allocate_seq().unwrap();
    conn.send_app(seq, &new_order(seq)).unwrap();

    drive(&mut conn);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_gap_fill() {
    let dir = tmp_dir("gap_fill");
    let (mut child, port) = spawn_peer("gap_fill");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();
    drive(&mut conn);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_seq_reset() {
    let dir = tmp_dir("seq_reset");
    let (mut child, port) = spawn_peer("seq_reset");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();
    drive(&mut conn);
    assert!(child.wait().unwrap().success());
}

// ── battle-test scenarios (Tier 1 sequence-number + Tier 3 liveness) ─────────
//
// See `.claude/fix-battletest-findings.md` for the pass/finding disposition of
// each case and the FIX 4.4 rationale behind every assertion.

/// Drive `recv` to a terminal outcome, recording whether `Resending` was ever
/// entered and whether an `Application` message surfaced. Returns the disconnect
/// reason: `None` for a clean, negotiated logout (`Message::LoggedOut`), or
/// `Some(reason)` for an abnormal end (`TransportError::UnexpectedDisconnect`).
/// Any other `recv` error mid-scenario is a survivability failure — the engine
/// must resolve every step to a message / suppression / logout / fault, never a
/// raw transport error — so it panics (surfacing a finding as a test failure).
fn drive_observe(conn: &mut Rig) -> (Option<DisconnectReason>, bool, bool) {
    let mut saw_resending = false;
    let mut saw_app = false;
    loop {
        match conn.step() {
            Ok(Step::Ended) => return (None, saw_resending, saw_app),
            Ok(Step::App) => saw_app = true,
            Ok(Step::Continue) => {}
            Err(TransportError::UnexpectedDisconnect { reason }) => {
                return (Some(reason), saw_resending, saw_app);
            }
            Err(e) => panic!("step errored mid-scenario: {e:?}"),
        }
        if conn.state().state() == State::Resending {
            saw_resending = true;
        }
    }
}

/// Drive until the session reaches `Active`, panicking on an early logout or
/// error. Used by the resend scenarios that inject app messages once live.
fn drive_to_active(conn: &mut Rig) {
    loop {
        match conn.step() {
            Ok(Step::Ended) => panic!("logged out before active"),
            Err(e) => panic!("disconnected before active: {e:?}"),
            Ok(_) => {}
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
    conn.connect().unwrap();
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
    conn.connect().unwrap();
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, Some(DisconnectReason::SeqNumTooLow));
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_seq_too_low_poss_dup() {
    let dir = tmp_dir("seq_too_low_poss_dup");
    let (mut child, port) = spawn_peer("seq_too_low_poss_dup");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();
    // The PossDup duplicate is ignored; the session survives to a clean logout.
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_app_in_order() {
    let dir = tmp_dir("app_in_order");
    let (mut child, port) = spawn_peer("app_in_order");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();
    let (reason, _, saw_app) = drive_observe(&mut conn);
    assert!(
        saw_app,
        "an in-order app must surface as Message::Application"
    );
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_resend_open_ended() {
    let dir = tmp_dir("resend_open_ended");
    let (mut child, port) = spawn_peer("resend_open_ended");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();
    drive_to_active(&mut conn);
    let seq = conn.allocate_seq().unwrap();
    conn.send_app(seq, &new_order(seq)).unwrap();
    // The peer asserts the open-ended (EndSeqNo=0) replay covers everything sent.
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_resend_admin_and_app() {
    let dir = tmp_dir("resend_admin_and_app");
    let (mut child, port) = spawn_peer("resend_admin_and_app");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();
    drive_to_active(&mut conn);
    for _ in 0..2 {
        let seq = conn.allocate_seq().unwrap();
        conn.send_app(seq, &new_order(seq)).unwrap();
    }
    // The peer asserts admin holes gap-fill and app messages replay with PossDup.
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_resend_during_resend() {
    let dir = tmp_dir("resend_during_resend");
    let (mut child, port) = spawn_peer("resend_during_resend");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();
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
    conn.connect().unwrap();
    // A backward SequenceReset-Reset is Reject'd (peer asserts 35=3); the session
    // is NOT torn down — it continues to a clean logout.
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_seq_reset_gap_fill_oos() {
    let dir = tmp_dir("seq_reset_gap_fill_oos");
    let (mut child, port) = spawn_peer("seq_reset_gap_fill_oos");
    let mut conn = connect(port, dir.path());
    conn.connect().unwrap();
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
    conn.connect().unwrap();
    // The peer asserts the >64-byte TestReqID is echoed verbatim (no truncation).
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, None);
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
    conn.connect().unwrap();
    let (reason, _, _) = drive_observe(&mut conn);
    assert_eq!(reason, None);
    assert!(child.wait().unwrap().success());
}
