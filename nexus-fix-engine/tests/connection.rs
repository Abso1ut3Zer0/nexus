#![cfg(unix)]

//! Socket-setup batteries tests (`FixConnectionBuilder` + `FixConnection`).
//!
//! B — the primary path — is exercised first: `builder.connect(addr, …)` hands back
//! `(FixParts, socket)`, driven with the ordinary three-object loop (zero-copy admin
//! replies), and reconnect keeps the parts while `connect_socket` opens a fresh
//! socket. A — the secondary owns-everything `FixConnection` — is covered by one
//! round-trip (via `open`, with the documented copy-out) plus a `from_parts` /
//! `into_parts` state-preservation check.

use std::io::{self, BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

use nexus_fix_codec::{
    AsciiTextStr, FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{
    CompId, FixConnection, FixConnectionBuilder, FixJournal, FixParts, Message, SessionConfig,
    SessionState, TransportError,
};

// ── mock dictionary (mirrors the conformance suite) ──────────────────────────

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

    fn sender_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>> {
        find_tag(self.buf, 0, 49).and_then(|s| FieldView::new(s, self.buf))
    }

    fn target_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>> {
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

/// Fixed UTC-unix-nanos clock (2026-06-03 16:55:33.000) — the peer asserts every
/// `SendingTime(52)` against it. Both surfaces produce byte-identical frames to the
/// raw session, so the same scenarios pass verbatim.
const NOW: i128 = 1_780_505_733_000_000_000;

/// RAII scratch directory (see the conformance suite for the rationale).
struct TempDir(PathBuf);

impl TempDir {
    fn new(suffix: &str) -> Self {
        let mut p = std::env::temp_dir();
        p.push(format!("nexus_fix_conn_{}_{}", std::process::id(), suffix));
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
    fn wait(&mut self) -> io::Result<std::process::ExitStatus> {
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

fn config() -> SessionConfig {
    SessionConfig {
        sender: CompId::new(b"ENGINE").unwrap(),
        target: CompId::new(b"PEER").unwrap(),
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

enum Step {
    Continue,
    Ended,
}

// ── B (primary): builder → (FixParts, socket) → raw three-object loop ────────

/// Open the socket + trio via the builder — the primary batteries. Returns the raw
/// `(FixParts, socket)`; nothing is bundled.
fn connect_b(port: u16, dir: &Path) -> (FixParts<MockDict>, TcpStream) {
    FixConnectionBuilder::<MockDict>::new()
        .disable_nagle()
        .read_timeout(Duration::from_secs(10))
        .connect(
            ("127.0.0.1", port),
            SessionState::new(Duration::from_secs(30)),
            config(),
            FixJournal::open(dir, 0, 256).unwrap(),
        )
        .unwrap()
}

/// One recv+reply over the raw parts. Destructures `FixParts` so `recv`'s `Message`
/// borrows `reader` only — the reply's `TestReqID` rides straight back **zero-copy**
/// (no copy-out), the whole point of B being primary.
fn step_b(parts: &mut FixParts<MockDict>, sock: &mut TcpStream) -> Result<Step, TransportError> {
    let FixParts {
        session,
        reader,
        writer,
    } = parts;
    match session.recv(reader, writer, sock, NOW)? {
        Some(Message::LoggedOut { .. }) => Ok(Step::Ended),
        Some(Message::LogoutRequest { .. }) => {
            session.logout(writer, sock, NOW, None)?;
            Ok(Step::Ended)
        }
        Some(Message::TestRequest { id }) => {
            session.heartbeat(writer, sock, NOW, Some(id))?; // zero-copy id
            Ok(Step::Continue)
        }
        Some(Message::GapDetected { begin }) => {
            session.resend_request(writer, sock, NOW, begin)?;
            Ok(Step::Continue)
        }
        _ => Ok(Step::Continue),
    }
}

fn drive_b(parts: &mut FixParts<MockDict>, sock: &mut TcpStream) {
    loop {
        match step_b(parts, sock) {
            Ok(Step::Ended) => return,
            Ok(Step::Continue) => {}
            Err(e) => panic!("raw-parts step errored before clean logout: {e:?}"),
        }
    }
}

#[test]
fn builder_connect_roundtrip_logon_logout() {
    let dir = tmp_dir("b_logon_logout");
    let (mut child, port) = spawn_peer("logon_logout");
    let (mut parts, mut sock) = connect_b(port, dir.path());
    parts
        .session
        .connect(&mut parts.writer, &mut sock, NOW)
        .unwrap(); // opening Logon
    drive_b(&mut parts, &mut sock);
    assert!(child.wait().unwrap().success());
}

#[test]
fn builder_connect_roundtrip_heartbeat() {
    let dir = tmp_dir("b_heartbeat");
    let (mut child, port) = spawn_peer("heartbeat");
    let (mut parts, mut sock) = connect_b(port, dir.path());
    parts
        .session
        .connect(&mut parts.writer, &mut sock, NOW)
        .unwrap();
    drive_b(&mut parts, &mut sock);
    assert!(child.wait().unwrap().success());
}

/// Reconnect under B: keep the `FixParts`, open a fresh socket with `connect_socket`.
/// Sequence numbers and the journal live in the retained parts, so the session
/// resumes on the new socket with no re-bundling. A listener (not a live peer) is
/// enough — nothing is read; the assertions are on the preserved state.
#[test]
fn reconnect_keeps_parts_new_socket() {
    let dir = tmp_dir("b_reconnect");
    let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
    let addr = listener.local_addr().unwrap();

    let (mut parts, mut sock) = FixConnectionBuilder::<MockDict>::new()
        .disable_nagle()
        .connect(
            addr,
            SessionState::new(Duration::from_secs(30)),
            config(),
            FixJournal::open(dir.path(), 0, 256).unwrap(),
        )
        .unwrap();

    // Advance outbound state + the journal over the first socket.
    parts
        .session
        .connect(&mut parts.writer, &mut sock, NOW)
        .unwrap(); // Logon consumes seq 1
    let s1 = parts.session.allocate_seq().unwrap();
    parts
        .session
        .send_app(&mut parts.writer, &mut sock, s1, &new_order(s1))
        .unwrap(); // journal stores seq 2
    let next_out = parts.session.state().next_outbound_seq();
    assert_eq!(next_out, 3, "Logon + 1 app send advance outbound to 3");

    // Reconnect: drop the old socket, open a new one — same parts.
    drop(sock);
    let mut sock2 = FixConnectionBuilder::<MockDict>::new()
        .disable_nagle()
        .connect_socket(addr)
        .unwrap();

    assert_eq!(
        parts.session.state().next_outbound_seq(),
        next_out,
        "outbound seqnum survives — it lives in the retained FixParts"
    );

    // The preserved journal keeps counting on the fresh socket.
    let s2 = parts.session.allocate_seq().unwrap();
    assert_eq!(
        s2, next_out,
        "allocate_seq continues from the preserved seqnum"
    );
    parts
        .session
        .send_app(&mut parts.writer, &mut sock2, s2, &new_order(s2))
        .unwrap();
    assert_eq!(parts.session.state().next_outbound_seq(), next_out + 1);
}

// ── A (secondary): FixConnection owns everything ─────────────────────────────

/// One recv+reply through the owns-everything bundle, demonstrating the documented
/// **copy-out**: `recv` borrows the whole `conn`, so the `TestReqID` is copied out
/// of the borrowed `Message` before the reply.
fn step_a(conn: &mut FixConnection<TcpStream, MockDict>) -> Result<Step, TransportError> {
    enum Act {
        None,
        Ended,
        Logout,
        Heartbeat(Vec<u8>),
        Resend(u32),
    }
    let act = match conn.recv(NOW)? {
        Some(Message::LoggedOut { .. }) => Act::Ended,
        Some(Message::LogoutRequest { .. }) => Act::Logout,
        Some(Message::TestRequest { id }) => Act::Heartbeat(id.as_bytes().to_vec()),
        Some(Message::GapDetected { begin }) => Act::Resend(begin),
        _ => Act::None,
    };
    match act {
        Act::None => Ok(Step::Continue),
        Act::Ended => Ok(Step::Ended),
        Act::Logout => {
            conn.logout(NOW, None)?;
            Ok(Step::Ended)
        }
        Act::Heartbeat(bytes) => {
            let id = AsciiTextStr::try_from_bytes(&bytes).unwrap();
            conn.heartbeat(NOW, Some(id))?;
            Ok(Step::Continue)
        }
        Act::Resend(begin) => {
            conn.resend_request(NOW, begin)?;
            Ok(Step::Continue)
        }
    }
}

#[test]
fn bundle_open_roundtrip_heartbeat() {
    let dir = tmp_dir("a_heartbeat");
    let (mut child, port) = spawn_peer("heartbeat");
    // One-step A construction.
    let mut conn = FixConnection::<TcpStream, MockDict>::open(
        ("127.0.0.1", port),
        SessionState::new(Duration::from_secs(30)),
        config(),
        FixJournal::open(dir.path(), 0, 256).unwrap(),
    )
    .unwrap();
    conn.stream()
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    conn.connect(NOW).unwrap(); // opening Logon
    loop {
        match step_a(&mut conn) {
            Ok(Step::Ended) => break,
            Ok(Step::Continue) => {}
            Err(e) => panic!("bundle step errored before clean logout: {e:?}"),
        }
    }
    assert!(child.wait().unwrap().success());
}

/// A-side reconnect + state preservation across the `FixParts` ⇄ bundle boundary:
/// `from_parts` → advance → `into_parts` → rebundle preserves seqnums and the
/// journal. Offline (a `Discard` socket) so the assertions are deterministic.
struct Discard;

impl Read for Discard {
    fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
        Ok(0)
    }
}

impl Write for Discard {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn bundle_into_from_parts_preserves_state() {
    let dir = tmp_dir("a_reconnect");
    // Build parts via the builder's `accept` (offline), bundle them into A.
    let (parts, sock) = FixConnectionBuilder::<MockDict>::new().accept(
        Discard,
        SessionState::new(Duration::from_secs(45)),
        config(),
        FixJournal::open(dir.path(), 0, 256).unwrap(),
    );
    let mut conn = FixConnection::from_parts(parts, sock);

    conn.connect(NOW).unwrap(); // Logon consumes outbound seq 1
    let s1 = conn.allocate_seq().unwrap();
    conn.send_app(s1, &new_order(s1)).unwrap(); // journal stores seq 2
    let next_out = conn.state().next_outbound_seq();
    let next_in = conn.state().next_inbound_seq();
    let hbi = conn.heartbeat_interval();
    assert_eq!(next_out, 3);
    assert_eq!(hbi, Duration::from_secs(45));

    // Unbundle to the raw parts, rebundle with a fresh socket — state survives.
    let (parts, _old) = conn.into_parts();
    let mut conn2 = FixConnection::from_parts(parts, Discard);

    assert_eq!(conn2.state().next_outbound_seq(), next_out);
    assert_eq!(conn2.state().next_inbound_seq(), next_in);
    assert_eq!(conn2.heartbeat_interval(), hbi);

    let s2 = conn2.allocate_seq().unwrap();
    assert_eq!(s2, next_out, "the preserved journal keeps counting");
    conn2.send_app(s2, &new_order(s2)).unwrap();
    assert_eq!(conn2.state().next_outbound_seq(), next_out + 1);
}
