#![cfg(unix)]

//! Socket-setup batteries tests — the async twin of the `nexus-fix-engine` bundle
//! tests.
//!
//! B — the primary path — is exercised first: `builder.connect(addr, …).await` hands
//! back `(FixParts, transport)`, driven with the ordinary three-object loop
//! (zero-copy admin replies), and reconnect keeps the parts while `connect_socket`
//! opens a fresh transport. A — the secondary owns-everything `FixConnection` — is
//! covered by one round-trip (via `open`, with the documented copy-out) plus a
//! `from_parts` / `into_parts` state check. Under the `tls` feature, `connect_tls` is
//! exercised end to end.

use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

use nexus_async_fix_engine::{FixConnection, FixConnectionBuilder, FixParts, MaybeTls};
use nexus_fix_codec::{
    AsciiTextStr, FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{CompId, FixJournal, Message, SessionConfig, SessionState, TransportError};

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
const NOW: i128 = 1_780_505_733_000_000_000;

struct TempDir(PathBuf);

impl TempDir {
    fn new(suffix: &str) -> Self {
        let mut p = std::env::temp_dir();
        p.push(format!(
            "nexus_async_fix_conn_{}_{}",
            std::process::id(),
            suffix
        ));
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

// ── B (primary): builder → (FixParts, transport) → raw three-object loop ─────

async fn connect_b(port: u16, dir: &Path) -> (FixParts<MockDict>, MaybeTls) {
    FixConnectionBuilder::<MockDict>::new()
        .disable_nagle()
        .connect(
            ("127.0.0.1", port),
            SessionState::new(Duration::from_secs(30)),
            config(),
            FixJournal::open(dir, 0, 256).unwrap(),
        )
        .await
        .unwrap()
}

/// One recv+reply over the raw parts. Destructures `FixParts` so `recv`'s `Message`
/// borrows `reader` only — the `TestReqID` rides back **zero-copy** (no copy-out).
async fn step_b(
    parts: &mut FixParts<MockDict>,
    conn: &mut MaybeTls,
) -> Result<Step, TransportError> {
    let FixParts {
        session,
        reader,
        writer,
    } = parts;
    match session.recv(reader, writer, conn, NOW).await? {
        Some(Message::LoggedOut { .. }) => Ok(Step::Ended),
        Some(Message::LogoutRequest { .. }) => {
            session.logout(writer, conn, NOW, None).await?;
            Ok(Step::Ended)
        }
        Some(Message::TestRequest { id }) => {
            session.heartbeat(writer, conn, NOW, Some(id)).await?; // zero-copy id
            Ok(Step::Continue)
        }
        Some(Message::GapDetected { begin }) => {
            session.resend_request(writer, conn, NOW, begin).await?;
            Ok(Step::Continue)
        }
        _ => Ok(Step::Continue),
    }
}

async fn drive_b(parts: &mut FixParts<MockDict>, conn: &mut MaybeTls) {
    loop {
        match step_b(parts, conn).await {
            Ok(Step::Ended) => return,
            Ok(Step::Continue) => {}
            Err(e) => panic!("raw-parts step errored before clean logout: {e:?}"),
        }
    }
}

#[tokio::test]
async fn builder_connect_roundtrip_logon_logout() {
    let dir = tmp_dir("b_logon_logout");
    let (mut child, port) = spawn_peer("logon_logout");
    let (mut parts, mut conn) = connect_b(port, dir.path()).await;
    parts
        .session
        .connect(&mut parts.writer, &mut conn, NOW)
        .await
        .unwrap(); // opening Logon
    drive_b(&mut parts, &mut conn).await;
    assert!(child.wait().unwrap().success());
}

#[tokio::test]
async fn builder_connect_roundtrip_heartbeat() {
    let dir = tmp_dir("b_heartbeat");
    let (mut child, port) = spawn_peer("heartbeat");
    let (mut parts, mut conn) = connect_b(port, dir.path()).await;
    parts
        .session
        .connect(&mut parts.writer, &mut conn, NOW)
        .await
        .unwrap();
    drive_b(&mut parts, &mut conn).await;
    assert!(child.wait().unwrap().success());
}

/// Reconnect under B: keep the `FixParts`, open a fresh transport with
/// `connect_socket`. A parked listener keeps the sockets alive; nothing is read.
#[tokio::test]
async fn reconnect_keeps_parts_new_socket() {
    let dir = tmp_dir("b_reconnect");
    let listener = tokio::net::TcpListener::bind(("127.0.0.1", 0))
        .await
        .unwrap();
    let addr = listener.local_addr().unwrap();
    let _srv = tokio::spawn(async move {
        loop {
            if listener.accept().await.is_err() {
                break;
            }
        }
    });

    let (mut parts, mut conn) = FixConnectionBuilder::<MockDict>::new()
        .disable_nagle()
        .connect(
            addr,
            SessionState::new(Duration::from_secs(30)),
            config(),
            FixJournal::open(dir.path(), 0, 256).unwrap(),
        )
        .await
        .unwrap();

    parts
        .session
        .connect(&mut parts.writer, &mut conn, NOW)
        .await
        .unwrap(); // Logon consumes seq 1
    let s1 = parts.session.allocate_seq().unwrap();
    parts
        .session
        .send_app(&mut parts.writer, &mut conn, s1, &new_order(s1))
        .await
        .unwrap(); // journal stores seq 2
    let next_out = parts.session.state().next_outbound_seq();
    assert_eq!(next_out, 3);

    // Reconnect: drop the old transport, open a new one — same parts.
    drop(conn);
    let mut conn2 = FixConnectionBuilder::<MockDict>::new()
        .disable_nagle()
        .connect_socket(addr)
        .await
        .unwrap();

    assert_eq!(
        parts.session.state().next_outbound_seq(),
        next_out,
        "outbound seqnum survives — it lives in the retained FixParts"
    );

    let s2 = parts.session.allocate_seq().unwrap();
    assert_eq!(
        s2, next_out,
        "allocate_seq continues from the preserved seqnum"
    );
    parts
        .session
        .send_app(&mut parts.writer, &mut conn2, s2, &new_order(s2))
        .await
        .unwrap();
    assert_eq!(parts.session.state().next_outbound_seq(), next_out + 1);
}

// ── A (secondary): FixConnection owns everything ─────────────────────────────

/// One recv+reply through the owns-everything bundle, demonstrating the documented
/// **copy-out**: the `TestReqID` is copied out of the borrowed `Message` before the
/// reply `.await`.
async fn step_a(conn: &mut FixConnection<MaybeTls, MockDict>) -> Result<Step, TransportError> {
    enum Act {
        None,
        Ended,
        Logout,
        Heartbeat(Vec<u8>),
        Resend(u32),
    }
    let act = match conn.recv(NOW).await? {
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
            conn.logout(NOW, None).await?;
            Ok(Step::Ended)
        }
        Act::Heartbeat(bytes) => {
            let id = AsciiTextStr::try_from_bytes(&bytes).unwrap();
            conn.heartbeat(NOW, Some(id)).await?;
            Ok(Step::Continue)
        }
        Act::Resend(begin) => {
            conn.resend_request(NOW, begin).await?;
            Ok(Step::Continue)
        }
    }
}

#[tokio::test]
async fn bundle_open_roundtrip_heartbeat() {
    let dir = tmp_dir("a_heartbeat");
    let (mut child, port) = spawn_peer("heartbeat");
    // One-step A construction.
    let mut conn = FixConnection::<MaybeTls, MockDict>::open(
        ("127.0.0.1", port),
        SessionState::new(Duration::from_secs(30)),
        config(),
        FixJournal::open(dir.path(), 0, 256).unwrap(),
    )
    .await
    .unwrap();
    conn.connect(NOW).await.unwrap(); // opening Logon
    loop {
        match step_a(&mut conn).await {
            Ok(Step::Ended) => break,
            Ok(Step::Continue) => {}
            Err(e) => panic!("bundle step errored before clean logout: {e:?}"),
        }
    }
    assert!(child.wait().unwrap().success());
}

/// A-side reconnect + state preservation across the `FixParts` ⇄ bundle boundary.
#[tokio::test]
async fn bundle_into_from_parts_preserves_state() {
    let dir = tmp_dir("a_reconnect");
    let listener = tokio::net::TcpListener::bind(("127.0.0.1", 0))
        .await
        .unwrap();
    let addr = listener.local_addr().unwrap();
    let _srv = tokio::spawn(async move {
        loop {
            if listener.accept().await.is_err() {
                break;
            }
        }
    });

    let mut conn = FixConnection::<MaybeTls, MockDict>::open(
        addr,
        SessionState::new(Duration::from_secs(45)),
        config(),
        FixJournal::open(dir.path(), 0, 256).unwrap(),
    )
    .await
    .unwrap();

    conn.connect(NOW).await.unwrap(); // Logon consumes outbound seq 1
    let s1 = conn.allocate_seq().unwrap();
    conn.send_app(s1, &new_order(s1)).await.unwrap(); // journal stores seq 2
    let next_out = conn.state().next_outbound_seq();
    let next_in = conn.state().next_inbound_seq();
    let hbi = conn.heartbeat_interval();
    assert_eq!(next_out, 3);
    assert_eq!(hbi, Duration::from_secs(45));

    // Unbundle to the raw parts, rebundle with a fresh transport — state survives.
    let (parts, _old) = conn.into_parts();
    let fresh = FixConnectionBuilder::<MockDict>::new()
        .connect_socket(addr)
        .await
        .unwrap();
    let mut conn2 = FixConnection::from_parts(parts, fresh);

    assert_eq!(conn2.state().next_outbound_seq(), next_out);
    assert_eq!(conn2.state().next_inbound_seq(), next_in);
    assert_eq!(conn2.heartbeat_interval(), hbi);

    let s2 = conn2.allocate_seq().unwrap();
    assert_eq!(s2, next_out, "the preserved journal keeps counting");
    conn2.send_app(s2, &new_order(s2)).await.unwrap();
    assert_eq!(conn2.state().next_outbound_seq(), next_out + 1);
}

// ── TLS: connect_tls hands back (FixParts, MaybeTls) end to end (feature-gated) ─

/// `connect_tls` performs the TCP connect, builds the rustls connector from a
/// `TlsConfig`, and drives the handshake — proving the `tokio-rustls` optional dep
/// is actually used. With nothing listening the TCP connect is refused, so it
/// surfaces `Err` rather than panicking; the point is that the whole TLS path
/// type-checks and runs and returns the raw `(FixParts, MaybeTls)`.
#[cfg(feature = "tls")]
#[tokio::test]
async fn connect_tls_wired_and_errors_when_refused() {
    use nexus_async_fix_engine::TlsConfig;

    let dir = tmp_dir("tls_refused");
    let cfg = TlsConfig::new().unwrap();
    let res = FixConnectionBuilder::<MockDict>::new()
        .connect_tls(
            "127.0.0.1:1", // nothing is listening — TCP connect is refused
            "example.com",
            &cfg,
            SessionState::new(Duration::from_secs(30)),
            config(),
            FixJournal::open(dir.path(), 0, 256).unwrap(),
        )
        .await;
    assert!(
        res.is_err(),
        "connect_tls to a closed port must error, not panic"
    );
}
