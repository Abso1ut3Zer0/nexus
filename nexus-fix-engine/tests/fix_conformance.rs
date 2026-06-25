#![cfg(unix)]

use std::io::BufRead;
use std::io::BufReader;
use std::net::TcpStream;
use std::path::PathBuf;
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

fn tmp_dir(suffix: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!("nexus_fix_conf_{}_{}", std::process::id(), suffix));
    std::fs::create_dir_all(&p).unwrap();
    p
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

fn connect(port: u16, dir: &PathBuf) -> FixConnection<TcpStream, MockDict> {
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
        FixJournal::open(dir, 256).unwrap(),
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
    let mut conn = connect(port, &dir);
    conn.connect(Instant::now()).unwrap();
    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_heartbeat() {
    let dir = tmp_dir("heartbeat");
    let (mut child, port) = spawn_peer("heartbeat");
    let mut conn = connect(port, &dir);
    conn.connect(Instant::now()).unwrap();
    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_resend() {
    let dir = tmp_dir("resend");
    let (mut child, port) = spawn_peer("resend");
    let mut conn = connect(port, &dir);
    conn.connect(Instant::now()).unwrap();

    loop {
        if let Some(Message::Disconnected { reason }) = conn.recv(Instant::now()).unwrap() {
            panic!("disconnected before active: {reason:?}");
        }
        if conn.state().state() == State::Active {
            break;
        }
    }

    let seq = conn.allocate_seq();
    conn.send_app(seq, &new_order(seq)).unwrap();

    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_gap_fill() {
    let dir = tmp_dir("gap_fill");
    let (mut child, port) = spawn_peer("gap_fill");
    let mut conn = connect(port, &dir);
    conn.connect(Instant::now()).unwrap();
    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}

#[test]
fn conformance_seq_reset() {
    let dir = tmp_dir("seq_reset");
    let (mut child, port) = spawn_peer("seq_reset");
    let mut conn = connect(port, &dir);
    conn.connect(Instant::now()).unwrap();
    assert_eq!(drive(&mut conn), DisconnectReason::Logout);
    assert!(child.wait().unwrap().success());
}
