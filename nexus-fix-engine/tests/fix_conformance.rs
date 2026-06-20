#![cfg(unix)]

use std::io::{BufRead, BufReader};
use std::net::TcpStream;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use nexus_fix_codec::{FrameFormatter, encode_fix_uint};
use nexus_fix_engine::{
    CompId, DisconnectReason, FixConnection, FixJournal, SessionConfig, SessionState, State,
};

const BEGIN: &[u8] = b"FIX.4.4";
const PEER: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/fix_peer.py");

fn tmp_dir(suffix: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!("nexus_fix_conf_{}_{}", std::process::id(), suffix));
    std::fs::create_dir_all(&p).unwrap();
    p
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

fn connect(port: u16, dir: &PathBuf) -> FixConnection<TcpStream> {
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
        BEGIN,
    )
}

fn drive(conn: &mut FixConnection<TcpStream>) -> DisconnectReason {
    loop {
        if let Some(r) = conn.recv(Instant::now(), &mut |_| {}).unwrap() {
            return r;
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
        match conn.recv(Instant::now(), &mut |_| {}).unwrap() {
            Some(r) => panic!("disconnected before active: {r:?}"),
            None if conn.state().state() == State::Active => break,
            None => {}
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
