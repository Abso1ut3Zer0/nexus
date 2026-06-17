#![cfg(unix)]

//! Blocking session recipe: one initiator connects to one acceptor on localhost,
//! sends a NewOrder, then logs out.
//!
//! Run with: cargo run --example blocking_session

use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use nexus_fix_codec::{FrameFormatter, encode_fix_uint};
use nexus_fix_engine::{CompId, FixConnection, FixJournal, SessionConfig, SessionState, State};

const BEGIN: &[u8] = b"FIX.4.4";

fn main() {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();

    let acceptor_dir = tmp_dir("acceptor");
    let acceptor = std::thread::spawn(move || run_acceptor(&listener, &acceptor_dir));

    let initiator_dir = tmp_dir("initiator");
    run_initiator(addr, &initiator_dir);

    acceptor.join().unwrap();
}

fn run_acceptor(listener: &TcpListener, dir: &Path) {
    let (stream, _) = listener.accept().unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();

    let mut conn = FixConnection::builder().accept(
        stream,
        SessionState::new(Duration::from_secs(30)),
        SessionConfig {
            sender: CompId::new(b"ACCEPTOR").unwrap(),
            target: CompId::new(b"INITIATOR").unwrap(),
        },
        FixJournal::open(dir, 256).unwrap(),
        BEGIN,
    );

    let mut n = 0usize;
    loop {
        match conn.recv(Instant::now(), &mut |_: &[u8]| n += 1) {
            Ok(Some(reason)) => {
                println!("acceptor: {reason:?}, {n} app message(s) received");
                break;
            }
            Ok(None) => {}
            Err(e) => {
                eprintln!("acceptor error: {e}");
                break;
            }
        }
    }
}

fn run_initiator(addr: std::net::SocketAddr, dir: &Path) {
    let mut conn = FixConnection::builder()
        .connect(
            addr,
            SessionState::new(Duration::from_secs(30)),
            SessionConfig {
                sender: CompId::new(b"INITIATOR").unwrap(),
                target: CompId::new(b"ACCEPTOR").unwrap(),
            },
            FixJournal::open(dir, 256).unwrap(),
            BEGIN,
        )
        .unwrap();

    conn.connect(Instant::now()).unwrap();

    // recv until session is active
    loop {
        match conn.recv(Instant::now(), &mut |_| {}) {
            Ok(Some(r)) => {
                eprintln!("initiator: disconnected before active ({r:?})");
                return;
            }
            Err(e) => {
                eprintln!("initiator error: {e}");
                return;
            }
            Ok(None) if conn.state().state() == State::Active => break,
            Ok(None) => {}
        }
    }

    // send one NewOrder
    let seq = conn.allocate_seq();
    let msg = new_order(seq);
    conn.send_app(seq, &msg).unwrap();

    // logout
    conn.logout(Instant::now()).unwrap();
    loop {
        match conn.recv(Instant::now(), &mut |_| {}) {
            Ok(Some(_)) | Err(_) => break,
            Ok(None) => {}
        }
    }
}

fn new_order(seq: u32) -> Vec<u8> {
    let mut buf = [0u8; 512];
    let mut seq_buf = [0u8; 10];
    let n = encode_fix_uint(seq, &mut seq_buf);
    let mut fmt = FrameFormatter::new(&mut buf, BEGIN, b"D");
    fmt.field(34, &seq_buf[..n]);
    fmt.field(49, b"INITIATOR");
    fmt.field(56, b"ACCEPTOR");
    fmt.field(52, b"20260101-00:00:00.000");
    fmt.field(11, b"ORD-1");
    let (start, len) = fmt.finish().unwrap();
    buf[start..start + len].to_vec()
}

fn tmp_dir(name: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!("nexus_blocking_{name}"));
    std::fs::create_dir_all(&p).unwrap();
    p
}
