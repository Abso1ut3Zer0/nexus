#![cfg(unix)]

//! Blocking session recipe: one initiator connects to one acceptor on localhost,
//! sends a NewOrder, then logs out.
//!
//! Run with: cargo run --example blocking_session

use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use nexus_fix_codec::{
    FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{
    CompId, FixConnection, FixJournal, Message, SessionConfig, SessionError, SessionState, State,
};

// ── minimal FIX 4.4 dictionary ───────────────────────────────────────────────

struct Fix44;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Fix44MsgType {}

struct Decoder<'buf> {
    _buf: &'buf [u8],
}

impl<'buf> FixAdminMsg<'buf> for Decoder<'buf> {
    fn decode(buf: &'buf [u8]) -> Result<Self, nexus_fix_codec::DecodeError> {
        Ok(Self { _buf: buf })
    }
}

impl FixDictionary for Fix44 {
    type MsgType = Fix44MsgType;
    type Header<'buf> = Fix44Header<'buf>;
    type Logon<'buf> = Decoder<'buf>;
    type Logout<'buf> = Decoder<'buf>;
    type Heartbeat<'buf> = Decoder<'buf>;
    type TestRequest<'buf> = Decoder<'buf>;
    type ResendRequest<'buf> = Decoder<'buf>;
    type SequenceReset<'buf> = Decoder<'buf>;
    type Reject<'buf> = Decoder<'buf>;
    const BEGIN_STRING: &'static [u8] = b"FIX.4.4";
    fn is_admin(_: Fix44MsgType) -> bool {
        false
    }
}

struct Fix44Header<'buf> {
    buf: &'buf [u8],
}

impl<'buf> FixHeader<'buf> for Fix44Header<'buf> {
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

// ── main ─────────────────────────────────────────────────────────────────────

fn main() {
    let port: u16 = std::env::var("FIX_PORT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0);
    let listener = TcpListener::bind(("127.0.0.1", port)).unwrap();
    let addr = listener.local_addr().unwrap();
    println!("listening on {addr}");

    if port != 0 {
        let mut n = 0u64;
        loop {
            let dir = tmp_dir(&format!("acceptor_{n}"));
            n += 1;
            run_acceptor(&listener, &dir);
        }
    } else {
        let acceptor_dir = tmp_dir("acceptor");
        let acceptor = std::thread::spawn(move || run_acceptor(&listener, &acceptor_dir));
        let initiator_dir = tmp_dir("initiator");
        run_initiator(addr, &initiator_dir);
        acceptor.join().unwrap();
    }
}

fn run_acceptor(listener: &TcpListener, dir: &Path) {
    let (stream, _) = listener.accept().unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();

    let mut conn: FixConnection<_, Fix44> = FixConnection::builder().accept(
        stream,
        SessionState::new(Duration::from_secs(30)),
        SessionConfig {
            sender: CompId::new(b"ACCEPTOR").unwrap(),
            target: CompId::new(b"INITIATOR").unwrap(),
        },
        FixJournal::open(dir, 256).unwrap(),
    );

    let mut n = 0usize;
    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { reason })) => {
                println!("acceptor: {reason:?}, {n} app message(s) received");
                break;
            }
            Ok(Some(Message::Application { .. })) => n += 1,
            Ok(Some(_) | None) => {}
            Err(e) => {
                eprintln!("acceptor error: {e}");
                break;
            }
        }
    }
}

fn run_initiator(addr: std::net::SocketAddr, dir: &Path) {
    let mut conn: FixConnection<_, Fix44> = FixConnection::builder()
        .connect(
            addr,
            SessionState::new(Duration::from_secs(30)),
            SessionConfig {
                sender: CompId::new(b"INITIATOR").unwrap(),
                target: CompId::new(b"ACCEPTOR").unwrap(),
            },
            FixJournal::open(dir, 256).unwrap(),
        )
        .unwrap();

    conn.connect(Instant::now()).unwrap();

    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { reason })) => {
                eprintln!("initiator: disconnected before active ({reason:?})");
                return;
            }
            Err(e) => {
                eprintln!("initiator error: {e}");
                return;
            }
            Ok(Some(_) | None) => {}
        }
        if conn.state().state() == State::Active {
            break;
        }
    }

    let seq = match conn.allocate_seq() {
        Ok(s) => s,
        Err(SessionError::SeqNumExhausted) => {
            eprintln!("initiator: sequence number exhausted; force a sequence reset");
            return;
        }
        Err(e) => {
            eprintln!("initiator: allocate_seq error: {e}");
            return;
        }
    };
    let msg = new_order(seq);
    conn.send_app(seq, &msg).unwrap();

    conn.logout(Instant::now()).unwrap();
    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(_)) | Err(_) => break,
            Ok(None) => {}
        }
    }
}

fn new_order(seq: u32) -> Vec<u8> {
    let mut buf = [0u8; 512];
    let mut seq_buf = [0u8; 10];
    let n = encode_fix_uint(seq, &mut seq_buf);
    let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
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
