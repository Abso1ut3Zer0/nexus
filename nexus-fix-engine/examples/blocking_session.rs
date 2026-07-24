#![cfg(unix)]

//! Blocking session recipe: one initiator connects to one acceptor on localhost,
//! sends a NewOrder, then logs out.
//!
//! Run with: cargo run --example blocking_session

use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::time::Duration;

use nexus_fix_codec::{
    FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{
    CompId, FixJournal, FixParts, FixSession, Message, SessionConfig, SessionError, SessionState,
    State,
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

/// Fixed UTC-unix-nanos clock. A production caller reads a real wall clock here
/// (`SystemTime::now().duration_since(UNIX_EPOCH)`, or a venue-supplied time);
/// the fixed value keeps this example deterministic. `now` stamps only
/// `SendingTime(52)` — the session reads no clock of its own.
const NOW: i128 = 1_780_505_733_000_000_000;

// ── main ─────────────────────────────────────────────────────────────────────

fn main() {
    let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
    let addr = listener.local_addr().unwrap();
    println!("listening on {addr}");

    let acceptor_dir = tmp_dir("acceptor");
    let acceptor = std::thread::spawn(move || run_acceptor(&listener, &acceptor_dir));
    let initiator_dir = tmp_dir("initiator");
    run_initiator(addr, &initiator_dir);
    acceptor.join().unwrap();
}

fn run_acceptor(listener: &TcpListener, dir: &Path) {
    let (mut stream, _) = listener.accept().unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();

    // The caller holds the trio; the socket is separate and passed per call.
    let FixParts {
        mut session,
        mut reader,
        mut writer,
    } = FixSession::<Fix44>::builder().build(
        SessionState::new(Duration::from_secs(30)),
        SessionConfig {
            sender: CompId::new(b"ACCEPTOR").unwrap(),
            target: CompId::new(b"INITIATOR").unwrap(),
        },
        FixJournal::open(dir, 0, 256).unwrap(),
    );

    // The user-driven loop: the engine surfaces each situation and its one
    // required response; the caller sends it. `recv` ties its `Message` to
    // `reader` only, so the reply's `&mut session` / `&mut writer` / `&mut stream`
    // stay free while a borrowed payload (a `TestReqID`, a `LogonDecision`) is
    // still alive.
    let mut n = 0usize;
    loop {
        match session.recv(&mut reader, &mut writer, &mut stream, NOW) {
            // The initiator's Logon: authenticate (inspect `d.logon()`) then accept.
            Ok(Some(Message::LogonRequest(d) | Message::LogonResetRequest(d))) => {
                d.accept(&mut session, &mut writer, &mut stream, NOW)
                    .unwrap();
            }
            // Peer liveness probe: echo the TestReqID in a Heartbeat.
            Ok(Some(Message::TestRequest { id })) => {
                session
                    .heartbeat(&mut writer, &mut stream, NOW, Some(id))
                    .unwrap();
            }
            // Inbound gap: ask for the missing range.
            Ok(Some(Message::GapDetected { begin })) => {
                session
                    .resend_request(&mut writer, &mut stream, NOW, begin)
                    .unwrap();
            }
            Ok(Some(Message::Application { .. })) => n += 1,
            // Peer initiated a logout: reply and finish.
            Ok(Some(Message::LogoutRequest { .. })) => {
                let _ = session.logout(&mut writer, &mut stream, NOW);
                println!("acceptor: peer logged out, {n} app message(s) received");
                break;
            }
            Ok(Some(Message::LoggedOut { .. })) => {
                println!("acceptor: logged out cleanly, {n} app message(s) received");
                break;
            }
            Ok(Some(_) | None) => {}
            Err(e) => {
                eprintln!("acceptor error: {e}");
                break;
            }
        }
    }
}

fn run_initiator(addr: std::net::SocketAddr, dir: &Path) {
    // The caller opens the socket; reconnect is "same trio, new socket."
    let mut stream = TcpStream::connect(addr).unwrap();
    stream.set_nodelay(true).unwrap();

    let FixParts {
        mut session,
        mut reader,
        mut writer,
    } = FixSession::<Fix44>::builder().build(
        SessionState::new(Duration::from_secs(30)),
        SessionConfig {
            sender: CompId::new(b"INITIATOR").unwrap(),
            target: CompId::new(b"ACCEPTOR").unwrap(),
        },
        FixJournal::open(dir, 0, 256).unwrap(),
    );

    // Combined verb: encode the opening Logon and flush it to the socket in one
    // call. (The encode-only `encode_connect` + a manual drain of `writer` is the
    // sans-IO alternative for custom transports.)
    session.connect(&mut writer, &mut stream, NOW).unwrap();

    loop {
        match session.recv(&mut reader, &mut writer, &mut stream, NOW) {
            Ok(Some(Message::TestRequest { id })) => {
                session
                    .heartbeat(&mut writer, &mut stream, NOW, Some(id))
                    .unwrap();
            }
            Ok(Some(Message::GapDetected { begin })) => {
                session
                    .resend_request(&mut writer, &mut stream, NOW, begin)
                    .unwrap();
            }
            Ok(Some(Message::LoggedOut { .. } | Message::LogoutRequest { .. })) => {
                eprintln!("initiator: logged out before active");
                return;
            }
            Err(e) => {
                eprintln!("initiator error: {e}");
                return;
            }
            Ok(Some(_) | None) => {}
        }
        if session.state().state() == State::Active {
            break;
        }
    }

    let seq = match session.allocate_seq() {
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
    session
        .send_app(&mut writer, &mut stream, seq, &msg)
        .unwrap();

    // We initiate the logout; the acceptor's confirming Logout ends the session
    // cleanly (surfaces as `LoggedOut`).
    session.logout(&mut writer, &mut stream, NOW).unwrap();
    loop {
        match session.recv(&mut reader, &mut writer, &mut stream, NOW) {
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
