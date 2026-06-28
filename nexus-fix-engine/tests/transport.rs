#![cfg(unix)]

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use nexus_fix_codec::{
    FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{
    CompId, DisconnectReason, FixConnection, FixJournal, Message, SessionConfig, SessionError,
    SessionState, State, TransportError,
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

fn sender() -> CompId {
    CompId::new(b"INITIATOR").unwrap()
}
fn target() -> CompId {
    CompId::new(b"ACCEPTOR").unwrap()
}

fn session_cfg(sender: CompId, target: CompId) -> SessionConfig {
    SessionConfig { sender, target }
}

fn journal(dir: &PathBuf) -> FixJournal {
    FixJournal::open(dir, 256).unwrap()
}

fn loopback_pair() -> (TcpStream, TcpStream) {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    let client = TcpStream::connect(addr).unwrap();
    let (server, _) = listener.accept().unwrap();
    (client, server)
}

fn tmp_dir(suffix: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!(
        "nexus_fix_transport_{}_{}",
        std::process::id(),
        suffix
    ));
    std::fs::create_dir_all(&p).unwrap();
    p
}

fn drive(
    conn: &mut FixConnection<TcpStream, MockDict>,
) -> Result<DisconnectReason, TransportError> {
    loop {
        if let Some(Message::Disconnected { reason }) = conn.recv(Instant::now())? {
            return Ok(reason);
        }
    }
}

struct Peer {
    stream: TcpStream,
    sender: CompId,
    target: CompId,
    next_out: u32,
}

impl Peer {
    fn new(stream: TcpStream, sender: CompId, target: CompId) -> Self {
        stream
            .set_read_timeout(Some(Duration::from_secs(5)))
            .unwrap();
        Self {
            stream,
            sender,
            target,
            next_out: 1,
        }
    }

    fn send_logon(&mut self, hbi: u32) {
        let seq = self.next_out;
        self.next_out += 1;
        let mut buf = [0u8; 512];
        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(seq, &mut seq_buf);
        let mut hbi_buf = [0u8; 10];
        let hbi_n = encode_fix_uint(hbi, &mut hbi_buf);
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, self.sender.as_bytes());
        fmt.field(56, self.target.as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(108, &hbi_buf[..hbi_n]);
        let (start, len) = fmt.finish().unwrap();
        self.stream.write_all(&buf[start..start + len]).unwrap();
        self.stream.flush().unwrap();
    }

    fn send_logout(&mut self) {
        let seq = self.next_out;
        self.next_out += 1;
        let mut buf = [0u8; 256];
        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(seq, &mut seq_buf);
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"5");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, self.sender.as_bytes());
        fmt.field(56, self.target.as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        let (start, len) = fmt.finish().unwrap();
        self.stream.write_all(&buf[start..start + len]).unwrap();
        self.stream.flush().unwrap();
    }

    fn send_app(&mut self, extra_tag: u32, extra_val: &[u8]) {
        let seq = self.next_out;
        self.next_out += 1;
        let mut buf = [0u8; 512];
        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(seq, &mut seq_buf);
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, self.sender.as_bytes());
        fmt.field(56, self.target.as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(extra_tag, extra_val);
        let (start, len) = fmt.finish().unwrap();
        self.stream.write_all(&buf[start..start + len]).unwrap();
        self.stream.flush().unwrap();
    }

    fn recv_msg(&mut self, buf: &mut [u8]) -> usize {
        self.stream.read(buf).unwrap()
    }

    fn send_resend_request(&mut self, begin: u32, end: u32) {
        let seq = self.next_out;
        self.next_out += 1;
        let mut buf = [0u8; 256];
        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(seq, &mut seq_buf);
        let mut begin_buf = [0u8; 10];
        let begin_n = encode_fix_uint(begin, &mut begin_buf);
        let mut end_buf = [0u8; 10];
        let end_n = encode_fix_uint(end, &mut end_buf);
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"2");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, self.sender.as_bytes());
        fmt.field(56, self.target.as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(7, &begin_buf[..begin_n]);
        fmt.field(16, &end_buf[..end_n]);
        let (start, len) = fmt.finish().unwrap();
        self.stream.write_all(&buf[start..start + len]).unwrap();
        self.stream.flush().unwrap();
    }

    fn send_sequence_reset_reset(&mut self, new_seq: u32) {
        let seq = self.next_out;
        self.next_out += 1;
        let mut buf = [0u8; 256];
        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(seq, &mut seq_buf);
        let mut nsq_buf = [0u8; 10];
        let nsq_n = encode_fix_uint(new_seq, &mut nsq_buf);
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"4");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, self.sender.as_bytes());
        fmt.field(56, self.target.as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(36, &nsq_buf[..nsq_n]);
        // No GapFillFlag(123) → Reset mode
        let (start, len) = fmt.finish().unwrap();
        self.stream.write_all(&buf[start..start + len]).unwrap();
        self.stream.flush().unwrap();
    }

    fn send_corrupt_heartbeat(&mut self) {
        let seq = self.next_out;
        self.next_out += 1;
        let mut buf = [0u8; 256];
        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(seq, &mut seq_buf);
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"0");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, self.sender.as_bytes());
        fmt.field(56, self.target.as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        let (start, len) = fmt.finish().unwrap();
        buf[start + len - 2] ^= 1; // corrupt last checksum digit
        self.stream.write_all(&buf[start..start + len]).unwrap();
        self.stream.flush().unwrap();
    }
}

// ── tests ────────────────────────────────────────────────────────────────────

#[test]
fn initiator_logon_and_logout() {
    let dir = tmp_dir("logon_logout");
    let (client_sock, server_sock) = loopback_pair();
    client_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    let t_sender = sender();
    let t_target = target();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(server_sock, target(), sender());
        let mut buf = [0u8; 512];
        let n = peer.recv_msg(&mut buf);
        assert!(n > 0);
        peer.send_logon(30);
        peer.send_logout();
        let _ = peer.recv_msg(&mut buf);
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        client_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(t_sender, t_target),
        journal(&dir),
    );
    conn.connect(Instant::now()).unwrap();

    let reason = drive(&mut conn).unwrap();
    assert_eq!(reason, DisconnectReason::Logout);

    handle.join().unwrap();
}

#[test]
fn acceptor_receives_app_message() {
    let dir = tmp_dir("acceptor_app");
    let (client_sock, server_sock) = loopback_pair();
    server_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(client_sock, sender(), target());
        peer.send_logon(30);
        let mut buf = [0u8; 512];
        let _ = peer.recv_msg(&mut buf);
        peer.send_app(11, b"ORD-1");
        peer.send_logout();
        let _ = peer.recv_msg(&mut buf);
    });

    let mut received_app = 0usize;
    let dir2 = tmp_dir("acceptor_app_srv");
    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(&dir2),
    );

    let reason = loop {
        match conn.recv(Instant::now()).unwrap() {
            Some(Message::Disconnected { reason }) => break reason,
            Some(Message::Application { header: _ }) => {
                received_app += 1;
            }
            Some(_) | None => {}
        }
    };

    assert_eq!(reason, DisconnectReason::Logout);
    assert_eq!(received_app, 1);

    handle.join().unwrap();
    let _ = dir;
}

#[test]
fn resend_request_triggers_gap_fill() {
    let dir_srv = tmp_dir("resend_srv");
    let dir_cli = tmp_dir("resend_cli");
    let (client_sock, server_sock) = loopback_pair();
    client_sock
        .set_read_timeout(Some(Duration::from_millis(500)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(server_sock, target(), sender());
        let mut buf = [0u8; 4096];

        let _ = peer.recv_msg(&mut buf);
        peer.send_logon(30);

        let mut rbuf = [0u8; 256];
        let mut fmt = FrameFormatter::new(&mut rbuf, b"FIX.4.4", b"2");
        fmt.field(34, b"2");
        fmt.field(49, b"ACCEPTOR");
        fmt.field(56, b"INITIATOR");
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(7, b"1");
        fmt.field(16, b"1");
        let (start, len) = fmt.finish().unwrap();
        peer.stream.write_all(&rbuf[start..start + len]).unwrap();
        peer.stream.flush().unwrap();
        peer.next_out = 3;

        let n = peer.recv_msg(&mut buf);
        assert!(n > 0);

        peer.send_logout();
        let _ = peer.recv_msg(&mut buf);
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        client_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(sender(), target()),
        journal(&dir_cli),
    );
    conn.connect(Instant::now()).unwrap();

    let reason = drive(&mut conn).unwrap();
    assert_eq!(reason, DisconnectReason::Logout);

    handle.join().unwrap();
    let _ = dir_srv;
}

#[test]
fn inbound_gap_sends_resend_request_and_suppresses_app_message() {
    let dir_cli = tmp_dir("inbound_gap");
    let (client_sock, server_sock) = loopback_pair();
    server_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    // Peer sends logon, then a gap app message, then drops (EOF to engine).
    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(client_sock, sender(), target());
        let mut buf = [0u8; 512];
        peer.send_logon(30);
        let _ = peer.recv_msg(&mut buf); // consume logon ack
        peer.next_out = 5;
        peer.send_app(11, b"ORD-GAP"); // seq=5, gap (expected 2)
        // Drop peer — engine sees EOF; no need to read ResendRequest here.
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(&dir_cli),
    );

    let mut saw_app = false;
    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { .. })) | Err(_) => break,
            Ok(Some(Message::Application { .. })) => saw_app = true,
            Ok(Some(_) | None) => {}
        }
    }

    assert!(!saw_app, "out-of-sequence app must not be surfaced");
    assert_eq!(
        conn.state().state(),
        State::Resending,
        "engine must enter Resending state (= ResendRequest sent) on inbound gap"
    );

    handle.join().unwrap();
}

#[test]
fn resend_request_huge_end_seq_clamped() {
    // Fix 1: peer sends EndSeqNo=4_000_000_000; engine must clamp to next_outbound-1
    // and respond immediately (not iterate 4B times).
    let dir = tmp_dir("resend_huge");
    let (client_sock, server_sock) = loopback_pair();
    client_sock
        .set_read_timeout(Some(Duration::from_millis(500)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(server_sock, target(), sender());
        let mut buf = [0u8; 4096];
        let _ = peer.recv_msg(&mut buf); // initiator logon
        peer.send_logon(30);
        peer.send_resend_request(1, 4_000_000_000); // seq=2, begin=1, end=4B
        let n = peer.recv_msg(&mut buf); // must receive GapFill quickly
        assert!(n > 0, "engine must respond to clamped ResendRequest");
        let new_seq: u32 = find_tag(&buf[..n], 0, 36)
            .and_then(|s| FieldView::new(s, &buf[..n]))
            .expect("GapFill must contain NewSeqNo(36)")
            .get();
        assert_eq!(new_seq, 2u32, "GapFill new_seq must equal next_outbound");
        peer.send_logout();
        let _ = peer.recv_msg(&mut buf);
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        client_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(sender(), target()),
        journal(&dir),
    );
    conn.connect(Instant::now()).unwrap();
    let reason = drive(&mut conn).unwrap();
    assert_eq!(reason, DisconnectReason::Logout);
    handle.join().unwrap();
}

#[test]
fn corrupt_checksum_frame_counted_as_garbage() {
    // Fix 2: a frame with a bad checksum must be detected at the frame boundary
    // and counted in garbage_frame_count.
    let dir = tmp_dir("corrupt_cs");
    let (client_sock, server_sock) = loopback_pair();
    server_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(client_sock, sender(), target());
        let mut buf = [0u8; 512];
        peer.send_logon(30);
        let _ = peer.recv_msg(&mut buf);
        peer.send_corrupt_heartbeat();
        // Drop peer
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(&dir),
    );

    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { .. })) | Err(_) => break,
            _ => {}
        }
    }

    assert!(
        conn.garbage_frame_count() > 0,
        "corrupt checksum must increment garbage_frame_count"
    );
    handle.join().unwrap();
}

#[test]
fn garbage_bytes_increment_counter() {
    // Fix 3: raw non-FIX bytes from a misbehaving peer must be counted.
    let dir = tmp_dir("garbage_count");
    let (client_sock, server_sock) = loopback_pair();
    server_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(client_sock, sender(), target());
        let mut buf = [0u8; 512];
        peer.send_logon(30);
        let _ = peer.recv_msg(&mut buf);
        peer.stream.write_all(b"GARBAGE_NOT_FIX").unwrap();
        peer.stream.flush().unwrap();
        // Drop peer
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(&dir),
    );

    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { .. })) | Err(_) => break,
            _ => {}
        }
    }

    assert!(
        conn.garbage_frame_count() > 0,
        "raw garbage bytes must increment garbage_frame_count"
    );
    handle.join().unwrap();
}

#[test]
fn sequence_reset_backward_ignored() {
    // Fix 4: SequenceReset Reset-mode with new_seq < next_inbound must be ignored.
    let dir = tmp_dir("seqreset_bwd");
    let (client_sock, server_sock) = loopback_pair();
    server_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(client_sock, sender(), target());
        let mut buf = [0u8; 512];
        peer.send_logon(30); // seq=1; server next_inbound becomes 2
        let _ = peer.recv_msg(&mut buf);
        peer.send_sequence_reset_reset(1); // new_seq=1 < next_inbound=2 → ignored
        peer.send_sequence_reset_reset(0); // new_seq=0 → ignored
        // Drop peer
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(&dir),
    );

    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { .. })) | Err(_) => break,
            _ => {}
        }
    }

    assert_eq!(
        conn.state().next_inbound_seq(),
        2,
        "backward/zero SequenceReset Reset must not rewind next_inbound"
    );
    handle.join().unwrap();
}

#[test]
fn overflowed_tag_34_yields_missing_seq_num() {
    let dir = tmp_dir("overflow_tag34");
    let (client_sock, server_sock) = loopback_pair();
    server_sock
        .set_read_timeout(Some(Duration::from_millis(500)))
        .unwrap();

    // Build a raw FIX frame where tag 34 is written with an overflowing digit
    // sequence (9999999999 > u32::MAX). parse_tag returns u32::MAX, so find_tag(34)
    // returns None → MissingMsgSeqNum.
    let body: &[u8] = b"35=A\x019999999999=1\x0149=ACCEPTOR\x0156=INITIATOR\x0152=20260615-12:00:00.000\x01108=30\x01";
    let header = format!("8=FIX.4.4\x019={}\x01", body.len());
    let precheck: u8 = header
        .bytes()
        .chain(body.iter().copied())
        .fold(0u32, |a, b| a.wrapping_add(b as u32)) as u8;
    let frame = {
        let mut v = header.into_bytes();
        v.extend_from_slice(body);
        v.extend_from_slice(format!("10={precheck:03}\x01").as_bytes());
        v
    };

    let handle = std::thread::spawn(move || {
        let mut s = client_sock;
        s.write_all(&frame).unwrap();
        s.flush().unwrap();
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(&dir),
    );

    let result = conn.recv(Instant::now());
    handle.join().unwrap();

    assert!(
        matches!(
            result,
            Err(TransportError::Protocol(SessionError::MissingMsgSeqNum))
        ),
        "expected MissingMsgSeqNum"
    );
}

#[test]
fn journal_recovers_admin_seqnums() {
    let dir = tmp_dir("journal_admin_seqnums");
    let (client_sock, server_sock) = loopback_pair();
    client_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(server_sock, target(), sender());
        let mut buf = [0u8; 512];
        let _ = peer.recv_msg(&mut buf);
        peer.send_logon(30);
        peer.send_logout();
        let _ = peer.recv_msg(&mut buf);
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        client_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(sender(), target()),
        journal(&dir),
    );
    conn.connect(Instant::now()).unwrap();
    let reason = drive(&mut conn).unwrap();
    assert_eq!(reason, DisconnectReason::Logout);
    handle.join().unwrap();
    drop(conn);

    // seq=1 logon + seq=2 logout-ack → next_outbound must be 3 after recovery
    let recovered = FixJournal::open(&dir, 256).unwrap();
    assert_eq!(
        recovered.next_outbound(),
        3,
        "journal must include admin seqnums"
    );
}
