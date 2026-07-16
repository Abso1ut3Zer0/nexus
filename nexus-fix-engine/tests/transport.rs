#![cfg(unix)]

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
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

fn journal(dir: &Path) -> FixJournal {
    FixJournal::open(dir, 0, 256).unwrap()
}

fn loopback_pair() -> (TcpStream, TcpStream) {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    let client = TcpStream::connect(addr).unwrap();
    let (server, _) = listener.accept().unwrap();
    (client, server)
}

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
            "nexus_fix_transport_{}_{}",
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

    /// Send a Heartbeat (35=0) with an explicit `MsgSeqNum` (not the auto-counter),
    /// so a test can drive a stale/too-low or forward-gap seqnum.
    fn send_heartbeat_seq(&mut self, seq: u32) {
        let mut buf = [0u8; 256];
        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(seq, &mut seq_buf);
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"0");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, self.sender.as_bytes());
        fmt.field(56, self.target.as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        let (start, len) = fmt.finish().unwrap();
        self.stream.write_all(&buf[start..start + len]).unwrap();
        self.stream.flush().unwrap();
    }

    /// Send a Heartbeat (35=0) with an explicit `MsgSeqNum` and `PossDupFlag=Y`,
    /// so a test can drive a below-expected duplicate (which must be ignored,
    /// not disconnect).
    fn send_heartbeat_poss_dup(&mut self, seq: u32) {
        let mut buf = [0u8; 256];
        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(seq, &mut seq_buf);
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"0");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, self.sender.as_bytes());
        fmt.field(56, self.target.as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(43, b"Y");
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
        journal(dir.path()),
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
        journal(dir2.path()),
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
fn heartbeat_stale_seqnum_disconnects() {
    // Regression for #588: a too-low MsgSeqNum in a Heartbeat must surface as a
    // SeqNumTooLow disconnect — not be swallowed and returned as a normal
    // Heartbeat while the session silently dies.
    let dir = tmp_dir("hb_stale_seq");
    let (client_sock, server_sock) = loopback_pair();
    server_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(client_sock, sender(), target());
        peer.send_logon(30);
        let mut buf = [0u8; 512];
        let _ = peer.recv_msg(&mut buf); // engine's Logon reply
        // Engine now expects inbound seq 2; a Heartbeat at seq 1 is too-low.
        peer.send_heartbeat_seq(1);
        let _ = peer.recv_msg(&mut buf); // drain the engine's Logout
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(dir.path()),
    );

    let reason = loop {
        if let Some(Message::Disconnected { reason }) = conn.recv(Instant::now()).unwrap() {
            break reason;
        }
    };
    assert_eq!(reason, DisconnectReason::SeqNumTooLow);

    handle.join().unwrap();
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
        journal(dir_cli.path()),
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
        journal(dir_cli.path()),
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
fn out_of_sequence_admin_suppressed_and_resends() {
    // An out-of-sequence admin (Heartbeat at a forward-gap seqnum) must NOT be
    // surfaced to the application: it is a recovery event. The engine emits a
    // ResendRequest and yields no admin message (Suppressed → Ok(None)). This is
    // the admin analogue of `inbound_gap_sends_resend_request_and_suppresses_app_message`.
    let dir = tmp_dir("oos_admin_suppress");
    let (client_sock, server_sock) = loopback_pair();
    server_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(client_sock, sender(), target());
        let mut buf = [0u8; 512];
        peer.send_logon(30); // seq 1 → engine Active, expects inbound seq 2
        let _ = peer.recv_msg(&mut buf); // consume the engine's Logon reply
        // Heartbeat at seq 5 (expected 2): a forward gap, not a duplicate.
        peer.send_heartbeat_seq(5);
        // The engine must answer the gap with a ResendRequest (35=2). Read it off
        // the wire and assert on it directly, so the resend is observed at the
        // transport boundary, not just via engine state.
        let n = peer.recv_msg(&mut buf);
        assert!(n > 0, "engine must send a ResendRequest on the admin gap");
        let msg_type = find_tag(&buf[..n], 0, 35).map(|s| s.slice(&buf[..n]));
        assert_eq!(
            msg_type,
            Some(b"2".as_ref()),
            "engine must respond to an out-of-sequence admin with a ResendRequest (35=2)"
        );
        let begin: u32 = find_tag(&buf[..n], 0, 7)
            .and_then(|s| FieldView::new(s, &buf[..n]))
            .expect("ResendRequest must carry BeginSeqNo(7)")
            .get();
        assert_eq!(begin, 2, "ResendRequest must start at the expected seqnum");
        // Drop peer → engine sees EOF and disconnects, ending the recv loop.
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(dir.path()),
    );

    let mut saw_admin = false;
    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { .. })) | Err(_) => break,
            // The out-of-sequence Heartbeat must never surface.
            Ok(Some(Message::Heartbeat { .. })) => saw_admin = true,
            Ok(Some(_) | None) => {}
        }
    }

    assert!(
        !saw_admin,
        "out-of-sequence admin (Heartbeat) must not be surfaced to the application"
    );
    assert_eq!(
        conn.state().state(),
        State::Resending,
        "engine must enter Resending (= ResendRequest sent) on an out-of-sequence admin"
    );

    handle.join().unwrap();
}

#[test]
fn duplicate_admin_suppressed_no_resend() {
    // A PossDup duplicate admin below the expected seqnum must be ignored: not
    // surfaced, no ResendRequest, and the session stays alive. This pins the
    // duplicate (vs. gap) branch at the transport boundary.
    let dir = tmp_dir("dup_admin_suppress");
    let (client_sock, server_sock) = loopback_pair();
    server_sock
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();

    let handle = std::thread::spawn(move || {
        let mut peer = Peer::new(client_sock, sender(), target());
        let mut buf = [0u8; 512];
        peer.send_logon(30); // seq 1 → engine Active, expects inbound seq 2
        let _ = peer.recv_msg(&mut buf); // consume the engine's Logon reply
        peer.send_app(11, b"ORD-1"); // seq 2, in-sequence → engine expects 3 next
        // Duplicate Heartbeat at seq 2 (< 3) WITH PossDup=Y: ignored silently.
        peer.send_heartbeat_poss_dup(2);
        // Drop peer → engine sees EOF and disconnects.
    });

    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(dir.path()),
    );

    let mut saw_dup_admin = false;
    let mut saw_app = false;
    loop {
        match conn.recv(Instant::now()) {
            Ok(Some(Message::Disconnected { .. })) | Err(_) => break,
            Ok(Some(Message::Application { .. })) => saw_app = true,
            Ok(Some(Message::Heartbeat { .. })) => saw_dup_admin = true,
            Ok(Some(_) | None) => {}
        }
    }

    assert!(saw_app, "the in-sequence app (seq 2) must surface");
    assert!(
        !saw_dup_admin,
        "a PossDup duplicate admin must not be surfaced"
    );
    assert_eq!(
        conn.state().state(),
        State::Active,
        "a duplicate admin must not enter Resending or disconnect the session"
    );
    // The engine consumed exactly the in-sequence app (next_inbound advanced to 3
    // and stayed there — the duplicate did not advance it).
    assert_eq!(
        conn.state().next_inbound_seq(),
        3,
        "duplicate admin must not advance next_inbound"
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
        journal(dir.path()),
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
        journal(dir.path()),
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
        journal(dir.path()),
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
        journal(dir.path()),
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
        journal(dir.path()),
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
        journal(dir.path()),
    );
    conn.connect(Instant::now()).unwrap();
    let reason = drive(&mut conn).unwrap();
    assert_eq!(reason, DisconnectReason::Logout);
    handle.join().unwrap();
    drop(conn);

    // seq=1 logon + seq=2 logout-ack → next_outbound must be 3 after recovery
    let recovered = FixJournal::open(dir.path(), 0, 256).unwrap();
    assert_eq!(
        recovered.next_outbound(),
        3,
        "journal must include admin seqnums"
    );
}

#[test]
fn send_app_rejects_oversized_frame() {
    // A frame larger than the writer capacity minus reframe headroom is a
    // configuration error — the caller sizes the writer up front — not a
    // runtime fallback. The cap fires before any journal or socket write.
    let dir = tmp_dir("oversized");
    let (client_sock, _server_sock) = loopback_pair();
    let mut conn: FixConnection<TcpStream, MockDict> = FixConnection::from_parts(
        client_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(sender(), target()),
        journal(dir.path()),
    );

    // The default writer is 64 KiB; a 64 KiB frame exceeds cap - headroom.
    let oversized = vec![0u8; 64 * 1024];
    assert!(matches!(
        conn.send_app(1, &oversized),
        Err(TransportError::MessageTooLarge(_))
    ));
}

/// In-memory stream that hands out queued bytes on `read` (never more than the
/// caller's spare) and swallows writes. Lets a test feed a single oversized frame
/// through the wrapper without a socket.
struct ChunkStream {
    inbound: std::collections::VecDeque<u8>,
}

impl ChunkStream {
    fn new(bytes: &[u8]) -> Self {
        Self {
            inbound: bytes.iter().copied().collect(),
        }
    }
}

impl Read for ChunkStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let n = buf.len().min(self.inbound.len());
        for slot in buf.iter_mut().take(n) {
            *slot = self.inbound.pop_front().unwrap();
        }
        Ok(n)
    }
}

impl Write for ChunkStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(buf.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[test]
fn frame_exceeding_reader_buffer_is_message_too_large_not_disconnect() {
    // Fix B: a single inbound frame larger than the reader buffer fills the
    // buffer with one incomplete frame. `read_spare` then returns an empty slice
    // (nothing to compact — the whole buffer is one partial frame). The wrapper
    // must surface this as MessageTooLarge, NOT read into a zero-length slice and
    // misread the resulting `Ok(0)` as EOF/Disconnected.
    let dir = tmp_dir("reader_buf_too_large");

    // Build one valid, self-delimiting FIX frame bigger than a tiny reader
    // buffer but well under the 1 MiB frame-reader max (so the too-large trips
    // at the buffer, not at max_message_size).
    const READER_CAP: usize = 256;
    let mut buf = vec![0u8; 4096];
    let big_filler = vec![b'x'; 512]; // frame will be ~570 bytes > READER_CAP
    let frame = {
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
        fmt.field(34, b"1");
        fmt.field(49, sender().as_bytes());
        fmt.field(56, target().as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(58, &big_filler);
        let (start, len) = fmt.finish().unwrap();
        buf[start..start + len].to_vec()
    };
    assert!(
        frame.len() > READER_CAP,
        "frame must exceed the reader buffer to trip the guard"
    );

    let stream = ChunkStream::new(&frame);
    let mut conn: FixConnection<ChunkStream, MockDict> =
        FixConnection::builder().reader_capacity(READER_CAP).accept(
            stream,
            SessionState::new(Duration::from_secs(30)),
            session_cfg(target(), sender()),
            journal(dir.path()),
        );

    match conn.recv(Instant::now()) {
        Err(TransportError::MessageTooLarge(_)) => {}
        Err(other) => panic!(
            "an inbound frame exceeding the reader buffer must be MessageTooLarge, got {other:?}"
        ),
        Ok(Some(Message::Disconnected { reason })) => {
            panic!("frame exceeding reader buffer was misread as a disconnect: {reason:?}")
        }
        Ok(_) => panic!("frame exceeding reader buffer must not surface a message"),
    }
}
