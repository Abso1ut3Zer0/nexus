#![cfg(unix)]

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use nexus_fix_codec::{FrameFormatter, encode_fix_uint};
use nexus_fix_engine::{
    CompId, DisconnectReason, FixConnection, FixJournal, SessionConfig, SessionState,
    TransportError,
};

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

fn drive<H>(
    conn: &mut FixConnection<TcpStream>,
    mut on_app: H,
) -> Result<DisconnectReason, TransportError>
where
    H: FnMut(&[u8]),
{
    loop {
        if let Some(reason) = conn.recv(Instant::now(), &mut on_app)? {
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
}

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

    let mut conn = FixConnection::from_parts(
        client_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(t_sender, t_target),
        journal(&dir),
        b"FIX.4.4",
    );
    conn.connect(Instant::now()).unwrap();

    let reason = drive(&mut conn, |_| {}).unwrap();
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

    let mut received: Vec<Vec<u8>> = Vec::new();
    let dir2 = tmp_dir("acceptor_app_srv");
    let mut conn = FixConnection::from_parts(
        server_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(target(), sender()),
        journal(&dir2),
        b"FIX.4.4",
    );

    let reason = drive(&mut conn, |frame| received.push(frame.to_vec())).unwrap();
    assert_eq!(reason, DisconnectReason::Logout);
    assert_eq!(received.len(), 1);
    assert!(received[0].starts_with(b"8=FIX.4.4"));

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
        fmt.field(7, b"2");
        fmt.field(16, b"3");
        let (start, len) = fmt.finish().unwrap();
        peer.stream.write_all(&rbuf[start..start + len]).unwrap();
        peer.stream.flush().unwrap();
        peer.next_out = 3;

        let n = peer.recv_msg(&mut buf);
        assert!(n > 0);

        peer.send_logout();
        let _ = peer.recv_msg(&mut buf);
    });

    let mut conn = FixConnection::from_parts(
        client_sock,
        SessionState::new(Duration::from_secs(30)),
        session_cfg(sender(), target()),
        journal(&dir_cli),
        b"FIX.4.4",
    );
    conn.connect(Instant::now()).unwrap();

    let reason = drive(&mut conn, |_| {}).unwrap();
    assert_eq!(reason, DisconnectReason::Logout);

    handle.join().unwrap();
    let _ = dir_srv;
}
