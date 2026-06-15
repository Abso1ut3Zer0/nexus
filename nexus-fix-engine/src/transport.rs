use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nexus_fix_codec::{
    FrameFormatter, encode_fix_uint, find_tag, parse_fix_bool, parse_fix_seqnum, parse_fix_uint,
};

use crate::frame::{FrameReader, FrameWriter};
use crate::framework::SessionConfig;
use crate::persist::{FixJournal, ReplayItem};
use crate::session::{AdminMsg, DisconnectReason, Event, Out, SessionState, State};
use crate::timestamp::{UTC_TIMESTAMP_LEN, format_utc_timestamp};

const POLL_INTERVAL: Duration = Duration::from_millis(100);

/// Error from [`FixConnection`] operations.
#[derive(Debug)]
pub enum Error {
    Io(io::Error),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "I/O: {e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

/// Synchronous TCP driver for a sans-IO FIX session.
///
/// Owns a socket, a [`FrameReader`]/[`FrameWriter`] pair, a [`SessionState`],
/// and a [`FixJournal`]. The read loop fires [`SessionState`] handlers,
/// encodes outbound admin messages, drives gap-fill replay from the journal
/// on `Event::ResendRange`, and delivers in-sequence application frames to
/// the caller via the `on_app` callback in [`run`](Self::run).
///
/// Mirrors the pattern used by `nexus-web`'s `Client<S>`.
pub struct FixConnection<S> {
    stream: S,
    reader: FrameReader,
    writer: FrameWriter,
    state: SessionState,
    journal: FixJournal,
    config: SessionConfig,
    begin_string: &'static [u8],
    initiator: bool,
}

/// Builder for [`FixConnection`].
pub struct FixConnectionBuilder {
    reader_cap: usize,
    writer_cap: usize,
    nodelay: bool,
    connect_timeout: Option<Duration>,
}

impl FixConnectionBuilder {
    pub fn reader_capacity(mut self, n: usize) -> Self {
        self.reader_cap = n;
        self
    }

    pub fn writer_capacity(mut self, n: usize) -> Self {
        self.writer_cap = n;
        self
    }

    pub fn nodelay(mut self, v: bool) -> Self {
        self.nodelay = v;
        self
    }

    pub fn connect_timeout(mut self, d: Duration) -> Self {
        self.connect_timeout = Some(d);
        self
    }

    /// Connect to `addr` and return an initiator-mode [`FixConnection`].
    ///
    /// Sets `TCP_NODELAY` and a 100 ms read timeout for timer polling.
    pub fn connect<A: ToSocketAddrs>(
        self,
        addr: A,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
        begin_string: &'static [u8],
    ) -> io::Result<FixConnection<TcpStream>> {
        let stream = match self.connect_timeout {
            Some(t) => {
                let addrs: Vec<_> = addr.to_socket_addrs()?.collect();
                let first = addrs
                    .first()
                    .ok_or_else(|| io::Error::other("DNS resolved to zero addresses"))?;
                TcpStream::connect_timeout(first, t)?
            }
            None => TcpStream::connect(addr)?,
        };
        stream.set_nodelay(self.nodelay)?;
        stream.set_read_timeout(Some(POLL_INTERVAL))?;
        Ok(FixConnection {
            stream,
            reader: FrameReader::builder()
                .buffer_capacity(self.reader_cap)
                .build(),
            writer: FrameWriter::builder()
                .buffer_capacity(self.writer_cap)
                .build(),
            state,
            journal,
            config,
            begin_string,
            initiator: true,
        })
    }

    /// Wrap an already-connected stream as an acceptor-mode [`FixConnection`].
    ///
    /// The caller is responsible for applying socket options (nodelay, read
    /// timeout) before calling this.
    pub fn accept<S: Read + Write>(
        self,
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
        begin_string: &'static [u8],
    ) -> FixConnection<S> {
        FixConnection {
            stream,
            reader: FrameReader::builder()
                .buffer_capacity(self.reader_cap)
                .build(),
            writer: FrameWriter::builder()
                .buffer_capacity(self.writer_cap)
                .build(),
            state,
            journal,
            config,
            begin_string,
            initiator: false,
        }
    }
}

impl FixConnection<TcpStream> {
    pub fn builder() -> FixConnectionBuilder {
        FixConnectionBuilder {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            nodelay: true,
            connect_timeout: None,
        }
    }
}

impl<S: Read + Write> FixConnection<S> {
    /// Construct from pre-built parts (useful for testing).
    pub fn from_parts(
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
        begin_string: &'static [u8],
        initiator: bool,
    ) -> Self {
        Self {
            stream,
            reader: FrameReader::builder().build(),
            writer: FrameWriter::builder().build(),
            state,
            journal,
            config,
            begin_string,
            initiator,
        }
    }

    pub fn state(&self) -> &SessionState {
        &self.state
    }

    pub fn state_mut(&mut self) -> &mut SessionState {
        &mut self.state
    }

    /// Allocate the next outbound sequence number for an app message.
    pub fn allocate_seq(&mut self) -> u32 {
        self.state.allocate_seq(Instant::now())
    }

    /// Store `frame` in the journal under `seq` and write it to the stream.
    ///
    /// The caller must have pre-encoded the complete FIX frame (including
    /// `MsgSeqNum(34)=seq`) and must have obtained `seq` via
    /// [`allocate_seq`](Self::allocate_seq).
    pub fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        self.journal
            .store(seq, frame)
            .map_err(|e| Error::Io(io::Error::other(format!("{e:?}"))))?;
        write_all(&mut self.stream, frame)?;
        Ok(())
    }

    /// Initiate a clean logout and flush the Logout message.
    pub fn logout(&mut self) -> Result<(), Error> {
        let now = Instant::now();
        let out = self.state.logout(now);
        self.flush_out(out, now)
    }

    /// Drive the session loop until the session disconnects.
    ///
    /// If `initiator`, sends a Logon before entering the read loop.
    /// Calls `on_app` for each in-sequence application message frame.
    /// Admin messages and timers are handled internally.
    ///
    /// Returns the disconnect reason on a clean or protocol-level disconnect.
    /// Returns `Err` on unrecoverable I/O failure.
    pub fn run<H>(&mut self, mut on_app: H) -> Result<DisconnectReason, Error>
    where
        H: FnMut(&[u8]),
    {
        if self.initiator {
            let now = Instant::now();
            let out = self.state.connect(now);
            self.flush_out(out, now)?;
        }

        loop {
            // Read bytes into the frame reader's spare region.
            let spare = self.reader.spare();
            let n = match self.stream.read(spare) {
                Ok(0) => return Ok(DisconnectReason::Logout),
                Ok(n) => n,
                Err(e) if is_timeout(&e) => {
                    let now = Instant::now();
                    let out = self.state.on_timeout(now);
                    if let Some(Event::Disconnected { reason }) = out.event() {
                        self.flush_out(out, now)?;
                        return Ok(reason);
                    }
                    self.flush_out(out, now)?;
                    continue;
                }
                Err(e) => return Err(Error::Io(e)),
            };
            self.reader.filled(n);

            // Drain complete FIX messages from the buffer.
            loop {
                match self.reader.next() {
                    Ok(Some(frame)) => {
                        let frame = frame.to_vec();
                        let now = Instant::now();
                        if let Some(reason) = self.dispatch(&frame, now, &mut on_app)? {
                            return Ok(reason);
                        }
                    }
                    Ok(None) => break,
                    Err(_) => {}
                }
            }
            if self.reader.should_compact() {
                self.reader.compact();
            }
        }
    }

    fn dispatch<H>(
        &mut self,
        frame: &[u8],
        now: Instant,
        on_app: &mut H,
    ) -> Result<Option<DisconnectReason>, Error>
    where
        H: FnMut(&[u8]),
    {
        let sender_ok = find_tag(frame, 0, 49)
            .is_some_and(|s| s.slice(frame) == self.config.target.as_bytes());
        let target_ok = find_tag(frame, 0, 56)
            .is_some_and(|s| s.slice(frame) == self.config.sender.as_bytes());
        if !sender_ok || !target_ok {
            let out = self.state.on_comp_id_mismatch(now);
            self.flush_out(out, now)?;
            return Ok(Some(DisconnectReason::CompIdMismatch));
        }

        let seq = match find_tag(frame, 0, 34)
            .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
        {
            Some(s) => s as u32,
            None => return Ok(None),
        };

        let poss_dup = find_tag(frame, 0, 43)
            .and_then(|s| parse_fix_bool(s.slice(frame)).ok())
            .unwrap_or(false);

        let msg_type = match find_tag(frame, 0, 35) {
            Some(s) => s.slice(frame),
            None => return Ok(None),
        };

        let (out, is_app) = match msg_type {
            b"A" => {
                let hbi = find_tag(frame, 0, 108)
                    .and_then(|s| parse_fix_uint(s.slice(frame)).ok())
                    .unwrap_or(30);
                let reset = find_tag(frame, 0, 141)
                    .and_then(|s| parse_fix_bool(s.slice(frame)).ok())
                    .unwrap_or(false);
                let was_logon_sent = self.state.state() == State::LogonSent;
                (self.state.on_logon(seq, hbi, reset, !was_logon_sent, now), false)
            }
            b"5" => (self.state.on_logout(seq, poss_dup, now), false),
            b"0" => (self.state.on_heartbeat(seq, poss_dup, now), false),
            b"1" => {
                let id = find_tag(frame, 0, 112).map_or(&b""[..], |s| s.slice(frame));
                (self.state.on_test_request(seq, poss_dup, id, now), false)
            }
            b"2" => {
                let begin = find_tag(frame, 0, 7)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .unwrap_or(0) as u32;
                let end = find_tag(frame, 0, 16)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .unwrap_or(0) as u32;
                (
                    self.state
                        .on_resend_request(seq, poss_dup, begin, end, now),
                    false,
                )
            }
            b"3" => {
                let ref_seq = find_tag(frame, 0, 45)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .unwrap_or(0) as u32;
                (self.state.on_reject(seq, poss_dup, ref_seq, now), false)
            }
            b"4" => {
                let new_seq = find_tag(frame, 0, 36)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .unwrap_or(0) as u32;
                let gap_fill = find_tag(frame, 0, 123)
                    .and_then(|s| parse_fix_bool(s.slice(frame)).ok())
                    .unwrap_or(false);
                (
                    self.state.on_sequence_reset(seq, new_seq, gap_fill, now),
                    false,
                )
            }
            _ => (self.state.on_app(seq, poss_dup, now), true),
        };

        self.flush_out(out, now)?;

        match out.event() {
            Some(Event::Disconnected { reason }) => return Ok(Some(reason)),
            Some(Event::ResendRange { begin, end }) => self.do_resend(begin, end, now)?,
            Some(Event::App { .. }) if is_app => on_app(frame),
            _ => {}
        }

        Ok(None)
    }

    fn flush_out(&mut self, out: Out, now: Instant) -> Result<(), Error> {
        for admin in out.admin_messages() {
            self.encode_admin(admin, now);
        }
        if !self.writer.is_empty() {
            self.flush_writer()?;
        }
        Ok(())
    }

    fn encode_admin(&mut self, admin: AdminMsg, _now: Instant) {
        let unix_nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as i128;
        let mut ts = [0u8; UTC_TIMESTAMP_LEN];
        format_utc_timestamp(unix_nanos, &mut ts);

        let msg_type: &[u8] = match admin {
            AdminMsg::Logon { .. } => b"A",
            AdminMsg::Logout { .. } => b"5",
            AdminMsg::Heartbeat { .. } => b"0",
            AdminMsg::TestRequest { .. } => b"1",
            AdminMsg::ResendRequest { .. } => b"2",
            AdminMsg::SequenceReset { .. } => b"4",
        };

        let seq = match admin {
            AdminMsg::Logon { seq, .. }
            | AdminMsg::Logout { seq }
            | AdminMsg::Heartbeat { seq, .. }
            | AdminMsg::TestRequest { seq, .. }
            | AdminMsg::ResendRequest { seq, .. }
            | AdminMsg::SequenceReset { seq, .. } => seq,
        };

        let begin_string = self.begin_string;
        let sender = self.config.sender;
        let target = self.config.target;

        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(seq, &mut seq_buf);

        let (start, len) = {
            let spare = self.writer.spare();
            let mut fmt = FrameFormatter::new(spare, begin_string, msg_type);
            fmt.field(34, &seq_buf[..seq_n]);
            fmt.field(49, sender.as_bytes());
            fmt.field(56, target.as_bytes());
            fmt.field(52, &ts);

            match admin {
                AdminMsg::Logon { heart_bt_int_s, .. } => {
                    let mut buf = [0u8; 10];
                    let n = encode_fix_uint(heart_bt_int_s, &mut buf);
                    fmt.field(108, &buf[..n]);
                }
                AdminMsg::Logout { .. } | AdminMsg::Heartbeat { echo: None, .. } => {}
                AdminMsg::Heartbeat {
                    echo: Some((id, id_len)),
                    ..
                } => {
                    fmt.field(112, &id[..id_len as usize]);
                }
                AdminMsg::TestRequest { id, .. } => {
                    let mut buf = [0u8; 20];
                    let n = encode_u64(id, &mut buf);
                    fmt.field(112, &buf[..n]);
                }
                AdminMsg::ResendRequest { begin, .. } => {
                    let mut buf = [0u8; 10];
                    let n = encode_fix_uint(begin, &mut buf);
                    fmt.field(7, &buf[..n]);
                    fmt.field(16, b"0");
                }
                AdminMsg::SequenceReset { new_seq, .. } => {
                    fmt.field(43, b"Y");
                    fmt.field(123, b"Y");
                    let mut buf = [0u8; 10];
                    let n = encode_fix_uint(new_seq, &mut buf);
                    fmt.field(36, &buf[..n]);
                }
            }

            match fmt.finish() {
                Ok(sl) => sl,
                Err(_) => return,
            }
        };

        self.writer.commit(start, len);
    }

    fn flush_writer(&mut self) -> Result<(), Error> {
        while !self.writer.is_empty() {
            let n = self.stream.write(self.writer.data())?;
            if n == 0 {
                return Err(Error::Io(io::Error::other("write returned 0")));
            }
            self.writer.advance(n);
        }
        self.stream.flush()?;
        Ok(())
    }

    fn do_resend(&mut self, begin: u32, end: u32, now: Instant) -> Result<(), Error> {
        let mut items: Vec<ReplayItem> = Vec::new();
        self.journal.resend_range(begin, end, |item| items.push(item));

        for item in items {
            match item {
                ReplayItem::GapFill { seq, new_seq } => {
                    self.encode_admin(AdminMsg::SequenceReset { seq, new_seq }, now);
                }
                ReplayItem::App(frame) => {
                    if !self.writer.is_empty() {
                        self.flush_writer()?;
                    }
                    write_all(&mut self.stream, &frame)?;
                }
            }
        }

        if !self.writer.is_empty() {
            self.flush_writer()?;
        }
        Ok(())
    }
}

fn is_timeout(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
    )
}

fn write_all<S: Write>(stream: &mut S, data: &[u8]) -> Result<(), Error> {
    let mut offset = 0;
    while offset < data.len() {
        let n = stream.write(&data[offset..]).map_err(Error::Io)?;
        if n == 0 {
            return Err(Error::Io(io::Error::other("write returned 0")));
        }
        offset += n;
    }
    stream.flush().map_err(Error::Io)
}

fn encode_u64(v: u64, out: &mut [u8; 20]) -> usize {
    if v == 0 {
        out[0] = b'0';
        return 1;
    }
    let mut tmp = [0u8; 20];
    let mut n = 0;
    let mut x = v;
    while x > 0 {
        tmp[n] = b'0' + (x % 10) as u8;
        x /= 10;
        n += 1;
    }
    for i in 0..n {
        out[i] = tmp[n - 1 - i];
    }
    n
}
