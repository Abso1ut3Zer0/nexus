//! Tokio async adapter for the sans-IO FIX session layer.
//!
//! [`AsyncFixConnection`] drives [`SessionState`] over a tokio `AsyncRead +
//! AsyncWrite` stream, mirroring [`FixConnection`](nexus_fix_engine::FixConnection)
//! with `.await` on socket I/O and `tokio::time` for heartbeat/TestRequest timers.

#![cfg(unix)]

use std::io;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nexus_fix_codec::{
    FieldReader, FrameFormatter, encode_fix_uint, find_tag, parse_fix_bool, parse_fix_seqnum,
    parse_fix_uint,
};
use nexus_fix_engine::{
    AdminMsg, CompId, DisconnectReason, Event, FixJournal, FrameError, FrameReader, FrameWriter,
    Out, ReplayItem, SessionConfig, SessionError, SessionState, State,
};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::time::timeout_at;

const TS_LEN: usize = 21;

/// Error from [`AsyncFixConnection`].
#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    FrameTooLarge(usize),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "I/O: {e}"),
            Self::FrameTooLarge(n) => write!(f, "frame too large: {n} bytes"),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

/// Async FIX session transport over any `AsyncRead + AsyncWrite` stream.
///
/// Wraps [`SessionState`] with tokio I/O and timers. The session core is
/// identical to [`FixConnection`](nexus_fix_engine::FixConnection); only the
/// transport layer is async.
pub struct AsyncFixConnection<S> {
    stream: S,
    reader: FrameReader,
    writer: FrameWriter,
    state: SessionState,
    journal: FixJournal,
    config: SessionConfig,
    begin_string: &'static [u8],
}

impl<S: AsyncRead + AsyncWrite + Unpin> AsyncFixConnection<S> {
    pub fn from_parts(
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
        begin_string: &'static [u8],
    ) -> Self {
        Self {
            stream,
            reader: FrameReader::builder().build(),
            writer: FrameWriter::builder().build(),
            state,
            journal,
            config,
            begin_string,
        }
    }

    pub fn state(&self) -> &SessionState {
        &self.state
    }

    pub fn state_mut(&mut self) -> &mut SessionState {
        &mut self.state
    }

    pub fn allocate_seq(&mut self) -> Result<u32, SessionError> {
        self.state.allocate_seq(Instant::now())
    }

    pub fn wants_read(&self) -> bool {
        self.state.state() != State::Disconnected
    }

    pub fn wants_write(&self) -> bool {
        !self.writer.is_empty()
    }

    /// Initiates a session: encodes and sends the opening Logon.
    pub async fn connect(&mut self) -> Result<(), Error> {
        let out = self.state.connect(Instant::now());
        self.flush_out(out).await
    }

    /// Initiates a session with `ResetSeqNumFlag(141)=Y`.
    pub async fn connect_reset(&mut self) -> Result<(), Error> {
        let out = self
            .state
            .connect_reset(Instant::now())
            .map_err(|e| Error::Io(io::Error::other(e.to_string())))?;
        self.flush_out(out).await
    }

    /// Initiates an in-session sequence reset.
    pub async fn reset_sequence(&mut self) -> Result<(), Error> {
        let out = self
            .state
            .reset_sequence(Instant::now())
            .map_err(|e| Error::Io(io::Error::other(e.to_string())))?;
        self.flush_out(out).await
    }

    /// Receives one batch of bytes, dispatches all complete frames, and
    /// fires any due timers. Returns `Some(reason)` when the session ends.
    pub async fn recv<H>(&mut self, on_app: &mut H) -> Result<Option<DisconnectReason>, Error>
    where
        H: FnMut(&[u8]),
    {
        let deadline = self.state.next_timeout().map_or_else(
            || tokio::time::Instant::now() + Duration::from_secs(60),
            tokio::time::Instant::from_std,
        );

        let mut tmp = [0u8; 8192];
        let n = match timeout_at(deadline, self.stream.read(&mut tmp)).await {
            Ok(Ok(0)) => return Ok(Some(DisconnectReason::Logout)),
            Ok(Ok(n)) => n,
            Ok(Err(e)) => return Err(Error::Io(e)),
            Err(_elapsed) => {
                let now = Instant::now();
                let out = self.state.on_timeout(now);
                if let Some(Event::Disconnected { reason }) = out.event() {
                    self.flush_out(out).await?;
                    return Ok(Some(reason));
                }
                self.flush_out(out).await?;
                return Ok(None);
            }
        };

        self.reader
            .read(&tmp[..n])
            .map_err(|_| Error::FrameTooLarge(n))?;

        let now = Instant::now();
        loop {
            match self.reader.next() {
                Ok(Some(frame)) => {
                    let frame = frame.to_vec();
                    if let Some(reason) = self.dispatch(&frame, now, on_app).await? {
                        return Ok(Some(reason));
                    }
                }
                Ok(None) => break,
                Err(FrameError::MessageTooLarge { size }) => {
                    return Err(Error::FrameTooLarge(size));
                }
                Err(FrameError::Garbage { .. }) => {}
            }
        }

        if self.reader.should_compact() {
            self.reader.compact();
        }

        Ok(None)
    }

    /// Stores the frame in the journal and writes it to the stream.
    pub async fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        self.journal
            .store(seq, frame)
            .map_err(|e| Error::Io(io::Error::other(format!("{e:?}"))))?;
        self.write_through(frame).await
    }

    /// Initiates a clean logout.
    pub async fn logout(&mut self) -> Result<(), Error> {
        let out = self.state.logout(Instant::now());
        self.flush_out(out).await
    }

    async fn dispatch<H>(
        &mut self,
        frame: &[u8],
        now: Instant,
        on_app: &mut H,
    ) -> Result<Option<DisconnectReason>, Error>
    where
        H: FnMut(&[u8]),
    {
        let sender_ok =
            find_tag(frame, 0, 49).is_some_and(|s| s.slice(frame) == self.config.target.as_bytes());
        let target_ok =
            find_tag(frame, 0, 56).is_some_and(|s| s.slice(frame) == self.config.sender.as_bytes());
        if !sender_ok || !target_ok {
            let out = self.state.on_comp_id_mismatch(now);
            self.flush_out(out).await?;
            return Ok(Some(DisconnectReason::CompIdMismatch));
        }

        let seq = match find_tag(frame, 0, 34).and_then(|s| parse_fix_seqnum(s.slice(frame)).ok()) {
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
                (
                    self.state.on_logon(seq, hbi, reset, !was_logon_sent, now),
                    false,
                )
            }
            b"5" => (self.state.on_logout(seq, poss_dup, now), false),
            b"0" => {
                let echo_id =
                    find_tag(frame, 0, 112).and_then(|s| parse_fix_seqnum(s.slice(frame)).ok());
                (self.state.on_heartbeat(seq, poss_dup, echo_id, now), false)
            }
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
                    self.state.on_resend_request(seq, poss_dup, begin, end, now),
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

        self.flush_out(out).await?;

        match out.event() {
            Some(Event::Disconnected { reason }) => return Ok(Some(reason)),
            Some(Event::ResendRange { begin, end }) => self.do_resend(begin, end).await?,
            Some(Event::App { .. }) if is_app => on_app(frame),
            _ => {}
        }

        Ok(None)
    }

    async fn flush_out(&mut self, out: Out) -> Result<(), Error> {
        for admin in out.admin_messages() {
            self.encode_admin(admin);
        }
        if !self.writer.is_empty() {
            self.flush_writer().await?;
        }
        Ok(())
    }

    fn encode_admin(&mut self, admin: AdminMsg) {
        let ts = make_ts();

        let msg_type: &[u8] = match admin {
            AdminMsg::Logon { .. } | AdminMsg::LogonReset { .. } => b"A",
            AdminMsg::Logout { .. } => b"5",
            AdminMsg::Heartbeat { .. } => b"0",
            AdminMsg::TestRequest { .. } => b"1",
            AdminMsg::ResendRequest { .. } => b"2",
            AdminMsg::SequenceReset { .. } => b"4",
            AdminMsg::Reject { .. } => b"3",
        };

        let seq = match admin {
            AdminMsg::Logon { seq, .. }
            | AdminMsg::LogonReset { seq, .. }
            | AdminMsg::Logout { seq }
            | AdminMsg::Heartbeat { seq, .. }
            | AdminMsg::TestRequest { seq, .. }
            | AdminMsg::ResendRequest { seq, .. }
            | AdminMsg::SequenceReset { seq, .. }
            | AdminMsg::Reject { seq, .. } => seq,
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
                AdminMsg::Logon { heart_bt_int_s, .. }
                | AdminMsg::LogonReset { heart_bt_int_s, .. } => {
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
                AdminMsg::Reject {
                    ref_seq_num,
                    ref_tag_id,
                    session_reject_reason,
                    ..
                } => {
                    let mut buf = [0u8; 10];
                    let n = encode_fix_uint(ref_seq_num, &mut buf);
                    fmt.field(45, &buf[..n]);
                    if let Some(tag) = ref_tag_id {
                        let n = encode_fix_uint(tag, &mut buf);
                        fmt.field(371, &buf[..n]);
                    }
                    let n = encode_fix_uint(session_reject_reason as u32, &mut buf);
                    fmt.field(373, &buf[..n]);
                }
            }

            match fmt.finish() {
                Ok(sl) => sl,
                Err(_) => return,
            }
        };

        self.writer.commit(start, len);
    }

    async fn flush_writer(&mut self) -> Result<(), Error> {
        while !self.writer.is_empty() {
            let n = self.stream.write(self.writer.data()).await?;
            if n == 0 {
                return Err(Error::Io(io::Error::other("write returned 0")));
            }
            self.writer.advance(n);
        }
        self.stream.flush().await?;
        Ok(())
    }

    async fn write_through(&mut self, frame: &[u8]) -> Result<(), Error> {
        if self.writer.remaining() < frame.len() {
            self.flush_writer().await?;
        }
        if self.writer.remaining() >= frame.len() {
            let spare = self.writer.spare();
            spare[..frame.len()].copy_from_slice(frame);
            self.writer.commit(0, frame.len());
        } else {
            self.stream.write_all(frame).await?;
            self.stream.flush().await?;
            return Ok(());
        }
        self.flush_writer().await
    }

    async fn do_resend(&mut self, begin: u32, end: u32) -> Result<(), Error> {
        enum Item {
            Gap(u32, u32),
            App(Vec<u8>),
        }

        let ts = make_ts();
        let begin_string = self.begin_string;
        let sender = self.config.sender;
        let target = self.config.target;

        let items: Vec<Item> = self
            .journal
            .resend(begin, end)
            .map(|r| match r {
                ReplayItem::GapFill { seq, new_seq } => Item::Gap(seq, new_seq),
                ReplayItem::App(d) => Item::App(d.to_vec()),
            })
            .collect();

        for item in items {
            let ok = match &item {
                Item::Gap(seq, new_seq) => encode_gap_fill(
                    &mut self.writer,
                    begin_string,
                    sender,
                    target,
                    &ts,
                    *seq,
                    *new_seq,
                ),
                Item::App(data) => reframe_app(&mut self.writer, data, &ts, begin_string),
            };
            if ok.is_err() {
                self.flush_writer().await?;
                let retry = match &item {
                    Item::Gap(seq, new_seq) => encode_gap_fill(
                        &mut self.writer,
                        begin_string,
                        sender,
                        target,
                        &ts,
                        *seq,
                        *new_seq,
                    ),
                    Item::App(data) => reframe_app(&mut self.writer, data, &ts, begin_string),
                };
                retry.map_err(|()| {
                    Error::FrameTooLarge(self.writer.remaining().saturating_add(1))
                })?;
            }
        }
        self.flush_writer().await
    }
}

impl AsyncFixConnection<tokio::net::TcpStream> {
    /// Connects a TCP stream, enables `TCP_NODELAY`, and wraps it.
    pub async fn tcp_connect(
        addr: std::net::SocketAddr,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
        begin_string: &'static [u8],
    ) -> io::Result<Self> {
        let stream = tokio::net::TcpStream::connect(addr).await?;
        stream.set_nodelay(true)?;
        Ok(Self::from_parts(
            stream,
            state,
            config,
            journal,
            begin_string,
        ))
    }
}

fn make_ts() -> [u8; TS_LEN] {
    let unix_nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos() as i128;
    let mut ts = [0u8; TS_LEN];
    format_utc_timestamp(unix_nanos, &mut ts);
    ts
}

fn format_utc_timestamp(unix_nanos: i128, out: &mut [u8; TS_LEN]) {
    let secs = unix_nanos.div_euclid(1_000_000_000) as i64;
    let millis = (unix_nanos.rem_euclid(1_000_000_000) / 1_000_000) as u32;
    let days = secs.div_euclid(86_400);
    let sod = secs.rem_euclid(86_400) as u32;
    let (y, m, d) = civil_from_days(days);

    write_digits(&mut out[0..4], y.max(0) as u32);
    write_digits(&mut out[4..6], m);
    write_digits(&mut out[6..8], d);
    out[8] = b'-';
    write_digits(&mut out[9..11], sod / 3600);
    out[11] = b':';
    write_digits(&mut out[12..14], sod / 60 % 60);
    out[14] = b':';
    write_digits(&mut out[15..17], sod % 60);
    out[17] = b'.';
    write_digits(&mut out[18..21], millis);
}

fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = (z - era * 146_097) as u64;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = (if mp < 10 { mp + 3 } else { mp - 9 }) as u32;
    (y + i64::from(m <= 2), m, d)
}

fn write_digits(out: &mut [u8], mut v: u32) {
    for slot in out.iter_mut().rev() {
        *slot = b'0' + (v % 10) as u8;
        v /= 10;
    }
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

fn encode_gap_fill(
    writer: &mut FrameWriter,
    begin_string: &'static [u8],
    sender: CompId,
    target: CompId,
    ts: &[u8],
    seq: u32,
    new_seq: u32,
) -> Result<(), ()> {
    let spare = writer.spare();
    let mut seq_buf = [0u8; 10];
    let seq_n = encode_fix_uint(seq, &mut seq_buf);
    let mut fmt = FrameFormatter::new(spare, begin_string, b"4");
    fmt.field(34, &seq_buf[..seq_n]);
    fmt.field(49, sender.as_bytes());
    fmt.field(56, target.as_bytes());
    fmt.field(52, ts);
    fmt.field(43, b"Y");
    fmt.field(123, b"Y");
    let mut nsq_buf = [0u8; 10];
    let nsq_n = encode_fix_uint(new_seq, &mut nsq_buf);
    fmt.field(36, &nsq_buf[..nsq_n]);
    let (start, len) = fmt.finish().map_err(|_| ())?;
    writer.commit(start, len);
    Ok(())
}

fn reframe_app(
    writer: &mut FrameWriter,
    orig: &[u8],
    ts: &[u8],
    begin_string: &'static [u8],
) -> Result<(), ()> {
    let msg_type = find_tag(orig, 0, 35).map_or(b"D" as &[u8], |s| s.slice(orig));
    let orig_time = find_tag(orig, 0, 52).map(|s| s.slice(orig));

    let spare = writer.spare();
    let mut fmt = FrameFormatter::new(spare, begin_string, msg_type);
    let mut poss_dup_done = false;

    for field in FieldReader::new(orig, 0) {
        match field.tag {
            8 | 9 | 10 | 35 | 43 | 122 => {}
            52 => {
                fmt.field(52, ts);
                fmt.field(43, b"Y");
                if let Some(t) = orig_time {
                    fmt.field(122, t);
                }
                poss_dup_done = true;
            }
            _ => fmt.field(field.tag, field.value.slice(orig)),
        }
    }

    if !poss_dup_done {
        fmt.field(43, b"Y");
        if let Some(t) = orig_time {
            fmt.field(122, t);
        }
    }

    let (start, len) = fmt.finish().map_err(|_| ())?;
    writer.commit(start, len);
    Ok(())
}
