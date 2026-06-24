use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant};

use nexus_fix_codec::{
    FieldReader, FixAdminMsg, FixDictionary, FixHeader, FrameFormatter, encode_fix_uint, find_tag,
    parse_fix_bool, parse_fix_seqnum, parse_fix_uint,
};

use crate::frame::{FrameError, FrameWriter};
use crate::framework::{Message, MessageReader, MessageWriter, SessionConfig, SessionError};
use crate::persist::{FixJournal, ReplayItem};
use crate::session::{DisconnectReason, Event, SessionState, State};
use crate::timestamp::UTC_TIMESTAMP_LEN;

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    FrameTooLarge(usize),
    Protocol(SessionError),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "I/O: {e}"),
            Self::FrameTooLarge(n) => write!(f, "frame too large: {n} bytes"),
            Self::Protocol(e) => write!(f, "protocol: {e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

pub struct FixConnection<S, D: FixDictionary> {
    stream: S,
    reader: MessageReader<D>,
    writer: MessageWriter<D>,
    state: SessionState,
    journal: FixJournal,
    config: SessionConfig,
    garbage_frames: u64,
}

pub struct FixConnectionBuilder<D: FixDictionary> {
    reader_cap: usize,
    writer_cap: usize,
    nodelay: bool,
    connect_timeout: Option<Duration>,
    _dict: std::marker::PhantomData<fn() -> D>,
}

impl<D: FixDictionary> FixConnectionBuilder<D> {
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

    pub fn connect<A: ToSocketAddrs>(
        self,
        addr: A,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<FixConnection<TcpStream, D>> {
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
        Ok(FixConnection {
            stream,
            reader: MessageReader::with_frame_reader(
                crate::frame::FrameReader::builder()
                    .buffer_capacity(self.reader_cap)
                    .build(),
            ),
            writer: MessageWriter::with_frame_writer(
                FrameWriter::builder()
                    .buffer_capacity(self.writer_cap)
                    .build(),
            ),
            state,
            journal,
            config,
            garbage_frames: 0,
        })
    }

    pub fn accept<S: Read + Write>(
        self,
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> FixConnection<S, D> {
        FixConnection {
            stream,
            reader: MessageReader::with_frame_reader(
                crate::frame::FrameReader::builder()
                    .buffer_capacity(self.reader_cap)
                    .build(),
            ),
            writer: MessageWriter::with_frame_writer(
                FrameWriter::builder()
                    .buffer_capacity(self.writer_cap)
                    .build(),
            ),
            state,
            journal,
            config,
            garbage_frames: 0,
        }
    }
}

impl<D: FixDictionary> FixConnection<TcpStream, D> {
    pub fn builder() -> FixConnectionBuilder<D> {
        FixConnectionBuilder {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            nodelay: true,
            connect_timeout: None,
            _dict: std::marker::PhantomData,
        }
    }
}

impl<S: Read + Write, D: FixDictionary> FixConnection<S, D> {
    pub fn from_parts(
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> Self {
        Self {
            stream,
            reader: MessageReader::new(),
            writer: MessageWriter::new(),
            state,
            journal,
            config,
            garbage_frames: 0,
        }
    }

    pub fn state(&self) -> &SessionState {
        &self.state
    }

    pub fn state_mut(&mut self) -> &mut SessionState {
        &mut self.state
    }

    pub fn garbage_frame_count(&self) -> u64 {
        self.garbage_frames
    }

    pub fn allocate_seq(&mut self) -> u32 {
        self.state.allocate_seq(Instant::now())
    }

    pub fn wants_read(&self) -> bool {
        self.state.state() != State::Disconnected
    }

    pub fn wants_write(&self) -> bool {
        !self.writer.is_empty()
    }

    pub fn flush(&mut self) -> Result<(), Error> {
        self.writer.flush_to(&mut self.stream).map_err(Error::Io)
    }

    pub fn connect(&mut self, now: Instant) -> Result<(), Error> {
        let out = self.state.connect(now);
        for admin in out.admin_messages() {
            self.writer.encode_admin(admin, &self.config);
        }
        if !self.writer.is_empty() {
            self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
        }
        Ok(())
    }

    pub fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        self.journal
            .store(seq, frame)
            .map_err(|e| Error::Io(io::Error::other(format!("{e:?}"))))?;
        write_through(&mut self.stream, &mut self.writer.inner, frame)
    }

    pub fn logout(&mut self, now: Instant) -> Result<(), Error> {
        let out = self.state.logout(now);
        for admin in out.admin_messages() {
            self.writer.encode_admin(admin, &self.config);
        }
        if !self.writer.is_empty() {
            self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
        }
        Ok(())
    }

    pub fn recv(&mut self, now: Instant) -> Result<Option<Message<'_, D>>, Error> {
        loop {
            if self.reader.inner.should_compact() {
                self.reader.inner.compact();
            }

            match self.reader.inner.next() {
                Err(FrameError::MessageTooLarge { size }) => {
                    return Err(Error::FrameTooLarge(size));
                }
                Err(FrameError::Garbage { .. }) => {
                    self.garbage_frames += 1;
                }
                Ok(None) => {
                    let n = {
                        let spare = self.reader.inner.spare();
                        match self.stream.read(spare) {
                            Ok(n) => n,
                            Err(e) if is_timeout(&e) => {
                                let out = self.state.on_timeout(now);
                                for admin in out.admin_messages() {
                                    self.writer.encode_admin(admin, &self.config);
                                }
                                if !self.writer.is_empty() {
                                    self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
                                }
                                if let Some(Event::Disconnected { reason }) = out.event() {
                                    return Ok(Some(Message::Disconnected { reason }));
                                }
                                return Ok(None);
                            }
                            Err(e) => return Err(Error::Io(e)),
                        }
                    };
                    if n == 0 {
                        return Ok(Some(Message::Disconnected {
                            reason: DisconnectReason::Logout,
                        }));
                    }
                    self.reader.inner.filled(n);
                }
                Ok(Some(raw)) => {
                    self.reader.frame.clear();
                    self.reader.frame.extend_from_slice(raw);
                    break;
                }
            }
        }

        let frame = &self.reader.frame[..];

        let (sender_ok, target_ok, seq, poss_dup) = {
            let hdr = D::Header::decode(frame);
            let sender_ok = hdr
                .sender_comp_id()
                .is_some_and(|fv| fv.as_bytes() == self.config.target.as_bytes());
            let target_ok = hdr
                .target_comp_id()
                .is_some_and(|fv| fv.as_bytes() == self.config.sender.as_bytes());
            let seq = match hdr.msg_seq_num() {
                Some(fv) => match fv.checked() {
                    Ok(num) => num as u32,
                    Err(_) => {
                        return Err(Error::Protocol(SessionError::MalformedField { tag: 34 }));
                    }
                },
                None => return Err(Error::Protocol(SessionError::MissingMsgSeqNum)),
            };
            let poss_dup = hdr
                .poss_dup_flag()
                .and_then(|fv| fv.checked().ok())
                .unwrap_or(false);
            (sender_ok, target_ok, seq, poss_dup)
        };

        if !sender_ok || !target_ok {
            let out = self.state.on_comp_id_mismatch(now);
            for admin in out.admin_messages() {
                self.writer.encode_admin(admin, &self.config);
            }
            if !self.writer.is_empty() {
                self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
            }
            return Ok(Some(Message::Disconnected {
                reason: DisconnectReason::CompIdMismatch,
            }));
        }

        let raw_type = match find_tag(frame, 0, 35) {
            Some(s) => s.slice(frame),
            None => return Err(Error::Protocol(SessionError::MissingMsgType)),
        };

        match raw_type {
            b"A" => {
                let hbi = find_tag(frame, 0, 108)
                    .and_then(|s| parse_fix_uint(s.slice(frame)).ok())
                    .unwrap_or(30);
                let reset = find_tag(frame, 0, 141)
                    .and_then(|s| parse_fix_bool(s.slice(frame)).ok())
                    .unwrap_or(false);
                let was_logon_sent = self.state.state() == State::LogonSent;
                let out = self.state.on_logon(seq, hbi, reset, !was_logon_sent, now);
                for admin in out.admin_messages() {
                    self.writer.encode_admin(admin, &self.config);
                }
                if !self.writer.is_empty() {
                    self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
                }
                if let Some(Event::Disconnected { reason }) = out.event() {
                    return Ok(Some(Message::Disconnected { reason }));
                }
                let msg = D::Logon::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                Ok(Some(if was_logon_sent {
                    Message::LogonAcknowledged { msg }
                } else {
                    Message::LogonRequest { msg }
                }))
            }
            b"5" => {
                let was_logout_pending = self.state.state() == State::LogoutPending;
                let out = self.state.on_logout(seq, poss_dup, now);
                for admin in out.admin_messages() {
                    self.writer.encode_admin(admin, &self.config);
                }
                if !self.writer.is_empty() {
                    self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
                }
                if let Some(Event::Disconnected { reason }) = out.event() {
                    return Ok(Some(Message::Disconnected { reason }));
                }
                let msg = D::Logout::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                Ok(Some(if was_logout_pending {
                    Message::LogoutAcknowledged { msg }
                } else {
                    Message::LogoutRequest { msg }
                }))
            }
            b"0" => {
                let out = self.state.on_heartbeat(seq, poss_dup, now);
                for admin in out.admin_messages() {
                    self.writer.encode_admin(admin, &self.config);
                }
                if !self.writer.is_empty() {
                    self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
                }
                let msg = D::Heartbeat::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                Ok(Some(Message::Heartbeat { msg }))
            }
            b"1" => {
                let test_req_id =
                    find_tag(frame, 0, 112).map_or_else(|| b"".as_ref(), |s| s.slice(frame));
                let out = self.state.on_test_request(seq, poss_dup, test_req_id, now);
                for admin in out.admin_messages() {
                    self.writer.encode_admin(admin, &self.config);
                }
                if !self.writer.is_empty() {
                    self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
                }
                let msg = D::TestRequest::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                Ok(Some(Message::TestRequest { msg }))
            }
            b"2" => {
                let begin = find_tag(frame, 0, 7)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .map_or(0, |v| v as u32);
                let end = find_tag(frame, 0, 16)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .map_or(0, |v| v as u32);
                let out = self.state.on_resend_request(seq, poss_dup, begin, end, now);
                for admin in out.admin_messages() {
                    self.writer.encode_admin(admin, &self.config);
                }
                if !self.writer.is_empty() {
                    self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
                }
                if let Some(Event::ResendRange { begin: rb, end: re }) = out.event() {
                    let re = if re == 0 {
                        self.state.next_outbound_seq().saturating_sub(1)
                    } else {
                        re.min(self.state.next_outbound_seq().saturating_sub(1))
                    };
                    do_resend::<S, D>(
                        rb,
                        re,
                        &self.journal,
                        &mut self.writer,
                        &mut self.stream,
                        &self.config,
                    )?;
                }
                let msg = D::ResendRequest::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                Ok(Some(Message::ResendRequest { msg }))
            }
            b"4" => {
                let new_seq = find_tag(frame, 0, 36)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .map_or(0, |v| v as u32);
                let gap_fill = find_tag(frame, 0, 123)
                    .and_then(|s| parse_fix_bool(s.slice(frame)).ok())
                    .unwrap_or(false);
                let out = self.state.on_sequence_reset(seq, new_seq, gap_fill, now);
                for admin in out.admin_messages() {
                    self.writer.encode_admin(admin, &self.config);
                }
                if !self.writer.is_empty() {
                    self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
                }
                let msg = D::SequenceReset::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                Ok(Some(Message::SequenceReset { msg }))
            }
            b"3" => {
                let ref_seq = find_tag(frame, 0, 45)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .map_or(0, |v| v as u32);
                let out = self.state.on_reject(seq, poss_dup, ref_seq, now);
                for admin in out.admin_messages() {
                    self.writer.encode_admin(admin, &self.config);
                }
                if !self.writer.is_empty() {
                    self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
                }
                let msg = D::Reject::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                Ok(Some(Message::Reject { msg }))
            }
            _ => {
                let out = self.state.on_app(seq, poss_dup, now);
                for admin in out.admin_messages() {
                    self.writer.encode_admin(admin, &self.config);
                }
                if !self.writer.is_empty() {
                    self.writer.flush_to(&mut self.stream).map_err(Error::Io)?;
                }
                if let Some(Event::Disconnected { reason }) = out.event() {
                    return Ok(Some(Message::Disconnected { reason }));
                }
                if matches!(out.event(), Some(Event::App { .. })) {
                    return Ok(Some(Message::Application {
                        header: D::Header::decode(frame),
                    }));
                }
                Ok(None) // gap: ResendRequest queued, nothing to surface
            }
        }
    }
}

fn do_resend<S: Write, D: FixDictionary>(
    begin: u32,
    end: u32,
    journal: &FixJournal,
    writer: &mut MessageWriter<D>,
    stream: &mut S,
    config: &SessionConfig,
) -> Result<(), Error> {
    use std::time::{SystemTime, UNIX_EPOCH};

    let unix_nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos() as i128;
    let mut ts = [0u8; UTC_TIMESTAMP_LEN];
    crate::timestamp::format_utc_timestamp(unix_nanos, &mut ts);

    let iter = journal.resend(begin, end);

    for item in iter {
        let ok = match &item {
            ReplayItem::GapFill { seq, new_seq } => encode_gap_fill(
                &mut writer.inner,
                D::BEGIN_STRING,
                config,
                &ts,
                *seq,
                *new_seq,
            ),
            ReplayItem::App(orig) => reframe_app(&mut writer.inner, orig, &ts, D::BEGIN_STRING),
        };
        if ok.is_err() {
            writer.flush_to(stream).map_err(Error::Io)?;
            match item {
                ReplayItem::GapFill { seq, new_seq } => {
                    encode_gap_fill(
                        &mut writer.inner,
                        D::BEGIN_STRING,
                        config,
                        &ts,
                        seq,
                        new_seq,
                    )
                    .map_err(|()| {
                        Error::FrameTooLarge(writer.inner.remaining().saturating_add(1))
                    })?;
                }
                ReplayItem::App(orig) => {
                    if reframe_app(&mut writer.inner, orig, &ts, D::BEGIN_STRING).is_err() {
                        let mut tmp = vec![0u8; orig.len() + 512];
                        let (start, len) = reframe_app_into(&mut tmp, orig, &ts, D::BEGIN_STRING)
                            .ok_or(Error::FrameTooLarge(orig.len()))?;
                        tmp.copy_within(start..start + len, 0);
                        tmp.truncate(len);
                        write_through(stream, &mut writer.inner, &tmp)?;
                    }
                }
            }
        }
    }
    writer.flush_to(stream).map_err(Error::Io)
}

fn write_through<S: Write>(
    stream: &mut S,
    writer: &mut FrameWriter,
    frame: &[u8],
) -> Result<(), Error> {
    if writer.remaining() < frame.len() {
        flush_to(stream, writer)?;
    }
    if writer.remaining() >= frame.len() {
        let spare = writer.spare();
        spare[..frame.len()].copy_from_slice(frame);
        writer.commit(0, frame.len());
    } else {
        let mut off = 0;
        while off < frame.len() {
            let n = stream.write(&frame[off..]).map_err(Error::Io)?;
            if n == 0 {
                return Err(Error::Io(io::Error::other("write returned 0")));
            }
            off += n;
        }
        stream.flush().map_err(Error::Io)?;
        return Ok(());
    }
    flush_to(stream, writer)
}

fn flush_to<S: Write>(stream: &mut S, writer: &mut FrameWriter) -> Result<(), Error> {
    while !writer.is_empty() {
        let n = stream.write(writer.data())?;
        if n == 0 {
            return Err(Error::Io(io::Error::other("write returned 0")));
        }
        writer.advance(n);
    }
    stream.flush()?;
    Ok(())
}

fn encode_gap_fill(
    writer: &mut FrameWriter,
    begin_string: &'static [u8],
    config: &SessionConfig,
    ts: &[u8],
    seq: u32,
    new_seq: u32,
) -> Result<(), ()> {
    let spare = writer.spare();
    let mut seq_buf = [0u8; 10];
    let seq_n = encode_fix_uint(seq, &mut seq_buf);
    let mut fmt = FrameFormatter::new(spare, begin_string, b"4");
    fmt.field(34, &seq_buf[..seq_n]);
    fmt.field(49, config.sender.as_bytes());
    fmt.field(56, config.target.as_bytes());
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
    let spare = writer.spare();
    let (start, len) = reframe_app_into(spare, orig, ts, begin_string).ok_or(())?;
    writer.commit(start, len);
    Ok(())
}

fn reframe_app_into(
    buf: &mut [u8],
    orig: &[u8],
    ts: &[u8],
    begin_string: &'static [u8],
) -> Option<(usize, usize)> {
    let msg_type = find_tag(orig, 0, 35).map_or(b"D" as &[u8], |s| s.slice(orig));
    let orig_time = find_tag(orig, 0, 52).map(|s| s.slice(orig));

    let mut fmt = FrameFormatter::new(buf, begin_string, msg_type);
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

    fmt.finish().ok()
}

fn is_timeout(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
    )
}
