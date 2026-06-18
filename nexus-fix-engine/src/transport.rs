use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nexus_fix_codec::{
    FieldReader, FrameFormatter, encode_fix_uint, find_tag, parse_fix_bool, parse_fix_seqnum,
    parse_fix_uint,
};

use crate::frame::{FrameError, FrameReader, FrameWriter};
use crate::framework::{CompId, SessionConfig};
use crate::persist::{FixJournal, ReplayItem};
use crate::session::{AdminMsg, DisconnectReason, Event, Out, SessionState, State};
use crate::timestamp::{UTC_TIMESTAMP_LEN, format_utc_timestamp};

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

pub struct FixConnection<S> {
    stream: S,
    reader: FrameReader,
    writer: FrameWriter,
    state: SessionState,
    journal: FixJournal,
    config: SessionConfig,
    begin_string: &'static [u8],
}

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
        })
    }

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

    pub fn allocate_seq(&mut self) -> u32 {
        self.state.allocate_seq(Instant::now())
    }

    pub fn connect(&mut self, now: Instant) -> Result<(), Error> {
        let out = self.state.connect(now);
        self.flush_out(out)
    }

    pub fn recv<H>(
        &mut self,
        now: Instant,
        on_app: &mut H,
    ) -> Result<Option<DisconnectReason>, Error>
    where
        H: FnMut(&[u8]),
    {
        let spare = self.reader.spare();
        let n = match self.stream.read(spare) {
            Ok(0) => return Ok(Some(DisconnectReason::Logout)),
            Ok(n) => n,
            Err(e) if is_timeout(&e) => {
                let out = self.state.on_timeout(now);
                if let Some(Event::Disconnected { reason }) = out.event() {
                    self.flush_out(out)?;
                    return Ok(Some(reason));
                }
                self.flush_out(out)?;
                return Ok(None);
            }
            Err(e) => return Err(Error::Io(e)),
        };
        self.reader.filled(n);

        loop {
            match self.reader.next() {
                Ok(Some(frame)) => {
                    let frame = frame.to_vec();
                    if let Some(reason) = self.dispatch(&frame, now, on_app)? {
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

    pub fn wants_read(&self) -> bool {
        self.state.state() != State::Disconnected
    }

    pub fn wants_write(&self) -> bool {
        !self.writer.is_empty()
    }

    pub fn flush(&mut self) -> Result<(), Error> {
        self.flush_writer()
    }

    pub fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        self.journal
            .store(seq, frame)
            .map_err(|e| Error::Io(io::Error::other(format!("{e:?}"))))?;
        write_through(&mut self.stream, &mut self.writer, frame)
    }

    pub fn logout(&mut self, now: Instant) -> Result<(), Error> {
        let out = self.state.logout(now);
        self.flush_out(out)
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
        let Some(h) = parse_frame_header(frame) else {
            return Ok(None);
        };

        if h.sender != self.config.target.as_bytes() || h.target != self.config.sender.as_bytes() {
            let out = self.state.on_comp_id_mismatch(now);
            self.flush_out(out)?;
            return Ok(Some(DisconnectReason::CompIdMismatch));
        }

        let (out, is_app) = match h.msg_type {
            b"A" => {
                let was_logon_sent = self.state.state() == State::LogonSent;
                (
                    self.state
                        .on_logon(h.seq, h.heart_bt_int, h.reset, !was_logon_sent, now),
                    false,
                )
            }
            b"5" => (self.state.on_logout(h.seq, h.poss_dup, now), false),
            b"0" => (self.state.on_heartbeat(h.seq, h.poss_dup, now), false),
            b"1" => (
                self.state
                    .on_test_request(h.seq, h.poss_dup, h.test_req_id, now),
                false,
            ),
            b"2" => (
                self.state
                    .on_resend_request(h.seq, h.poss_dup, h.begin_seq, h.end_seq, now),
                false,
            ),
            b"3" => (
                self.state.on_reject(h.seq, h.poss_dup, h.ref_seq, now),
                false,
            ),
            b"4" => (
                self.state
                    .on_sequence_reset(h.seq, h.new_seq_no, h.gap_fill, now),
                false,
            ),
            _ => (self.state.on_app(h.seq, h.poss_dup, now), true),
        };

        self.flush_out(out)?;

        match out.event() {
            Some(Event::Disconnected { reason }) => return Ok(Some(reason)),
            Some(Event::ResendRange { begin, end }) => self.do_resend(begin, end)?,
            Some(Event::App { .. }) if is_app => on_app(frame),
            _ => {}
        }

        Ok(None)
    }

    fn flush_out(&mut self, out: Out) -> Result<(), Error> {
        for admin in out.admin_messages() {
            self.encode_admin(admin);
        }
        if !self.writer.is_empty() {
            self.flush_writer()?;
        }
        Ok(())
    }

    fn encode_admin(&mut self, admin: AdminMsg) {
        let ts = make_ts();

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
        flush_to(&mut self.stream, &mut self.writer)
    }

    fn do_resend(&mut self, begin: u32, end: u32) -> Result<(), Error> {
        let ts = make_ts();
        let begin_string = self.begin_string;
        let sender = self.config.sender;
        let target = self.config.target;

        let iter = self.journal.resend(begin, end);
        let writer = &mut self.writer;
        let stream = &mut self.stream;

        for item in iter {
            let ok = match &item {
                ReplayItem::GapFill { seq, new_seq } => {
                    encode_gap_fill(writer, begin_string, sender, target, &ts, *seq, *new_seq)
                }
                ReplayItem::App(orig) => reframe_app(writer, orig, &ts, begin_string),
            };
            if ok.is_err() {
                flush_to(stream, writer)?;
                match item {
                    ReplayItem::GapFill { seq, new_seq } => {
                        encode_gap_fill(writer, begin_string, sender, target, &ts, seq, new_seq)
                            .map_err(|()| {
                                Error::FrameTooLarge(writer.remaining().saturating_add(1))
                            })?;
                    }
                    ReplayItem::App(orig) => {
                        if reframe_app(writer, orig, &ts, begin_string).is_err() {
                            // frame exceeds writer capacity; reframe into a heap buffer and write through
                            let mut tmp = vec![0u8; orig.len() + 512];
                            let (start, len) = reframe_app_into(&mut tmp, orig, &ts, begin_string)
                                .ok_or(Error::FrameTooLarge(orig.len()))?;
                            tmp.copy_within(start..start + len, 0);
                            tmp.truncate(len);
                            write_through(stream, writer, &tmp)?;
                        }
                    }
                }
            }
        }
        flush_to(stream, writer)
    }
}

fn make_ts() -> [u8; UTC_TIMESTAMP_LEN] {
    let unix_nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos() as i128;
    let mut ts = [0u8; UTC_TIMESTAMP_LEN];
    format_utc_timestamp(unix_nanos, &mut ts);
    ts
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
        // frame exceeds writer capacity — write directly (writer is empty after flush)
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

struct FrameHeader<'a> {
    sender: &'a [u8],
    target: &'a [u8],
    msg_type: &'a [u8],
    seq: u32,
    poss_dup: bool,
    heart_bt_int: u32,
    reset: bool,
    test_req_id: &'a [u8],
    begin_seq: u32,
    end_seq: u32,
    ref_seq: u32,
    new_seq_no: u32,
    gap_fill: bool,
}

fn parse_frame_header(frame: &[u8]) -> Option<FrameHeader<'_>> {
    let mut sender: &[u8] = b"";
    let mut target: &[u8] = b"";
    let mut msg_type = None::<&[u8]>;
    let mut seq = None::<u32>;
    let mut poss_dup = false;
    let mut heart_bt_int = 30u32;
    let mut reset = false;
    let mut test_req_id: &[u8] = b"";
    let mut begin_seq = 0u32;
    let mut end_seq = 0u32;
    let mut ref_seq = 0u32;
    let mut new_seq_no = 0u32;
    let mut gap_fill = false;

    for field in FieldReader::new(frame, 0) {
        match field.tag {
            35 => msg_type = Some(field.value.slice(frame)),
            34 => {
                seq = parse_fix_seqnum(field.value.slice(frame))
                    .ok()
                    .map(|s| s as u32)
            }
            49 => sender = field.value.slice(frame),
            56 => target = field.value.slice(frame),
            43 => poss_dup = parse_fix_bool(field.value.slice(frame)).unwrap_or(false),
            108 => heart_bt_int = parse_fix_uint(field.value.slice(frame)).unwrap_or(30),
            141 => reset = parse_fix_bool(field.value.slice(frame)).unwrap_or(false),
            112 => test_req_id = field.value.slice(frame),
            7 => {
                begin_seq = parse_fix_seqnum(field.value.slice(frame))
                    .ok()
                    .map_or(0, |s| s as u32)
            }
            16 => {
                end_seq = parse_fix_seqnum(field.value.slice(frame))
                    .ok()
                    .map_or(0, |s| s as u32)
            }
            45 => {
                ref_seq = parse_fix_seqnum(field.value.slice(frame))
                    .ok()
                    .map_or(0, |s| s as u32)
            }
            36 => {
                new_seq_no = parse_fix_seqnum(field.value.slice(frame))
                    .ok()
                    .map_or(0, |s| s as u32)
            }
            123 => gap_fill = parse_fix_bool(field.value.slice(frame)).unwrap_or(false),
            _ => {}
        }
    }

    Some(FrameHeader {
        sender,
        target,
        msg_type: msg_type?,
        seq: seq?,
        poss_dup,
        heart_bt_int,
        reset,
        test_req_id,
        begin_seq,
        end_seq,
        ref_seq,
        new_seq_no,
        gap_fill,
    })
}

fn is_timeout(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
    )
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
