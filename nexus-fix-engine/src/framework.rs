use core::marker::PhantomData;
use std::io::Write;

use nexus_fix_codec::{FixDictionary, NoCustomizer, SessionCustomizer};
use nexus_net::wire::ParserSink;

use crate::frame::{FrameReader, FrameWriter};
#[cfg(unix)]
use crate::session::AdminMsg;

const COMP_ID_CAP: usize = 20;

#[derive(Clone, Copy, Debug)]
pub struct CompId {
    bytes: [u8; COMP_ID_CAP],
    len: u8,
}

impl CompId {
    pub fn new(s: &[u8]) -> Option<Self> {
        if s.len() > COMP_ID_CAP {
            return None;
        }
        let mut bytes = [0u8; COMP_ID_CAP];
        bytes[..s.len()].copy_from_slice(s);
        Some(Self {
            bytes,
            len: s.len() as u8,
        })
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.len as usize]
    }
}

/// Session configuration: CompID pair used for inbound header validation.
#[derive(Clone, Copy, Debug)]
pub struct SessionConfig {
    /// Our own SenderCompID — must match incoming TargetCompID (tag 56).
    pub sender: CompId,
    /// Counterparty SenderCompID — must match incoming SenderCompID (tag 49).
    pub target: CompId,
}

/// Error returned by the framework layer when decoding fails.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SessionError {
    /// Tag 35 (MsgType) absent.
    MissingMsgType,
    /// Tag 34 (MsgSeqNum) absent.
    MissingMsgSeqNum,
    /// A required field for this message type is absent.
    MissingField { tag: u32 },
    /// A field is present but fails to parse.
    MalformedField { tag: u32 },
    /// Admin message decoder failed.
    MalformedMessage,
    /// Outbound sequence number reached i32::MAX; caller must force a sequence reset.
    SeqNumExhausted,
    /// An in-session reset is already in progress; outbound allocation is blocked.
    ResetInProgress,
    /// Operation not valid in the current session state.
    InvalidState,
}

impl core::fmt::Display for SessionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::MissingMsgType => write!(f, "tag 35 (MsgType) missing"),
            Self::MissingMsgSeqNum => write!(f, "tag 34 (MsgSeqNum) missing"),
            Self::MissingField { tag } => write!(f, "required tag {tag} missing"),
            Self::MalformedField { tag } => write!(f, "tag {tag} malformed"),
            Self::MalformedMessage => write!(f, "admin message malformed"),
            Self::SeqNumExhausted => write!(f, "outbound sequence number exhausted (i32::MAX)"),
            Self::ResetInProgress => write!(f, "in-session reset in progress"),
            Self::InvalidState => write!(f, "operation not valid in current session state"),
        }
    }
}

impl core::error::Error for SessionError {}

/// Typed inbound message returned by the transport layer.
///
/// Admin messages carry the dictionary's zero-copy decoder for the message type
/// so callers can read any field — protocol-required or venue-specific — without
/// re-parsing. App messages surface the decoded header so the caller can route
/// by `MsgType` and decode the body independently.
pub enum Message<'buf, D: FixDictionary> {
    /// Counterparty initiated a Logon (acceptor role). Send your own Logon back.
    LogonRequest { msg: D::Logon<'buf> },
    /// Counterparty acknowledged our Logon (initiator role). Session is live.
    LogonAcknowledged { msg: D::Logon<'buf> },
    /// A Logout (35=5) that did not end the session, which only happens
    /// out-of-state (e.g. mid-reset). The engine answers and closes an
    /// in-sequence logout itself; that surfaces as
    /// [`Message::Disconnected`] with [`DisconnectReason::Logout`].
    LogoutRequest { msg: D::Logout<'buf> },
    /// Heartbeat (35=0). No reply required unless it carries a TestReqID.
    Heartbeat { msg: D::Heartbeat<'buf> },
    /// TestRequest (35=1). Echo the `TestReqID` in a Heartbeat reply.
    TestRequest { msg: D::TestRequest<'buf> },
    /// ResendRequest (35=2). Re-send or gap-fill the requested range.
    ResendRequest { msg: D::ResendRequest<'buf> },
    /// SequenceReset (35=4). State updated internally; inspect if needed.
    SequenceReset { msg: D::SequenceReset<'buf> },
    /// Reject (35=3). State updated internally; inspect if needed.
    Reject { msg: D::Reject<'buf> },
    /// Business message. Route by `header.raw_msg_type()` and decode the body.
    Application { header: D::Header<'buf> },
    /// Session disconnected (CompID mismatch, timeout, or protocol violation).
    Disconnected { reason: crate::DisconnectReason },
}

/// Zero-copy FIX frame reader, dictionary-aware via `D::Header`.
pub struct MessageReader<D: FixDictionary> {
    pub(crate) inner: FrameReader,
    pub(crate) frame: Vec<u8>,
    _dict: PhantomData<fn() -> D>,
}

impl<D: FixDictionary> MessageReader<D> {
    pub fn new() -> Self {
        Self {
            inner: FrameReader::builder().build(),
            frame: Vec::new(),
            _dict: PhantomData,
        }
    }

    pub fn with_frame_reader(inner: FrameReader) -> Self {
        Self {
            inner,
            frame: Vec::new(),
            _dict: PhantomData,
        }
    }
}

impl<D: FixDictionary> Default for MessageReader<D> {
    fn default() -> Self {
        Self::new()
    }
}

impl<D: FixDictionary> ParserSink for MessageReader<D> {
    fn spare(&mut self) -> &mut [u8] {
        self.inner.spare()
    }

    fn filled(&mut self, n: usize) {
        self.inner.filled(n);
    }
}

/// Outbound FIX message writer, dictionary-aware via `D::BEGIN_STRING`.
///
/// `C` is the per-venue [`SessionCustomizer`](nexus_fix_codec::SessionCustomizer)
/// run over each outbound admin message; it defaults to
/// [`NoCustomizer`], so plain-FIX callers write `MessageWriter<Fix44>`.
pub struct MessageWriter<D: FixDictionary, C = NoCustomizer> {
    pub(crate) inner: FrameWriter,
    /// Only read by `encode_admin`, which is `#[cfg(unix)]` — so on other
    /// platforms this field is genuinely dead rather than accidentally unused.
    #[cfg_attr(not(unix), allow(dead_code))]
    customizer: C,
    _dict: PhantomData<fn() -> D>,
}

impl<D: FixDictionary> MessageWriter<D, NoCustomizer> {
    pub fn new() -> Self {
        Self::with_customizer(NoCustomizer)
    }

    pub fn with_frame_writer(inner: FrameWriter) -> Self {
        Self::with_frame_writer_and_customizer(inner, NoCustomizer)
    }
}

// The customizer bound sits on the constructors, not the struct, so a type that
// is not a `SessionCustomizer` is rejected where it is supplied rather than
// later at `encode_admin`.
impl<D: FixDictionary, C: SessionCustomizer> MessageWriter<D, C> {
    /// Builds a writer with default buffers and a per-venue customizer.
    pub fn with_customizer(customizer: C) -> Self {
        Self {
            inner: FrameWriter::builder().build(),
            customizer,
            _dict: PhantomData,
        }
    }

    /// Builds a writer from a pre-sized frame writer and a per-venue customizer.
    pub fn with_frame_writer_and_customizer(inner: FrameWriter, customizer: C) -> Self {
        Self {
            inner,
            customizer,
            _dict: PhantomData,
        }
    }
}

impl<D: FixDictionary, C> MessageWriter<D, C> {
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn data(&self) -> &[u8] {
        self.inner.data()
    }

    pub fn advance(&mut self, n: usize) {
        self.inner.advance(n);
    }

    pub fn remaining(&self) -> usize {
        self.inner.remaining()
    }

    /// Total buffer capacity in bytes (fixed at construction).
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    pub fn flush_to<S: Write>(&mut self, stream: &mut S) -> std::io::Result<()> {
        while !self.inner.is_empty() {
            let n = stream.write(self.inner.data())?;
            if n == 0 {
                return Err(std::io::Error::other("write returned 0"));
            }
            self.inner.advance(n);
        }
        stream.flush()
    }
}

impl<D: FixDictionary, C: SessionCustomizer> MessageWriter<D, C> {
    /// Encodes one admin message into the outbound buffer.
    ///
    /// Owns the frame lifecycle so the customizer hook can run at the one point
    /// where it is useful: after the session header (`8`/`35`/`34`/`49`/`56`/`52`)
    /// is stamped — so a venue can sign over it — and before
    /// [`FrameFormatter::finish`] computes `BodyLength(9)`/`CheckSum(10)` — so
    /// whatever the hook appended is covered by both.
    #[cfg(unix)]
    pub fn encode_admin(&mut self, admin: AdminMsg, config: &SessionConfig) {
        use nexus_fix_codec::{AdminHeader, AdminMsgOut, FrameFormatter};

        let ts = make_ts();
        let sender = config.sender.as_bytes();
        let target = config.target.as_bytes();
        let mk_hdr = |seq: u32| AdminHeader {
            seq,
            sender,
            target,
            ts: &ts,
        };

        let customizer = &self.customizer;
        let spare = self.inner.spare();

        // Each arm: start the frame, write the dictionary's standard fields,
        // run the venue hook, then finish. `hdr` outlives the borrow in
        // `AdminMsgOut`, so it is bound before the formatter.
        let result = match admin {
            AdminMsg::Logon {
                seq,
                heart_bt_int_s,
            } => {
                let hdr = mk_hdr(seq);
                let mut fmt = FrameFormatter::new(spare, D::BEGIN_STRING, b"A");
                D::encode_logon(&mut fmt, &hdr, heart_bt_int_s);
                customizer.configure_logon(&mut AdminMsgOut::new(&mut fmt, &hdr, b"A"));
                fmt.finish().ok()
            }
            AdminMsg::LogonReset {
                seq,
                heart_bt_int_s,
            } => {
                let hdr = mk_hdr(seq);
                let mut fmt = FrameFormatter::new(spare, D::BEGIN_STRING, b"A");
                D::encode_logon_reset(&mut fmt, &hdr, heart_bt_int_s);
                customizer.configure_logon_reset(&mut AdminMsgOut::new(&mut fmt, &hdr, b"A"));
                fmt.finish().ok()
            }
            AdminMsg::Logout { seq } => {
                let hdr = mk_hdr(seq);
                let mut fmt = FrameFormatter::new(spare, D::BEGIN_STRING, b"5");
                D::encode_logout(&mut fmt, &hdr);
                customizer.configure_logout(&mut AdminMsgOut::new(&mut fmt, &hdr, b"5"));
                fmt.finish().ok()
            }
            AdminMsg::Heartbeat { seq, echo } => {
                let hdr = mk_hdr(seq);
                let echo_bytes = echo.as_ref().map(|(id, len)| &id[..*len as usize]);
                let mut fmt = FrameFormatter::new(spare, D::BEGIN_STRING, b"0");
                D::encode_heartbeat(&mut fmt, &hdr, echo_bytes);
                customizer.configure_heartbeat(&mut AdminMsgOut::new(&mut fmt, &hdr, b"0"));
                fmt.finish().ok()
            }
            AdminMsg::TestRequest { seq, id } => {
                let hdr = mk_hdr(seq);
                let mut fmt = FrameFormatter::new(spare, D::BEGIN_STRING, b"1");
                D::encode_test_request(&mut fmt, &hdr, id);
                customizer.configure_test_request(&mut AdminMsgOut::new(&mut fmt, &hdr, b"1"));
                fmt.finish().ok()
            }
            AdminMsg::ResendRequest { seq, begin } => {
                let hdr = mk_hdr(seq);
                let mut fmt = FrameFormatter::new(spare, D::BEGIN_STRING, b"2");
                D::encode_resend_request(&mut fmt, &hdr, begin);
                customizer.configure_resend_request(&mut AdminMsgOut::new(&mut fmt, &hdr, b"2"));
                fmt.finish().ok()
            }
            AdminMsg::SequenceReset { seq, new_seq } => {
                let hdr = mk_hdr(seq);
                let mut fmt = FrameFormatter::new(spare, D::BEGIN_STRING, b"4");
                D::encode_sequence_reset(&mut fmt, &hdr, new_seq);
                customizer.configure_sequence_reset(&mut AdminMsgOut::new(&mut fmt, &hdr, b"4"));
                fmt.finish().ok()
            }
            AdminMsg::Reject {
                seq,
                ref_seq_num,
                ref_tag_id,
                session_reject_reason,
            } => {
                let hdr = mk_hdr(seq);
                let mut fmt = FrameFormatter::new(spare, D::BEGIN_STRING, b"3");
                D::encode_reject(
                    &mut fmt,
                    &hdr,
                    ref_seq_num,
                    ref_tag_id,
                    session_reject_reason,
                );
                customizer.configure_reject(&mut AdminMsgOut::new(&mut fmt, &hdr, b"3"));
                fmt.finish().ok()
            }
        };

        if let Some((start, len)) = result {
            self.inner.commit(start, len);
        }
    }
}

impl<D: FixDictionary> Default for MessageWriter<D, NoCustomizer> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(unix)]
fn make_ts() -> [u8; crate::timestamp::UTC_TIMESTAMP_LEN] {
    use std::time::{SystemTime, UNIX_EPOCH};

    let unix_nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos() as i128;
    let mut ts = [0u8; crate::timestamp::UTC_TIMESTAMP_LEN];
    crate::timestamp::format_utc_timestamp(unix_nanos, &mut ts);
    ts
}
