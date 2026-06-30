use core::marker::PhantomData;
use std::io::Write;

use nexus_fix_codec::FixDictionary;
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
    /// Counterparty initiated a Logout. Send a Logout acknowledgement.
    LogoutRequest { msg: D::Logout<'buf> },
    /// Counterparty acknowledged our Logout. Session is done.
    LogoutAcknowledged { msg: D::Logout<'buf> },
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
pub struct MessageWriter<D: FixDictionary> {
    pub(crate) inner: FrameWriter,
    _dict: PhantomData<fn() -> D>,
}

impl<D: FixDictionary> MessageWriter<D> {
    pub fn new() -> Self {
        Self {
            inner: FrameWriter::builder().build(),
            _dict: PhantomData,
        }
    }

    pub fn with_frame_writer(inner: FrameWriter) -> Self {
        Self {
            inner,
            _dict: PhantomData,
        }
    }

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

    #[cfg(unix)]
    pub fn encode_admin(&mut self, admin: AdminMsg, config: &SessionConfig) {
        use nexus_fix_codec::AdminHeader;

        let ts = make_ts();
        let sender = config.sender.as_bytes();
        let target = config.target.as_bytes();
        let mk_hdr = |seq: u32| AdminHeader {
            seq,
            sender,
            target,
            ts: &ts,
        };

        let spare = self.inner.spare();
        let result = match admin {
            AdminMsg::Logon {
                seq,
                heart_bt_int_s,
            } => D::encode_logon(spare, mk_hdr(seq), heart_bt_int_s),
            AdminMsg::LogonReset {
                seq,
                heart_bt_int_s,
            } => D::encode_logon_reset(spare, mk_hdr(seq), heart_bt_int_s),
            AdminMsg::Logout { seq } => D::encode_logout(spare, mk_hdr(seq)),
            AdminMsg::Heartbeat { seq, echo } => {
                let echo_bytes = echo.as_ref().map(|(id, len)| &id[..*len as usize]);
                D::encode_heartbeat(spare, mk_hdr(seq), echo_bytes)
            }
            AdminMsg::TestRequest { seq, id } => D::encode_test_request(spare, mk_hdr(seq), id),
            AdminMsg::ResendRequest { seq, begin } => {
                D::encode_resend_request(spare, mk_hdr(seq), begin)
            }
            AdminMsg::SequenceReset { seq, new_seq } => {
                D::encode_sequence_reset(spare, mk_hdr(seq), new_seq)
            }
            AdminMsg::Reject {
                seq,
                ref_seq_num,
                ref_tag_id,
                session_reject_reason,
            } => D::encode_reject(
                spare,
                mk_hdr(seq),
                ref_seq_num,
                ref_tag_id,
                session_reject_reason,
            ),
        };

        if let Some((start, len)) = result {
            self.inner.commit(start, len);
        }
    }
}

impl<D: FixDictionary> Default for MessageWriter<D> {
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
