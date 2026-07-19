use core::marker::PhantomData;
use std::io::Write;

use nexus_fix_codec::{FixDictionary, NoCustomizer, SessionCustomizer};
use nexus_net::wire::ParserSink;

#[cfg(unix)]
use nexus_fix_codec::AdminEncode;

#[cfg(unix)]
use crate::fix_session::Error;
use crate::frame::{FrameReader, FrameWriter};
#[cfg(unix)]
use crate::session::Emit;

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
    /// [`Message::Disconnected`] with [`DisconnectReason::Logout`](crate::DisconnectReason::Logout).
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
    /// A malformed frame was discarded to resync to the next `8=` boundary:
    /// garbled bytes, a bad `BodyLength(9)`, or a failed `CheckSum(10)` (see
    /// [`reason`](crate::MalformedReason)). This is **not** a disconnect — per
    /// FIX's optimistic recovery the session continues and the inbound seqnum
    /// is left unchanged. `skipped` is the bytes discarded to resync; `count`
    /// is the running total of malformed frames this session. The caller owns
    /// the policy: log it, alert on it, or disconnect on a sustained flood.
    Malformed {
        skipped: usize,
        count: u64,
        reason: crate::MalformedReason,
    },
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
    /// Only read by [`Emitter`], which is `#[cfg(unix)]` — so on other platforms
    /// this field is genuinely dead rather than accidentally unused.
    #[cfg_attr(not(unix), allow(dead_code))]
    pub(crate) customizer: C,
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
// later at the `Emitter`.
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

/// Encodes admin messages into a [`MessageWriter`] and runs an injected `after`
/// hook on each committed frame — the emit seam's production [`Emit`] impl.
///
/// The concrete admin type is never erased: [`emit`](Emit::emit) is generic
/// over [`AdminEncode`], so a `ResendRequest` stays a `ResendRequest` through
/// encode, customize, and journal.
///
/// The `after` closure is the journaling policy, chosen per emit context by the
/// driver: [`FixSession`](crate::FixSession) passes a closure that journals the
/// frame under its seqnum for most admin, and a no-op closure for the encode-only
/// missing-tag-35 reject. Keeping it a closure (rather than a second [`Emit`] impl)
/// leaves the policy the driver's to pick while the encode path stays
/// single-sourced here.
#[cfg(unix)]
pub struct Emitter<'a, D: FixDictionary, C, J> {
    writer: &'a mut MessageWriter<D, C>,
    config: &'a SessionConfig,
    after: J,
}

#[cfg(unix)]
impl<'a, D: FixDictionary, C: SessionCustomizer, J> Emitter<'a, D, C, J>
where
    J: FnMut(u32, &[u8]) -> Result<(), Error>,
{
    /// Build an emitter over `writer`, stamping headers from `config` and running
    /// `after(seq, frame)` on every committed frame.
    pub fn new(writer: &'a mut MessageWriter<D, C>, config: &'a SessionConfig, after: J) -> Self {
        Self {
            writer,
            config,
            after,
        }
    }
}

#[cfg(unix)]
impl<D: FixDictionary, C: SessionCustomizer, J> Emit for Emitter<'_, D, C, J>
where
    J: FnMut(u32, &[u8]) -> Result<(), Error>,
{
    type Error = Error;

    /// Encode `msg` into the writer, commit it, then run the `after` hook.
    ///
    /// Owns the frame lifecycle so the [`SessionCustomizer`] hook runs at the one
    /// point where it is useful: after the session header
    /// (`8`/`35`/`34`/`49`/`56`/`52`) is stamped — so a venue can sign over it —
    /// and before [`FrameFormatter::finish`](nexus_fix_codec::FrameFormatter::finish)
    /// computes `BodyLength(9)`/`CheckSum(10)` — so whatever the hook appended is
    /// covered by both. The single `M::MSG_TYPE` passed to both
    /// [`FrameFormatter::new`](nexus_fix_codec::FrameFormatter::new) and
    /// `AdminMsgOut::new` is the value written into the frame and the one the hook
    /// reads back, so what a venue signs over cannot drift from the wire; the
    /// tripwire's owned-tag list is `M::owned::<D>()`, sourced from the dictionary
    /// next to the encoder that writes it.
    ///
    /// The frame handed to `after` is the committed bytes including anything the
    /// hook injected, so a journaling `after` archives the wire byte-for-byte.
    ///
    /// # Errors
    ///
    /// [`Error::MessageTooLarge`] if the message did not fit the writer's spare
    /// capacity — most plausibly because a hook appended more than fits (an
    /// oversized `RawData(96)`, say), the one unbounded input on this path.
    /// Nothing is committed or journaled on failure, so a too-large message never
    /// reaches the wire half-written; the outbound seqnum's owner learns the
    /// encode failed instead of the session silently wedging.
    fn emit<M: AdminEncode>(&mut self, msg: M) -> Result<(), Error> {
        use nexus_fix_codec::{AdminHeader, AdminMsgOut, FrameFormatter};

        let ts = make_ts();
        let hdr = AdminHeader {
            seq: msg.seq(),
            sender: self.config.sender.as_bytes(),
            target: self.config.target.as_bytes(),
            ts: &ts,
        };

        // Offset of this frame within the (possibly non-empty) outbound buffer,
        // captured before the encode so `after` sees exactly the new frame.
        let before = self.writer.inner.data().len();
        // Captured before the spare borrow. A poisoned frame cannot report how
        // many bytes it needed — the overflowing writes were dropped, not counted
        // — so report the smallest size that certainly did not fit: the spare it
        // was offered, plus one. Same convention as the resend guard in
        // `fix_session`.
        let needed = self.writer.inner.remaining().saturating_add(1);

        // Disjoint field borrows: `&mut self.writer.customizer` and
        // `self.writer.inner.spare()` (also `&mut`) are different fields of
        // `*self.writer`, so both `&mut` borrows stay live while the formatter
        // holds the spare. The `&mut` on the customizer lets a venue hook carry
        // mutable auth state (a per-logon nonce, a rotating key).
        let customizer = &mut self.writer.customizer;
        let spare = self.writer.inner.spare();
        let mut fmt = FrameFormatter::new(spare, D::BEGIN_STRING, M::MSG_TYPE);
        msg.encode::<D>(&mut fmt, &hdr);
        msg.customize(
            customizer,
            &mut AdminMsgOut::new(&mut fmt, &hdr, M::MSG_TYPE, M::owned::<D>()),
        );
        match fmt.finish() {
            Ok((start, len)) => self.writer.inner.commit(start, len),
            // `FrameFormatter::finish` fails only with `BufferFull`; the frame was
            // built into `spare` and never committed, so the buffer still holds
            // exactly what it held before this call.
            Err(_) => return Err(Error::MessageTooLarge(needed)),
        }

        (self.after)(msg.seq(), &self.writer.inner.data()[before..])
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
