use core::marker::PhantomData;
use std::io::Write;

use nexus_fix_codec::{AsciiTextStr, FixDictionary, NoCustomizer, SessionCustomizer};
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

/// Typed inbound message returned by the receive surface.
///
/// The session is a **framework**: it surfaces what happened and the *one*
/// response each situation needs; the caller drives every reply with the send
/// helpers. Nothing is auto-answered on your behalf (the engine drives only its
/// own mechanism — the reset handshake and protocol-error disconnects).
///
/// Admin messages that carry data (`Heartbeat`, `Reject`, …) surface the
/// dictionary's zero-copy decoder so callers can read any field without
/// re-parsing; app messages surface the decoded header so the caller can route by
/// `MsgType` and decode the body independently. Every borrowed payload ties to the
/// `MessageReader` frame, never to `&mut session`, so the reply's `&mut session` /
/// `&mut writer` stay free while the payload is still borrowed.
pub enum Message<'r, D: FixDictionary> {
    /// Business message. Route by `header.raw_msg_type()` and decode the body.
    Application { header: D::Header<'r> },
    /// TestRequest (35=1). Answer with `heartbeat(&mut writer, &mut conn, now,
    /// Some(id))` — `id` is the borrowed `TestReqID(112)`, echoed verbatim.
    ///
    /// The `TestReqID` is a validated [`AsciiTextStr`]: the receive path checks tag
    /// 112 is **present and printable-ASCII** before this variant is produced (an
    /// absent or non-ASCII 112 surfaces as an `Err`, not a silently-empty echo), so
    /// the borrowed value is sound to read as text and re-encode.
    TestRequest {
        /// The validated `TestReqID(112)` to echo back, borrowed from the frame.
        id: &'r AsciiTextStr,
    },
    /// An inbound gap was detected. Answer with `resend_request(&mut writer, &mut
    /// conn, now, begin)`. The engine has entered `Resending`; a further gap in the
    /// same window is suppressed until recovery completes.
    GapDetected {
        /// First missing inbound seqnum — the `BeginSeqNo(7)` for the reply.
        begin: u32,
    },
    /// Counterparty initiated a Logon (acceptor role). Answer with
    /// `decision.accept(..)` or `decision.reject(..)` — the reply is yours to send,
    /// gated on your auth policy.
    LogonRequest(LogonDecision<'r, D>),
    /// Counterparty initiated a reset Logon (`ResetSeqNumFlag(141)=Y`). Answer with
    /// `decision.accept(..)` (sends a `LogonReset` reply) or `decision.reject(..)`.
    LogonResetRequest(LogonDecision<'r, D>),
    /// Counterparty initiated a Logout (35=5). Answer with `logout(&mut writer,
    /// &mut conn, now)` to send your Logout reply, then close the transport. (A
    /// Logout confirming *your* initiated logout surfaces as [`LoggedOut`](Self::LoggedOut)
    /// instead.)
    LogoutRequest { msg: D::Logout<'r> },
    /// Heartbeat (35=0). No reply required.
    Heartbeat { msg: D::Heartbeat<'r> },
    /// ResendRequest (35=2) whose requested range is fully within the journal's
    /// retained replay window. Pump the [`ResendCursor`] to replay it — each
    /// [`next`](ResendCursor::next) yields bytes to write; dropping it refuses the
    /// resend. The up-front providability check guarantees the cursor fulfills, so
    /// it never hits out-of-range mid-pump.
    ResendRequest {
        /// The retransmission cursor. `Copy`, so binding it carries no reader
        /// borrow: copy it out and pump `next(&mut session, &mut writer, now)`.
        cursor: ResendCursor,
    },
    /// ResendRequest (35=2) the journal can no longer fulfill — the requested range
    /// falls outside the retained replay window `[low_water, high_water]`. **No
    /// cursor**: the user decides. `begin < low_water` means the start rotated off;
    /// `end > high_water` means the peer asked for messages we never sent (desync).
    /// Answer with `sequence_reset(&mut writer, &mut conn, now, new_seq, gap_fill)`
    /// (GapFill or Reset mode), or log out.
    ResendOutOfRange {
        /// Requested `BeginSeqNo(7)`.
        begin: u32,
        /// Resolved `EndSeqNo(16)` (open-ended `0` clamped to `high_water`).
        end: u32,
        /// Oldest outbound seqnum still replayable (`next_outbound - window`).
        low_water: u32,
        /// Highest outbound seqnum ever sent (`next_outbound - 1`).
        high_water: u32,
    },
    /// SequenceReset (35=4). State updated internally; inspect if needed. No reply.
    SequenceReset { msg: D::SequenceReset<'r> },
    /// Reject (35=3). State updated internally; inspect if needed. No reply.
    Reject { msg: D::Reject<'r> },
    /// Counterparty acknowledged our Logon (initiator role). Session is live. No reply.
    LogonAcknowledged { msg: D::Logon<'r> },
    /// A clean, negotiated logout completed and the session ended — the graceful
    /// terminal event confirming *our* initiated logout. Carries the peer's Logout
    /// (35=5). An *abnormal* end never appears here: it surfaces as
    /// `Err(TransportError::UnexpectedDisconnect { reason })`.
    LoggedOut { msg: D::Logout<'r> },
}

/// A user-pumped cursor over a retransmission, surfaced inside
/// [`Message::ResendRequest`].
///
/// The engine hands one back only after an **up-front providability check**: the
/// requested `[begin, end]` lies fully within the journal's retained replay window
/// (`[low_water, high_water]`), so the cursor is *guaranteed* to fulfill — it never
/// hits an out-of-range mid-pump. A request outside the window surfaces as
/// [`Message::ResendOutOfRange`] instead, with no cursor.
///
/// # Pumping
///
/// The caller drives the replay one write at a time. `next` reframes the next
/// journalled item into the caller's `writer` — an app message as a PossDup replay
/// (`PossDupFlag(43)=Y`, `OrigSendingTime(122)` from the stored frame, a fresh
/// `SendingTime(52)` from `now`), or a run of admin holes / never-sent seqnums as
/// one `SequenceReset-GapFill` — and returns the reframed bytes. `Ok(None)` means
/// the whole range has drained (Done). The bytes borrow the writer, so **write each
/// yielded slice before the next call** — the next call reuses (overwrites) the
/// writer buffer.
///
/// ```ignore
/// Message::ResendRequest { cursor } => {
///     let mut c = cursor;                       // Copy — carries no reader borrow
///     while let Some(bytes) = c.next(&mut session, &mut writer, now)? {
///         conn.write_all(bytes)?;               // pace / bound / abort is yours
///     }
/// }
/// ```
///
/// # Sans-IO and `Copy`
///
/// The cursor performs no I/O — it yields bytes and the caller writes them, so the
/// same cursor drives sync (`write_all`) and async (`.await` the write). It holds
/// only three seqnums (`Copy`, no borrowed iterator): re-deriving
/// `journal.resend(pos, end)` each call is O(1) to locate a seqnum via the offset
/// table. Being `Copy`, it rides in the non-borrowing verdict from `poll` straight
/// into `message()` with no frame borrow, and — because `Copy` and `Drop` are
/// mutually exclusive — it has no destructor: **dropping it without pumping simply
/// refuses the resend** (nothing is sent). Pace, bound, or abort the replay in your
/// own loop; that is how you refuse an abusive multi-million-message demand instead
/// of parking your session thread.
///
/// The replay pump (`next` / `next_batch`) is defined on the unix-only
/// [`FixSession`](crate::FixSession) side, since it drives the journal; the state
/// here is platform-independent.
#[derive(Clone, Copy, Debug)]
pub struct ResendCursor {
    /// Requested `BeginSeqNo(7)` — retained for [`begin`](Self::begin)/logging.
    pub(crate) begin: u32,
    /// Resolved `EndSeqNo(16)` (open-ended `0` clamped to high-water) — the last
    /// seqnum to replay, inclusive.
    pub(crate) end: u32,
    /// Next outbound seqnum to replay; starts at `begin`, advances past each item
    /// (one past an app, to a gap-fill's `NewSeqNo`). `> end` means Done.
    pub(crate) pos: u32,
}

impl ResendCursor {
    /// Construct a cursor over the (already validated, providable) resolved range.
    pub(crate) fn new(begin: u32, end: u32) -> Self {
        Self {
            begin,
            end,
            pos: begin,
        }
    }

    /// The requested `BeginSeqNo(7)`.
    pub fn begin(&self) -> u32 {
        self.begin
    }

    /// The resolved `EndSeqNo(16)` (open-ended `0` clamped to the journal
    /// high-water at the time the request was classified).
    pub fn end(&self) -> u32 {
        self.end
    }
}

/// The binary-choice response object for a counterparty-initiated Logon.
///
/// Surfaced inside [`Message::LogonRequest`] / [`Message::LogonResetRequest`]. A
/// Logon has exactly one required response — accept it (send the reply, bring the
/// session up) or reject it (send a Logout, disconnect) — so it is a decision
/// object rather than a plain payload: the type makes "answer it" unavoidable.
///
/// It borrows only the reader frame (`'r`); [`accept`](Self::accept) /
/// [`reject`](Self::reject) take `&mut session` / `&mut writer` / `&mut conn`
/// separately, so the reply's mutable borrows stay disjoint from the borrowed
/// Logon fields ([`logon`](Self::logon)).
#[must_use = "a Logon must be accepted or rejected"]
pub struct LogonDecision<'r, D: FixDictionary> {
    pub(crate) msg: D::Logon<'r>,
    pub(crate) seq: u32,
    pub(crate) heart_bt_int_s: u32,
    pub(crate) is_reset: bool,
}

impl<'r, D: FixDictionary> LogonDecision<'r, D> {
    /// Reads the peer's Logon for the auth decision (`HeartBtInt`, `Username`,
    /// venue fields, …) — the zero-copy decoder, borrowing the frame.
    pub fn logon(&self) -> &D::Logon<'r> {
        &self.msg
    }
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

    /// Spare region of the inbound buffer for the caller to read transport bytes
    /// into. Commit the number actually read with [`filled`](Self::filled). This
    /// is the inbound half of the sans-IO byte seam: a custom transport fills
    /// `spare()`, commits with `filled(n)`, then drives
    /// [`FixSession::poll`](crate::FixSession::poll).
    ///
    /// Compacts on the usual `should_compact()` threshold, but *also* whenever the
    /// buffer is full (`remaining() == 0`) even below that threshold. Without the
    /// full-buffer case a buffer that is full but <50% consumed would return an
    /// empty spare slice; a wrapper's `stream.read(&mut [])` then returns `Ok(0)`
    /// and is misread as EOF/disconnect. Compacting reclaims all consumed space, so
    /// the spare is non-empty whenever there is anything to reclaim. If nothing is
    /// reclaimable (a single incomplete frame already fills the whole buffer) the
    /// spare stays empty, and the caller turns that into a "message too large"
    /// condition rather than reading into a zero-length slice.
    pub fn spare(&mut self) -> &mut [u8] {
        if self.inner.should_compact() || self.inner.remaining() == 0 {
            self.inner.compact();
        }
        self.inner.spare()
    }

    /// Commit `n` bytes read into [`spare`](Self::spare).
    pub fn filled(&mut self, n: usize) {
        self.inner.filled(n);
    }

    /// Inbound buffer capacity in bytes (fixed at construction).
    ///
    /// The largest single frame the reader can buffer. A wrapper reports this as
    /// the "message too large" size when [`spare`](Self::spare) returns an empty
    /// slice — the buffer is full with one incomplete frame that cannot grow.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }
}

impl<D: FixDictionary> Default for MessageReader<D> {
    fn default() -> Self {
        Self::new()
    }
}

/// Lets a [`nexus_net::WireStream`] transport fill the reader's inbound buffer
/// directly (`poll_fill_into(&mut reader, …)`), skipping the intermediate
/// `&mut [u8]` copy. Forwards to the inherent [`spare`](MessageReader::spare) /
/// [`filled`](MessageReader::filled) so the compaction contract holds on both
/// paths.
impl<D: FixDictionary> ParserSink for MessageReader<D> {
    fn spare(&mut self) -> &mut [u8] {
        MessageReader::spare(self)
    }

    fn filled(&mut self, n: usize) {
        MessageReader::filled(self, n);
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
    /// `SendingTime(52)` stamped into every frame this emitter produces, formatted
    /// once from the caller-supplied `now`. There is no internal clock read: the
    /// core is a pure function of `(bytes, now)`.
    ts: [u8; crate::timestamp::UTC_TIMESTAMP_LEN],
    after: J,
}

#[cfg(unix)]
impl<'a, D: FixDictionary, C: SessionCustomizer, J> Emitter<'a, D, C, J>
where
    J: FnMut(u32, &[u8]) -> Result<(), Error>,
{
    /// Build an emitter over `writer`, stamping headers from `config` and running
    /// `after(seq, frame)` on every committed frame.
    ///
    /// `now` is a UTC wall-clock timestamp in nanoseconds since the Unix epoch; it
    /// is formatted once into the `SendingTime(52)` every emitted frame carries.
    /// The emitter reads no clock of its own — every stamp comes from this `now`.
    pub fn new(
        writer: &'a mut MessageWriter<D, C>,
        config: &'a SessionConfig,
        now: i128,
        after: J,
    ) -> Self {
        let mut ts = [0u8; crate::timestamp::UTC_TIMESTAMP_LEN];
        crate::timestamp::format_utc_timestamp(now, &mut ts);
        Self {
            writer,
            config,
            ts,
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

        let hdr = AdminHeader {
            seq: msg.seq(),
            sender: self.config.sender.as_bytes(),
            target: self.config.target.as_bytes(),
            ts: &self.ts,
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
