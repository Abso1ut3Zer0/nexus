//! Sans-IO FIX session core.
//!
//! [`FixSession`] is the sans-IO *brain*: the [`SessionState`] machine, the
//! [`FixJournal`], the [`SessionConfig`], and the resumable resend cursor. It owns
//! no buffers and no socket. The caller holds the [`FixParts`] trio — the session
//! plus a [`MessageReader`] (inbound bytes) and a [`MessageWriter`] (outbound
//! bytes) — and passes the reader/writer and its transport per call.
//!
//! # Sans-IO byte seam (custom transports)
//!
//! A caller with any transport (blocking sockets, kernel bypass, io_uring) drives
//! the whole machine without [`recv`](FixSession::recv) or any `Read`/`Write`
//! bound:
//!
//! - inbound: read transport bytes into [`reader.spare()`](MessageReader::spare),
//!   commit with [`reader.filled(n)`](MessageReader::filled),
//! - advance: [`session.poll(&mut reader, &mut writer, now)`](FixSession::poll),
//! - decode: [`session.message(&reader)`](FixSession::message) after
//!   [`PollOutcome::Message`],
//! - send: the encode-only helpers ([`encode_connect`](FixSession::encode_connect),
//!   [`encode_send_app`](FixSession::encode_send_app), …) stage bytes into `writer`,
//! - outbound: drain [`writer.data()`](MessageWriter::data) and commit with
//!   [`writer.advance(n)`](MessageWriter::advance).
//!
//! [`recv`](FixSession::recv) is a thin convenience over this seam for `Read +
//! Write` transports; the async twin (`nexus_async_fix_engine::FixSession::recv`)
//! is the same convenience for a [`nexus_net::WireStream`].
//!
//! # The poll/message split
//!
//! Returning a borrowed [`Message`] directly from a loop that also reads more
//! bytes hits the borrow checker (the classic NLL conditional-borrow wall). So
//! [`poll`](FixSession::poll) returns a *non-borrowing* [`PollOutcome`] after
//! processing one frame into a stable buffer (`reader.frame`), and
//! [`message`](FixSession::message) borrows that stable buffer to reconstruct the
//! typed [`Message`]. The `Message` borrows the *reader*, never `&mut self`, so
//! `&mut session` and `&mut writer` stay free for the reply while the payload is
//! still borrowed.

use core::marker::PhantomData;
use std::io::{self, Read, Write};

use nexus_fix_codec::{
    AsciiTextStr, FieldReader, FieldView, FixAdminMsg, FixDictionary, FixHeader, FrameFormatter,
    NoCustomizer, SessionCustomizer, encode_fix_uint, find_tag, parse_fix_bool, parse_fix_seqnum,
    parse_fix_uint,
};
use nexus_journal::WriteError;

use crate::frame::{FrameError, FrameReader, FrameWriter, MalformedReason};
use crate::framework::{
    Emitter, LogonDecision, Message, MessageReader, MessageWriter, ResendCursor, SessionConfig,
    SessionError,
};
use crate::persist::{FixJournal, ReplayItem};
use crate::session::{
    AppIn, Control, DisconnectReason, HeartbeatIn, LogonIn, LogoutIn, RejectIn, RejectInboundIn,
    ResendRequestIn, SequenceResetIn, SessionState, State, TestRequestIn,
};
use crate::timestamp::UTC_TIMESTAMP_LEN;

/// Error surfaced by the session.
///
/// The pure sans-IO seam ([`poll`](FixSession::poll) and the encode-only send
/// helpers) never performs I/O, so it never produces [`Error::Io`]. The `Io`
/// variant is produced only by the transport conveniences
/// ([`recv`](FixSession::recv) and the async twin), which read/write the socket.
#[derive(Debug)]
pub enum Error {
    /// A malformed inbound frame was discarded to resync to the next `8=`
    /// boundary: garbled bytes, a bad `BodyLength(9)`, or a failed `CheckSum(10)`
    /// (see `reason`). **Recoverable** — the reader has resynced and the session
    /// is intact, so this is the only non-fatal variant (see
    /// [`is_fatal`](Self::is_fatal)); a strict caller that does `recv()?` tears
    /// down, a tolerant one matches and keeps receiving. `skipped` is the bytes
    /// discarded to resync; `count` is the running total this session. Per FIX's
    /// optimistic recovery the inbound seqnum is left unchanged. The caller owns
    /// the policy: tolerate it, or tear down on a sustained flood.
    Malformed {
        skipped: usize,
        count: u64,
        reason: MalformedReason,
    },
    /// The session was dropped abnormally (see `reason`) — a fault, distinct from
    /// a clean logout (which surfaces as [`Message::LoggedOut`] on the `Ok` side).
    /// Terminal.
    UnexpectedDisconnect { reason: DisconnectReason },
    /// `recv` was called after the session already ended — a prior call already
    /// returned `Message::LoggedOut` or a terminal error. A caller bug: the
    /// session is gone. Terminal.
    Closed,
    /// A socket-level I/O failure. Terminal.
    Io(std::io::Error),
    /// An inbound frame exceeded the reader buffer or the configured maximum — a
    /// provisioning or protocol mismatch the session cannot continue past. Terminal.
    MessageTooLarge(usize),
    /// A session-layer protocol error. Terminal.
    Protocol(SessionError),
}

impl Error {
    /// Whether this error ends the session. Every variant is terminal except
    /// [`Malformed`](Self::Malformed), which is recoverable — the reader has
    /// resynced and receiving can continue.
    pub fn is_fatal(&self) -> bool {
        !matches!(self, Self::Malformed { .. })
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed {
                skipped, reason, ..
            } => write!(f, "malformed frame: discarded {skipped} bytes ({reason})"),
            Self::UnexpectedDisconnect { reason } => {
                write!(f, "unexpected disconnect: {reason:?}")
            }
            Self::Closed => f.write_str("recv on a closed session"),
            Self::Io(e) => write!(f, "I/O: {e}"),
            Self::MessageTooLarge(n) => write!(f, "message too large: {n} bytes"),
            Self::Protocol(e) => write!(f, "protocol: {e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<SessionError> for Error {
    fn from(e: SessionError) -> Self {
        Self::Protocol(e)
    }
}

/// Bytes reserved per app message for a later resend reframe.
///
/// A reframe adds `PossDupFlag` (`43=Y`), `OrigSendingTime` (`122=<UTC
/// timestamp>`), and a little `BodyLength` digit growth. [`FixSession::encode_send_app`]
/// keeps app frames this far below the writer capacity so a stored message always
/// reframes back into the pre-allocated buffer — no runtime allocation on the
/// resend path.
///
/// Exposed so callers sizing a writer via `writer_capacity(...)` know the
/// per-message reserve: the largest app frame they can send is
/// `writer_capacity - REFRAME_HEADROOM`.
pub const REFRAME_HEADROOM: usize = 64;

/// Non-borrowing result of [`FixSession::poll`].
///
/// A separate [`FixSession::message`] borrows the stable frame buffer to build
/// the typed [`Message`] once [`PollOutcome::Message`] is returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PollOutcome {
    /// A typed message is ready. Call [`FixSession::message`] to borrow it.
    Message,
    /// No complete frame is buffered. The caller must read more bytes into
    /// [`reader.spare()`](MessageReader::spare) and commit with
    /// [`reader.filled(n)`](MessageReader::filled), then poll again.
    NeedMoreBytes,
    /// The frame was processed but there is nothing to surface to the application
    /// (an out-of-sequence app suppressed pending resend, or a session-level
    /// reject was emitted). The wrapper should surface this as `Ok(None)`.
    Suppressed,
    /// A clean, negotiated logout ended the session. The wrapper surfaces
    /// `Message::LoggedOut`.
    LoggedOut,
    /// The session was dropped abnormally. The wrapper surfaces
    /// `Err(TransportError::UnexpectedDisconnect { reason })`.
    Disconnected(DisconnectReason),
}

/// Sans-IO FIX session: the state machine + journal *brain*. No buffers, no
/// socket.
///
/// The caller holds the [`FixParts`] trio — this session plus a
/// [`MessageReader`] and a [`MessageWriter`] — and passes the reader/writer per
/// call. See the [module docs](self) for the byte seam and the poll/message
/// split. Build one with [`FixSession::builder`] (returns [`FixParts`]) or
/// [`FixSession::new`] plus hand-built buffers.
///
/// A resend is *not* driven here: an inbound ResendRequest surfaces a
/// [`ResendCursor`] (or a [`Message::ResendOutOfRange`]) the caller pumps, so the
/// session holds no in-progress resend state.
pub struct FixSession<D: FixDictionary> {
    state: SessionState,
    journal: FixJournal,
    config: SessionConfig,
    garbage_frames: u64,
    /// The verdict the state machine last returned. [`message`](Self::message)
    /// reconstructs the borrowed [`Message`] from it after a
    /// [`PollOutcome::Message`]; see [`Control`].
    pending: Control,
    /// Set once [`recv`](Self::recv) surfaced a terminal outcome (a clean logout
    /// or a fatal error). A subsequent `recv` returns [`Error::Closed`].
    terminated: bool,
    _dict: PhantomData<fn() -> D>,
}

/// The persistent trio a caller holds.
///
/// The sans-IO [`FixSession`] brain plus its [`MessageReader`] (inbound bytes) and
/// [`MessageWriter`] (outbound bytes + venue customizer). Produced by
/// [`FixSessionBuilder::build`]; the transport is separate and passed per call, so
/// reconnect is "same trio, new socket."
pub struct FixParts<D: FixDictionary, C = NoCustomizer> {
    pub session: FixSession<D>,
    pub reader: MessageReader<D>,
    pub writer: MessageWriter<D, C>,
}

/// Builds a [`FixParts`] trio.
///
/// Sizes the reader/writer buffers and attaches an optional per-venue
/// [`SessionCustomizer`]. The socket is the caller's to open (transport policy is
/// not the session's concern).
///
/// `C` is the customizer type, defaulting to [`NoCustomizer`]; attach one with
/// [`customizer`](Self::customizer), which changes the resulting
/// [`MessageWriter`]'s `C`.
pub struct FixSessionBuilder<D: FixDictionary, C = NoCustomizer> {
    reader_cap: usize,
    writer_cap: usize,
    customizer: C,
    _dict: PhantomData<fn() -> D>,
}

impl<D: FixDictionary, C> FixSessionBuilder<D, C> {
    /// Inbound reader buffer capacity in bytes (largest single frame; default 64 KiB).
    pub fn reader_capacity(mut self, n: usize) -> Self {
        self.reader_cap = n;
        self
    }

    /// Outbound writer buffer capacity in bytes (default 64 KiB). The largest app
    /// frame you can [`send_app`](FixSession::encode_send_app) is `writer_capacity` minus
    /// [`REFRAME_HEADROOM`].
    pub fn writer_capacity(mut self, n: usize) -> Self {
        self.writer_cap = n;
        self
    }

    /// Attach a per-venue [`SessionCustomizer`] — the hook that injects Logon auth
    /// (e.g. `Username(553)`/`Password(554)`/`RawData(96)`). Changes the resulting
    /// [`MessageWriter`]'s customizer type to `C2`.
    pub fn customizer<C2: SessionCustomizer>(self, customizer: C2) -> FixSessionBuilder<D, C2> {
        FixSessionBuilder {
            reader_cap: self.reader_cap,
            writer_cap: self.writer_cap,
            customizer,
            _dict: PhantomData,
        }
    }
}

impl<D: FixDictionary, C: SessionCustomizer> FixSessionBuilder<D, C> {
    /// Builds the [`FixParts`] trio from the configured capacities/customizer plus
    /// the session's `state`, `config`, and `journal`. The socket is opened
    /// separately and passed per call.
    pub fn build(
        self,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> FixParts<D, C> {
        FixParts {
            session: FixSession::new(state, config, journal),
            reader: MessageReader::with_frame_reader(
                FrameReader::builder()
                    .buffer_capacity(self.reader_cap)
                    .build(),
            ),
            writer: MessageWriter::with_frame_writer_and_customizer(
                FrameWriter::builder()
                    .buffer_capacity(self.writer_cap)
                    .build(),
                self.customizer,
            ),
        }
    }
}

impl<D: FixDictionary> FixSession<D> {
    /// Builds a session *brain* with no buffers. Pair it with a hand-built
    /// [`MessageReader`] and [`MessageWriter`], or prefer
    /// [`builder`](Self::builder) to size them and get a [`FixParts`] trio.
    pub fn new(state: SessionState, config: SessionConfig, journal: FixJournal) -> Self {
        Self {
            state,
            journal,
            config,
            garbage_frames: 0,
            pending: Control::None,
            terminated: false,
            _dict: PhantomData,
        }
    }

    /// Starts a [`FixSessionBuilder`] to configure and build a [`FixParts`] trio.
    pub fn builder() -> FixSessionBuilder<D, NoCustomizer> {
        FixSessionBuilder {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            customizer: NoCustomizer,
            _dict: PhantomData,
        }
    }

    // ── introspection ────────────────────────────────────────────────────────

    pub fn state(&self) -> &SessionState {
        &self.state
    }

    pub fn state_mut(&mut self) -> &mut SessionState {
        &mut self.state
    }

    /// The negotiated heartbeat interval (`HeartBtInt(108)`). The one value the
    /// session exposes so the caller can build their own keepalive/liveness
    /// timers — the session holds none. See
    /// [`SessionState::heartbeat_interval`].
    pub fn heartbeat_interval(&self) -> std::time::Duration {
        self.state.heartbeat_interval()
    }

    pub fn garbage_frame_count(&self) -> u64 {
        self.garbage_frames
    }

    /// Whether the session should still be read from (not disconnected).
    pub fn wants_read(&self) -> bool {
        self.state.state() != State::Disconnected
    }

    /// Whether the session has terminated: a clean logout completed, or a fatal
    /// error was surfaced. Once terminated, [`recv`](Self::recv) refuses further
    /// calls until a fresh [`connect`](Self::connect)/[`connect_reset`](Self::connect_reset)
    /// revives it.
    pub const fn is_terminated(&self) -> bool {
        self.terminated
    }

    /// Force the terminated flag so [`recv`](Self::recv) refuses further calls.
    ///
    /// **Wrapper-author API — do NOT call in normal use.** [`recv`](Self::recv)
    /// already sets this on a clean logout or a fatal error, and
    /// [`connect`](Self::connect)/[`connect_reset`](Self::connect_reset) clear it.
    /// It exists solely for authors building a custom transport wrapper over the
    /// sans-IO seam who reimplement `recv`'s terminated guard — exactly what the
    /// async engine's `FixSession` newtype does. Ordinary session code never
    /// touches it.
    pub fn mark_terminated(&mut self) {
        self.terminated = true;
    }

    pub fn allocate_seq(&mut self) -> Result<u32, SessionError> {
        self.state.allocate_seq()
    }

    // ── protocol actions — encode-only primitives (sans-IO, no transport) ─────
    //
    // Each `encode_<action>` stamps the seqnum + SendingTime, journals where the
    // protocol requires it, and stages the frame into `writer` — no I/O. Drain
    // the bytes yourself via [`writer.data()`](MessageWriter::data) /
    // [`advance`](MessageWriter::advance) (the kernel-bypass / custom-transport
    // path), or use the combined verb form below, which encodes then flushes.
    //
    // ## The `now` clock contract
    //
    // Every send takes `now: i128` — a UTC wall-clock timestamp in **nanoseconds
    // since the Unix epoch** — and stamps it into `SendingTime(52)`. The session
    // reads no clock of its own: the core is a pure function of `(bytes, now)`,
    // fully replayable for testing and historical replay. `now` exists *only* for
    // the wire timestamp; it is never an `Instant` and never drives session state.

    /// Encodes a Logon (initiate the session) into `writer`. Encode-only: drain
    /// the bytes yourself via [`writer.data()`](MessageWriter::data), use
    /// [`connect`](Self::connect) to encode + flush in one call, or let
    /// [`recv`](Self::recv) flush them.
    ///
    /// `now` stamps `SendingTime(52)` (UTC unix-nanos); see the [clock
    /// contract](#the-now-clock-contract).
    pub fn encode_connect<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
    ) -> Result<(), Error> {
        // A fresh connection revives a session that terminated (clean logout or
        // fatal error), so the same carry-over session can reconnect.
        self.terminated = false;
        let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
        self.state.connect(&mut emitter)?;
        Ok(())
    }

    /// Encodes a Logon with `ResetSeqNumFlag=Y` into `writer`. Encode-only; see
    /// [`connect_reset`](Self::connect_reset) for the encode + flush form. `now`
    /// stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn encode_connect_reset<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
    ) -> Result<(), Error> {
        self.terminated = false;
        let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
        self.state.connect_reset(&mut emitter)?;
        Ok(())
    }

    /// Encodes an in-session sequence reset handshake into `writer`. Encode-only;
    /// see [`reset_sequence`](Self::reset_sequence) for the encode + flush form.
    /// `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn encode_reset_sequence<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
    ) -> Result<(), Error> {
        let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
        self.state.reset_sequence(&mut emitter)?;
        Ok(())
    }

    /// Encodes a Logout into `writer`. Encode-only; see [`logout`](Self::logout)
    /// for the encode + flush form. `now` stamps `SendingTime(52)` (UTC unix-nanos).
    ///
    /// `reason`, if `Some`, rides the wire as `Text(58)` — a printable-ASCII
    /// [`AsciiTextStr`], SOH-safe by construction. `None` emits a bare Logout.
    pub fn encode_logout<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
        reason: Option<&AsciiTextStr>,
    ) -> Result<(), Error> {
        let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
        self.state.logout(reason, &mut emitter)?;
        Ok(())
    }

    /// Encodes a Heartbeat (35=0) into `writer`, optionally echoing a peer's
    /// `TestReqID(112)`. Encode-only; see [`heartbeat`](Self::heartbeat) for the
    /// encode + flush form.
    ///
    /// Pass `Some(id)` — the validated `TestReqID` from a
    /// [`Message::TestRequest`], echoed verbatim via its bytes — to answer it, or
    /// `None` for an unsolicited keepalive. `now` stamps `SendingTime(52)` (UTC
    /// unix-nanos).
    pub fn encode_heartbeat<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
        echo: Option<&AsciiTextStr>,
    ) -> Result<(), Error> {
        let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
        self.state
            .heartbeat(echo.map(AsciiTextStr::as_bytes), &mut emitter)?;
        Ok(())
    }

    /// Encodes a TestRequest (35=1) into `writer` with a fresh `TestReqID(112)`.
    /// Encode-only; see [`test_request`](Self::test_request) for the encode + flush
    /// form. `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn encode_test_request<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
    ) -> Result<(), Error> {
        let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
        self.state.test_request(&mut emitter)?;
        Ok(())
    }

    /// Encodes a ResendRequest (35=2) covering `[begin, ∞)` into `writer`.
    /// Encode-only; see [`resend_request`](Self::resend_request) for the encode +
    /// flush form. `begin` is the first missing inbound seqnum; `now` stamps
    /// `SendingTime(52)` (UTC unix-nanos).
    pub fn encode_resend_request<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
        begin: u32,
    ) -> Result<(), Error> {
        let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
        self.state.resend_request(begin, &mut emitter)?;
        Ok(())
    }

    /// Encodes a SequenceReset-Reset (35=4, `GapFillFlag=N`) forcing the peer's
    /// expected inbound seqnum to `new_seq` into `writer`. Encode-only; see
    /// [`sequence_reset`](Self::sequence_reset) for the encode + flush form.
    ///
    /// The "force the peer forward" answer to a [`Message::ResendOutOfRange`] whose
    /// `EndSeqNo` exceeds what we sent. Allocates the next outbound seqnum for
    /// `MsgSeqNum(34)` and journals, like every other outbound admin. For the
    /// GapFill-mode answer (a `BeginSeqNo` that rotated off) use
    /// [`encode_gap_fill`](Self::encode_gap_fill) instead.
    ///
    /// **Distinct from [`encode_reset_sequence`](Self::encode_reset_sequence)**,
    /// which starts the *in-session reset handshake* (a TestRequest/Logon exchange),
    /// not a SequenceReset message. `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn encode_sequence_reset<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
        new_seq: u32,
    ) -> Result<(), Error> {
        let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
        self.state.sequence_reset(new_seq, &mut emitter)?;
        Ok(())
    }

    /// Encodes a SequenceReset-GapFill (35=4, `GapFillFlag=Y` + `PossDupFlag=Y`)
    /// standing in for the skipped outbound range `[from_seq, new_seq)` into
    /// `writer`. Encode-only; see [`gap_fill`](Self::gap_fill) for the encode + flush
    /// form.
    ///
    /// The answer to a [`Message::ResendOutOfRange`] whose `BeginSeqNo` rotated off
    /// the replay window. **`MsgSeqNum(34)` is `from_seq`** (the seqnum the peer is
    /// waiting on), *not* an allocated one — a gap-fill closes the peer's gap rather
    /// than opening a new one, so this **does not allocate or advance the outbound
    /// seqnum**. It is also **not journaled**: `from_seq` has already rotated off the
    /// replay window, so journaling it would rewind the outbound counter. `new_seq`
    /// is the `NewSeqNo(36)`. `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn encode_gap_fill<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
        from_seq: u32,
        new_seq: u32,
    ) -> Result<(), Error> {
        // A no-op `after`: unlike other admin emits, a gap-fill is not journaled —
        // `from_seq` sits below the replay low-water (that is why the resend was
        // out of range), so `journal.store(from_seq, ..)` would rewind next_outbound.
        // The customizer still runs (it is part of `Emitter::emit`), matching every
        // other outbound admin.
        let mut emitter = Emitter::new(writer, &self.config, now, |_seq, _frame| Ok(()));
        self.state.gap_fill(from_seq, new_seq, &mut emitter)?;
        Ok(())
    }

    /// Encodes the reply to a counterparty-initiated Logon surfaced as
    /// [`Message::LogonRequest`] / [`Message::LogonResetRequest`], and advances the
    /// session — the encode-only half of [`LogonDecision::accept`]. `now` stamps
    /// `SendingTime(52)` (UTC unix-nanos).
    ///
    /// The `seq`/`heart_bt_int_s`/`is_reset` are the fields captured from the peer
    /// Logon by the decision. Returns [`Error::UnexpectedDisconnect`] if the peer's
    /// Logon seqnum was below expected (an establishment protocol error); the
    /// session is marked terminated in that case.
    pub fn encode_accept_logon<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
        seq: u32,
        heart_bt_int_s: u32,
        is_reset: bool,
    ) -> Result<(), Error> {
        let ctrl = {
            let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
            self.state
                .accept_logon(seq, heart_bt_int_s, is_reset, &mut emitter)?
        };
        if let Control::Disconnected { reason } = ctrl {
            self.terminated = true;
            return Err(Error::UnexpectedDisconnect { reason });
        }
        Ok(())
    }

    /// Encodes a Logout rejecting a counterparty-initiated Logon and disconnects —
    /// the encode-only half of [`LogonDecision::reject`]. `now` stamps
    /// `SendingTime(52)` (UTC unix-nanos).
    ///
    /// `reason` is the caller's rejection rationale (e.g. failed authentication).
    /// When `Some`, it rides the wire as `Text(58)` on the emitted Logout — a
    /// printable-ASCII [`AsciiTextStr`], SOH-safe by construction; `None` emits a
    /// bare Logout. The session is marked terminated.
    pub fn encode_reject_logon<C: SessionCustomizer>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        now: i128,
        reason: Option<&AsciiTextStr>,
    ) -> Result<(), Error> {
        {
            let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
            self.state.reject_logon(reason, &mut emitter)?;
        }
        self.terminated = true;
        Ok(())
    }

    /// Journals then encodes an application frame at sequence `seq` into `writer`.
    /// Encode-only; see [`send_app`](Self::send_app) for the encode + flush form.
    ///
    /// The frame must fit the pre-allocated writer with [`REFRAME_HEADROOM`] to
    /// spare (so a later resend reframe fits). Larger frames return
    /// [`Error::MessageTooLarge`] before any journal or buffer write; size the
    /// writer up front for the workload.
    pub fn encode_send_app<C>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        seq: u32,
        frame: &[u8],
    ) -> Result<(), Error> {
        if frame.len() > writer.capacity().saturating_sub(REFRAME_HEADROOM) {
            return Err(Error::MessageTooLarge(frame.len()));
        }
        journal_write(frame.len(), || self.journal.store(seq, frame))?;
        buffer_frame(&mut writer.inner, frame)
    }

    // ── protocol actions — combined (encode + flush over `Read + Write`) ──────
    //
    // The one-call convenience: encode via the `encode_<action>` primitive above,
    // then flush the whole writer to `conn` with
    // [`writer.flush_to`](MessageWriter::flush_to). The async twin
    // (`nexus_async_fix_engine::FixSession`) offers the same verbs over a
    // [`nexus_net::WireStream`]. For a custom transport, call the encode-only form
    // and drain the byte seam yourself.

    /// Encodes a Logon and flushes it to `conn` (initiate the session). `now`
    /// stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn connect<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_connect(writer, now)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Encodes a Logon with `ResetSeqNumFlag=Y` and flushes it to `conn`. `now`
    /// stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn connect_reset<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_connect_reset(writer, now)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Encodes an in-session sequence reset handshake and flushes it to `conn`.
    /// `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn reset_sequence<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_reset_sequence(writer, now)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Encodes a Logout and flushes it to `conn`. Use this to answer a
    /// [`Message::LogoutRequest`] or to initiate a logout. `now` stamps
    /// `SendingTime(52)` (UTC unix-nanos).
    ///
    /// `reason`, if `Some`, rides the wire as `Text(58)` — a printable-ASCII
    /// [`AsciiTextStr`], SOH-safe by construction. `None` emits a bare Logout.
    pub fn logout<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        reason: Option<&AsciiTextStr>,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_logout(writer, now, reason)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Encodes a Heartbeat (echoing `echo` if `Some`) and flushes it to `conn`.
    /// Answers a [`Message::TestRequest`] with `Some(id)` (the validated
    /// `TestReqID`), or sends an unsolicited keepalive with `None`. `now` stamps
    /// `SendingTime(52)` (UTC unix-nanos).
    pub fn heartbeat<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        echo: Option<&AsciiTextStr>,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_heartbeat(writer, now, echo)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Encodes a TestRequest and flushes it to `conn`. `now` stamps
    /// `SendingTime(52)` (UTC unix-nanos).
    pub fn test_request<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_test_request(writer, now)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Encodes a ResendRequest covering `[begin, ∞)` and flushes it to `conn`.
    /// Answers a [`Message::GapDetected`]. `now` stamps `SendingTime(52)` (UTC
    /// unix-nanos).
    pub fn resend_request<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        begin: u32,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_resend_request(writer, now, begin)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Encodes a SequenceReset-Reset forcing the peer's expected seqnum to `new_seq`
    /// and flushes it to `conn`. Answers a [`Message::ResendOutOfRange`] whose
    /// `EndSeqNo` exceeds what we sent; see
    /// [`encode_sequence_reset`](Self::encode_sequence_reset). For the rotated-off
    /// `BeginSeqNo` case use [`gap_fill`](Self::gap_fill). Distinct from
    /// [`reset_sequence`](Self::reset_sequence) (the in-session reset handshake).
    /// `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn sequence_reset<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        new_seq: u32,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_sequence_reset(writer, now, new_seq)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Encodes a SequenceReset-GapFill standing in for `[from_seq, new_seq)` and
    /// flushes it to `conn`. Answers a [`Message::ResendOutOfRange`] whose
    /// `BeginSeqNo` rotated off the replay window: `MsgSeqNum(34)` is `from_seq` (no
    /// seqnum is consumed), and the frame is not journaled — see
    /// [`encode_gap_fill`](Self::encode_gap_fill). `now` stamps `SendingTime(52)`.
    pub fn gap_fill<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        from_seq: u32,
        new_seq: u32,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_gap_fill(writer, now, from_seq, new_seq)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Journals, encodes an application frame at sequence `seq`, and flushes it to
    /// `conn`. See [`encode_send_app`](Self::encode_send_app) for the frame-size
    /// constraint. The app frame carries its own `SendingTime(52)`, so this takes
    /// no `now`.
    pub fn send_app<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        seq: u32,
        frame: &[u8],
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_send_app(writer, seq, frame)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Accepts a counterparty-initiated Logon (surfaced as [`Message::LogonRequest`] /
    /// [`Message::LogonResetRequest`]): sends the reply and brings the session up. The
    /// session-method spelling of [`LogonDecision::accept`], and the sync twin of the
    /// async `FixSession::accept_logon`. `now` stamps `SendingTime(52)`.
    pub fn accept_logon<C, S>(
        &mut self,
        decision: LogonDecision<'_, D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        decision.accept(self, writer, conn, now)
    }

    /// Rejects a counterparty-initiated Logon: sends a Logout (optional `Text(58)`
    /// reason) and disconnects. The session-method spelling of [`LogonDecision::reject`],
    /// and the sync twin of the async `FixSession::reject_logon`. `now` stamps
    /// `SendingTime(52)`.
    pub fn reject_logon<C, S>(
        &mut self,
        decision: LogonDecision<'_, D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        reason: Option<&AsciiTextStr>,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        decision.reject(self, writer, conn, now, reason)
    }

    // ── inbound processing ───────────────────────────────────────────────────

    /// Processes the next buffered inbound frame in `reader`, driving the state
    /// machine, journaling, and enqueuing any *mechanism* outbound admin into
    /// `writer` (the reset-handshake and protocol-error emits the engine still
    /// drives). Returns a non-borrowing [`PollOutcome`]; call
    /// [`message`](Self::message) after [`PollOutcome::Message`].
    ///
    /// `now` stamps `SendingTime(52)` on any mechanism emit (UTC unix-nanos); most
    /// calls will not emit and ignore it. See the [module docs](self) for the poll
    /// loop.
    pub fn poll<C: SessionCustomizer>(
        &mut self,
        reader: &mut MessageReader<D>,
        writer: &mut MessageWriter<D, C>,
        now: i128,
    ) -> Result<PollOutcome, Error> {
        // Keep the journal's inbound cursor aligned with the state machine.
        let n = self.state.next_inbound_seq();
        if n != self.journal.next_inbound() {
            self.journal.set_next_inbound(n);
        }

        // Pull the next complete frame into the stable buffer. A malformed frame
        // is surfaced as the recoverable `Error::Malformed` (one per poll) rather
        // than silently skipped, so the caller can observe link deterioration; the
        // reader has already advanced past it, so the next poll resumes cleanly.
        if reader.inner.should_compact() {
            reader.inner.compact();
        }
        match reader.inner.next() {
            Err(FrameError::MessageTooLarge { size }) => {
                return Err(Error::MessageTooLarge(size));
            }
            Err(FrameError::Malformed { skipped, reason }) => {
                self.garbage_frames += 1;
                return Err(Error::Malformed {
                    skipped,
                    count: self.garbage_frames,
                    reason,
                });
            }
            Ok(None) => return Ok(PollOutcome::NeedMoreBytes),
            Ok(Some(raw)) => {
                reader.frame.clear();
                reader.frame.extend_from_slice(raw);
            }
        }

        self.process_frame(reader, writer, now)
    }

    /// Reconstructs the typed [`Message`] for the frame just processed by
    /// [`poll`](Self::poll). Only valid immediately after a [`PollOutcome::Message`]
    /// or a [`PollOutcome::LoggedOut`] (which maps to `Message::LoggedOut`); an
    /// abnormal [`PollOutcome::Disconnected`] is surfaced as an `Err`, never here.
    ///
    /// The borrow is over the `reader`'s stable frame buffer — *not* `&mut self` —
    /// so `&mut session` and `&mut writer` stay free for the reply.
    pub fn message<'r>(&self, reader: &'r MessageReader<D>) -> Message<'r, D> {
        let frame = &reader.frame[..];
        match self.pending {
            // Only the initiator ack (`acknowledged == true`) is ever surfaced as a
            // `Control::Logon`; the acceptor returns `Control::LogonRequest`.
            Control::Logon { .. } => {
                let msg = D::Logon::decode(frame).expect("frame decoded in poll");
                Message::LogonAcknowledged { msg }
            }
            Control::LogonRequest {
                seq,
                heart_bt_int_s,
            } => Message::LogonRequest(LogonDecision {
                msg: D::Logon::decode(frame).expect("frame decoded in poll"),
                seq,
                heart_bt_int_s,
                is_reset: false,
            }),
            Control::LogonResetRequest {
                seq,
                heart_bt_int_s,
            } => Message::LogonResetRequest(LogonDecision {
                msg: D::Logon::decode(frame).expect("frame decoded in poll"),
                seq,
                heart_bt_int_s,
                is_reset: true,
            }),
            Control::GapDetected { begin } => Message::GapDetected { begin },
            Control::Logout => {
                let msg = D::Logout::decode(frame).expect("frame decoded in poll");
                Message::LogoutRequest { msg }
            }
            Control::Heartbeat => {
                let msg = D::Heartbeat::decode(frame).expect("frame decoded in poll");
                Message::Heartbeat { msg }
            }
            Control::TestRequest => {
                let id = find_tag(frame, 0, 112)
                    .and_then(|span| FieldView::<&AsciiTextStr>::new(span, frame))
                    .map_or(AsciiTextStr::empty(), |fv| {
                        // SAFETY: the b"1" classify path in `process_frame` already
                        // validated tag 112 is present and printable-ASCII before
                        // producing `Control::TestRequest`, and `message()` runs
                        // only after that successful `poll` — so the unchecked
                        // borrow upholds the `AsciiTextStr` invariant.
                        unsafe { fv.get_unchecked() }
                    });
                Message::TestRequest { id }
            }
            Control::ResendCursor { begin, end } => Message::ResendRequest {
                cursor: ResendCursor::new(begin, end),
            },
            Control::ResendOutOfRange {
                begin,
                end,
                low_water,
                high_water,
            } => Message::ResendOutOfRange {
                begin,
                end,
                low_water,
                high_water,
            },
            Control::ResendRequest => {
                unreachable!("driver refines ResendRequest into ResendCursor/ResendOutOfRange")
            }
            Control::SequenceReset => {
                let msg = D::SequenceReset::decode(frame).expect("frame decoded in poll");
                Message::SequenceReset { msg }
            }
            Control::Reject => {
                let msg = D::Reject::decode(frame).expect("frame decoded in poll");
                Message::Reject { msg }
            }
            Control::Application => Message::Application {
                header: D::Header::decode(frame),
            },
            Control::LoggedOut => {
                let msg = D::Logout::decode(frame).expect("frame decoded in poll");
                Message::LoggedOut { msg }
            }
            Control::Disconnected { .. } => {
                unreachable!("abnormal disconnect is surfaced as an Err, never message()")
            }
            Control::None | Control::Proceed => {
                unreachable!("message() called without a pending message")
            }
        }
    }

    /// Full protocol handling for the frame in `reader.frame`. Comp-id
    /// validation, inbound journaling, per-type state driving, and outbound
    /// admin/resend enqueue into `writer`.
    fn process_frame<C: SessionCustomizer>(
        &mut self,
        reader: &MessageReader<D>,
        writer: &mut MessageWriter<D, C>,
        now: i128,
    ) -> Result<PollOutcome, Error> {
        let frame = &reader.frame[..];

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
            {
                let mut emitter = journaling_emitter(writer, &mut self.journal, &self.config, now);
                self.state.on_comp_id_mismatch(&mut emitter)?;
            }
            // Always surface CompIdMismatch here, mirroring the original driver:
            // the handler disconnects the state machine; the reason is fixed.
            return Ok(self.dispose(Control::Disconnected {
                reason: DisconnectReason::CompIdMismatch,
            }));
        }

        // Well-framed and comp-id-valid: archive the inbound message for
        // visibility/audit. Malformed and foreign (comp-id-mismatched) frames are
        // not journaled — they never reach here.
        journal_write(frame.len(), || self.journal.store_inbound(frame))?;

        let frame = &reader.frame[..];
        let raw_type = if let Some(s) = find_tag(frame, 0, 35) {
            s.slice(frame)
        } else {
            // The missing-tag-35 reject is NOT journaled (matches the original):
            // this call site gives the `Emitter` a no-op `after` closure, while
            // every other site uses the journaling emitter.
            let mut emitter = Emitter::new(writer, &self.config, now, |_seq, _frame| Ok(()));
            self.state.on_reject_inbound(
                RejectInboundIn {
                    seq,
                    ref_tag_id: Some(35),
                    session_reject_reason: 1,
                    is_poss_dup: poss_dup,
                },
                &mut emitter,
            )?;
            return Ok(PollOutcome::Suppressed);
        };

        match raw_type {
            b"A" => {
                // Validate the typed decode before any side effect: a malformed
                // admin (e.g. a Logon missing a required field) must error with
                // MalformedMessage, not drive the state machine and then surface a
                // `Control` whose `message()` reconstruction panics in
                // `.expect("frame decoded in poll")`. The handler returns the
                // message kind from tag 35 regardless of the typed body, so this
                // decode is the only place the typed parse runs — it makes that
                // `.expect()` genuinely safe. Discard the value; validation only.
                D::Logon::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                let hbi = find_tag(frame, 0, 108)
                    .and_then(|s| parse_fix_uint(s.slice(frame)).ok())
                    .unwrap_or(30);
                let reset = find_tag(frame, 0, 141)
                    .and_then(|s| parse_fix_bool(s.slice(frame)).ok())
                    .unwrap_or(false);
                let was_logon_sent = self.state.state() == State::LogonSent;
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(writer, &mut self.journal, &self.config, now);
                    self.state.on_logon(
                        LogonIn {
                            seq,
                            heart_bt_int_s: hbi,
                            is_reset_seq_num: reset,
                            send_reply: !was_logon_sent,
                        },
                        &mut emitter,
                    )?
                };
                Ok(self.dispose(ctrl))
            }
            b"5" => {
                // Validate the typed decode before any side effect (see `b"A"`).
                D::Logout::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(writer, &mut self.journal, &self.config, now);
                    self.state.on_logout(
                        LogoutIn {
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        &mut emitter,
                    )?
                };
                Ok(self.dispose(ctrl))
            }
            b"0" => {
                // Validate the typed decode before any side effect (see `b"A"`).
                D::Heartbeat::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                let echo_id =
                    find_tag(frame, 0, 112).and_then(|s| parse_fix_seqnum(s.slice(frame)).ok());
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(writer, &mut self.journal, &self.config, now);
                    self.state.on_heartbeat(
                        HeartbeatIn {
                            echo_id,
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        &mut emitter,
                    )?
                };
                Ok(self.dispose(ctrl))
            }
            b"1" => {
                // Validate the typed decode before any side effect (see `b"A"`).
                D::TestRequest::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                // Validate `TestReqID(112)` here, in the fallible path: absent →
                // MissingField, present-but-non-ASCII → MalformedField. This is
                // what makes the later unchecked borrow in `message()` sound — the
                // id is proven present + printable-ASCII before the message is
                // surfaced (a malformed 112 is an error, never a silent empty echo).
                let span = find_tag(frame, 0, 112)
                    .ok_or(Error::Protocol(SessionError::MissingField { tag: 112 }))?;
                FieldView::<&AsciiTextStr>::new(span, frame)
                    .ok_or(Error::Protocol(SessionError::MissingField { tag: 112 }))?
                    .checked()
                    .map_err(|_| Error::Protocol(SessionError::MalformedField { tag: 112 }))?;
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(writer, &mut self.journal, &self.config, now);
                    self.state.on_test_request(
                        TestRequestIn {
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        &mut emitter,
                    )?
                };
                Ok(self.dispose(ctrl))
            }
            b"2" => {
                // Validate the typed decode before any side effect (see `b"A"`).
                D::ResendRequest::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                let begin = find_tag(frame, 0, 7)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .map_or(0, |v| v as u32);
                let end = find_tag(frame, 0, 16)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .map_or(0, |v| v as u32);
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(writer, &mut self.journal, &self.config, now);
                    self.state.on_resend_request(
                        ResendRequestIn {
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        &mut emitter,
                    )?
                };
                // ResendRequest is the one kind the driver refines beyond
                // surfacing the message: it checks the requested range against the
                // journal's retained replay window up front, so the surfaced cursor
                // is *guaranteed* to fulfill (it never hits out-of-range mid-pump),
                // and a range outside the window becomes an explicit out-of-range
                // signal the user answers with `sequence_reset` — never a silent
                // gap-fill.
                match ctrl {
                    Control::ResendRequest => {
                        let low_water = self.journal.resend_low_water();
                        let high_water = self.journal.resend_high_water();
                        // Open-ended (`EndSeqNo=0`) resolves to everything we have.
                        let resolved_end = if end == 0 { high_water } else { end };
                        self.pending = if low_water <= begin && resolved_end <= high_water {
                            Control::ResendCursor {
                                begin,
                                end: resolved_end,
                            }
                        } else {
                            Control::ResendOutOfRange {
                                begin,
                                end: resolved_end,
                                low_water,
                                high_water,
                            }
                        };
                        Ok(PollOutcome::Message)
                    }
                    other => Ok(self.dispose(other)),
                }
            }
            b"4" => {
                // Validate the typed decode before any side effect (see `b"A"`).
                D::SequenceReset::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                let new_seq = find_tag(frame, 0, 36)
                    .and_then(|s| parse_fix_seqnum(s.slice(frame)).ok())
                    .map_or(0, |v| v as u32);
                let gap_fill = find_tag(frame, 0, 123)
                    .and_then(|s| parse_fix_bool(s.slice(frame)).ok())
                    .unwrap_or(false);
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(writer, &mut self.journal, &self.config, now);
                    self.state.on_sequence_reset(
                        SequenceResetIn {
                            seq,
                            new_seq,
                            is_poss_dup: poss_dup,
                            is_gap_fill: gap_fill,
                        },
                        &mut emitter,
                    )?
                };
                Ok(self.dispose(ctrl))
            }
            b"3" => {
                // Validate the typed decode before any side effect (see `b"A"`).
                D::Reject::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(writer, &mut self.journal, &self.config, now);
                    self.state.on_reject(
                        RejectIn {
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        &mut emitter,
                    )?
                };
                Ok(self.dispose(ctrl))
            }
            _ => {
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(writer, &mut self.journal, &self.config, now);
                    self.state.on_app(
                        AppIn {
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        &mut emitter,
                    )?
                };
                Ok(self.dispose(ctrl))
            }
        }
    }

    /// Stores the state machine's verdict for [`message`](Self::message) and maps
    /// it to a [`PollOutcome`]. Centralizes the outcome mapping every non-resend
    /// arm shares.
    fn dispose(&mut self, ctrl: Control) -> PollOutcome {
        self.pending = ctrl;
        match ctrl {
            Control::None => PollOutcome::Suppressed,
            Control::LoggedOut => PollOutcome::LoggedOut,
            Control::Disconnected { reason } => PollOutcome::Disconnected(reason),
            Control::Proceed => unreachable!("Proceed is transient; handlers never return it"),
            _ => PollOutcome::Message,
        }
    }

    // ── transport convenience (blocking `Read + Write`) ──────────────────────

    /// Receives the next typed [`Message`] over a blocking `Read + Write`
    /// transport — the thin convenience over the sans-IO seam.
    ///
    /// Fills `reader` from `conn`, drives [`poll`](Self::poll), drains any
    /// *mechanism* outbound (reset handshake, protocol-error Logout) from `writer`
    /// to `conn`, and returns the message. A resend is *not* driven here — an
    /// inbound ResendRequest surfaces a [`ResendCursor`] the caller pumps. `Ok(None)`
    /// means a step produced nothing to surface (an out-of-sequence app, a
    /// session-level reject, or a caller-set socket read timeout elapsing with no
    /// complete frame — run your own liveness timers and call `recv` again).
    ///
    /// `now` (UTC unix-nanos) stamps `SendingTime(52)` on any mechanism emit the
    /// engine still drives inside `recv`, so the core stays a pure function of
    /// `(bytes, now)`. It keeps its `writer` for exactly those emits; the reply to
    /// the returned message is still yours to send. `now` is `Copy`, so the borrow
    /// guarantee below is unaffected.
    ///
    /// The returned `Message<'r>` borrows `reader`, *not* `&mut self`, so `&mut
    /// session` and `&mut writer` stay free for the reply while the payload is
    /// still borrowed. A caller that needs no `Read + Write` bound drives the seam
    /// directly (`poll`/`message` + the byte methods) instead.
    pub fn recv<'r, C, S>(
        &mut self,
        reader: &'r mut MessageReader<D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<Option<Message<'r, D>>, Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        if self.terminated {
            return Err(Error::Closed);
        }
        // `recv_step` returns an *owned* outcome so this dispatch can arm the
        // terminated guard — on a clean logout or any fatal error — before
        // borrowing `reader` to reconstruct the message.
        match self.recv_step(reader, writer, conn, now) {
            Ok(RecvStep::Message) => Ok(Some(self.message(reader))),
            Ok(RecvStep::LoggedOut) => {
                self.terminated = true;
                Ok(Some(self.message(reader)))
            }
            Ok(RecvStep::Nothing) => Ok(None),
            Err(e) => {
                if e.is_fatal() {
                    self.terminated = true;
                }
                Err(e)
            }
        }
    }

    /// Advances one step over a blocking transport, returning an *owned*
    /// [`RecvStep`]. Fills `reader` from `conn` on `NeedMoreBytes` and drains
    /// `writer` to `conn` after every `poll`.
    fn recv_step<C, S>(
        &mut self,
        reader: &mut MessageReader<D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<RecvStep, Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        loop {
            let outcome = self.poll(reader, writer, now)?;
            // Drain any admin the core enqueued this step (mirrors the original
            // driver, which flushed after every protocol handler). Also flushes a
            // pending opening Logon / `send_app` staged before `recv`.
            writer.flush_to(conn).map_err(Error::Io)?;

            match outcome {
                PollOutcome::Message => return Ok(RecvStep::Message),
                PollOutcome::LoggedOut => return Ok(RecvStep::LoggedOut),
                // Abnormal drop: a fault, surfaced as an error, not a message.
                PollOutcome::Disconnected(reason) => {
                    return Err(Error::UnexpectedDisconnect { reason });
                }
                PollOutcome::Suppressed => return Ok(RecvStep::Nothing),
                PollOutcome::NeedMoreBytes => {
                    // An empty spare means the reader buffer is full with a single
                    // incomplete frame that cannot grow (compaction reclaimed
                    // nothing). Reading into a zero-length slice yields `Ok(0)`,
                    // which the `Ok(0)` arm below would misread as EOF. Surface it
                    // as the real cause: a frame larger than the reader buffer.
                    if reader.spare().is_empty() {
                        return Err(Error::MessageTooLarge(reader.capacity().saturating_add(1)));
                    }
                    let spare = reader.spare();
                    match conn.read(spare) {
                        // Peer closed the transport (FIN) without a FIX Logout.
                        Ok(0) => {
                            return Err(Error::UnexpectedDisconnect {
                                reason: DisconnectReason::PeerClosed,
                            });
                        }
                        Ok(n) => reader.filled(n),
                        // A caller-set socket read timeout elapsed with no complete
                        // frame. The session holds no timers, so there is nothing to
                        // service — yield control so the caller can run its own
                        // heartbeat/liveness timers, then call `recv` again.
                        Err(e) if is_timeout(&e) => return Ok(RecvStep::Nothing),
                        Err(e) => return Err(Error::Io(e)),
                    }
                }
            }
        }
    }
}

impl<D: FixDictionary> LogonDecision<'_, D> {
    /// Encodes the accept reply into `writer` and advances the session — the
    /// encode-only half of [`accept`](Self::accept), for the custom-transport /
    /// async path. Consumes the decision (its obligation is satisfied). `now`
    /// stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn encode_accept<C: SessionCustomizer>(
        self,
        session: &mut FixSession<D>,
        writer: &mut MessageWriter<D, C>,
        now: i128,
    ) -> Result<(), Error> {
        session.encode_accept_logon(writer, now, self.seq, self.heart_bt_int_s, self.is_reset)
    }

    /// Encodes the reject Logout into `writer` and disconnects — the encode-only
    /// half of [`reject`](Self::reject). `now` stamps `SendingTime(52)`.
    ///
    /// `reason`, if `Some`, rides the wire as `Text(58)` on the Logout — a
    /// printable-ASCII [`AsciiTextStr`], SOH-safe by construction; see
    /// [`FixSession::encode_reject_logon`].
    pub fn encode_reject<C: SessionCustomizer>(
        self,
        session: &mut FixSession<D>,
        writer: &mut MessageWriter<D, C>,
        now: i128,
        reason: Option<&AsciiTextStr>,
    ) -> Result<(), Error> {
        session.encode_reject_logon(writer, now, reason)
    }

    /// Accepts the Logon: sends the reply (a Logon, or a LogonReset for a reset
    /// request), applies the negotiated `HeartBtInt`, and brings the session up.
    /// Encode + flush over a blocking transport. `now` stamps `SendingTime(52)`.
    pub fn accept<C, S>(
        self,
        session: &mut FixSession<D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_accept(session, writer, now)?;
        writer.flush_to(conn).map_err(Error::Io)
    }

    /// Rejects the Logon: sends a Logout and disconnects. Encode + flush over a
    /// blocking transport. `now` stamps `SendingTime(52)`.
    ///
    /// `reason`, if `Some`, rides the wire as `Text(58)` on the Logout — a
    /// printable-ASCII [`AsciiTextStr`], SOH-safe by construction; `None` sends a
    /// bare Logout. The rejected peer sees the reason string when supplied.
    pub fn reject<C, S>(
        self,
        session: &mut FixSession<D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        reason: Option<&AsciiTextStr>,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: Read + Write,
    {
        self.encode_reject(session, writer, now, reason)?;
        writer.flush_to(conn).map_err(Error::Io)
    }
}

/// Pumping methods for [`ResendCursor`]. The `Copy` state struct and its
/// `begin`/`end` getters are defined alongside [`Message`] (so both compile on
/// non-unix); the replay pump lives here because it drives the unix-only
/// [`FixJournal`] through [`FixSession`].
impl ResendCursor {
    /// Reframe the next item into `writer` and return its bytes, or `Ok(None)` when
    /// the whole range has drained (Done).
    ///
    /// The returned slice borrows `writer`; **write it before calling `next` again**
    /// — the next call reuses the writer buffer. `now` (UTC unix-nanos) stamps the
    /// item's `SendingTime(52)`. Equivalent to [`next_batch`](Self::next_batch) with
    /// `max = 1`.
    pub fn next<'w, D, C>(
        &mut self,
        session: &mut FixSession<D>,
        writer: &'w mut MessageWriter<D, C>,
        now: i128,
    ) -> Result<Option<&'w [u8]>, Error>
    where
        D: FixDictionary,
    {
        self.next_batch(session, writer, now, 1)
    }

    /// Reframe up to `max` items into `writer` (also bounded by writer capacity),
    /// concatenated, so one write drains several messages. Returns the concatenated
    /// bytes, or `Ok(None)` when the whole range has drained (Done).
    ///
    /// The returned slice borrows `writer`; **write it before calling again** — the
    /// next call reuses the writer buffer. One `now` stamps every item's
    /// `SendingTime(52)` in the batch (the standard for a batch retransmit).
    ///
    /// Stops early when the next item would not fit the writer's remaining capacity,
    /// returning what has been staged so far; the following call resumes at the
    /// unfit item. If a *single* item does not fit an empty writer the writer is
    /// undersized for the workload and [`Error::MessageTooLarge`] is returned.
    pub fn next_batch<'w, D, C>(
        &mut self,
        session: &mut FixSession<D>,
        writer: &'w mut MessageWriter<D, C>,
        now: i128,
        max: usize,
    ) -> Result<Option<&'w [u8]>, Error>
    where
        D: FixDictionary,
    {
        // Discard the previously-yielded frame — the caller has written it. The
        // writer auto-resets to full capacity once fully drained, so each batch
        // reframes into a fresh buffer and the returned slice is exactly this batch.
        let staged = writer.inner.data().len();
        if staged > 0 {
            writer.inner.advance(staged);
        }

        if max == 0 || self.pos > self.end {
            return Ok(None);
        }

        let mut ts = [0u8; UTC_TIMESTAMP_LEN];
        crate::timestamp::format_utc_timestamp(now, &mut ts);

        let mut produced = 0usize;
        while produced < max && self.pos <= self.end {
            // O(1) per item: `resend(pos, end)` locates `pos` via the offset table.
            // An `App` first item is always at `pos` (a gap starting at `pos` yields
            // a `GapFill` instead), so advance one past it; a `GapFill` covers
            // `[pos, new_seq)`, so resume at its `NewSeqNo`. Chunking this way yields
            // the exact same item sequence a single `resend(begin, end)` walk would.
            let Some(item) = session.journal.resend(self.pos, self.end).next() else {
                break;
            };
            let next_pos = match &item {
                ReplayItem::App(_) => self.pos.saturating_add(1),
                ReplayItem::GapFill { new_seq, .. } => *new_seq,
            };
            let ok = encode_resend_item(
                &mut writer.inner,
                &item,
                &session.config,
                &ts,
                D::BEGIN_STRING,
            );
            if ok.is_err() {
                // Buffer full. `send_app`'s headroom guarantees any single item fits
                // an *empty* writer; if it still does not, the writer is undersized —
                // a configuration error. Otherwise leave the item for the next call
                // and return what is staged.
                if writer.inner.is_empty() {
                    return Err(Error::MessageTooLarge(
                        writer.inner.remaining().saturating_add(1),
                    ));
                }
                break;
            }
            self.pos = next_pos;
            produced += 1;
        }

        if writer.inner.is_empty() {
            Ok(None)
        } else {
            Ok(Some(writer.inner.data()))
        }
    }
}

/// Owned outcome of one [`FixSession::recv_step`], so [`FixSession::recv`] can arm
/// the terminated guard before borrowing `reader` to reconstruct the message.
enum RecvStep {
    /// A typed message is ready; call [`FixSession::message`].
    Message,
    /// A clean, negotiated logout ended the session.
    LoggedOut,
    /// Nothing to surface this step (a suppressed frame, or a read timeout with no
    /// complete frame buffered); `recv` returns `Ok(None)`.
    Nothing,
}

/// Whether a socket error is a read timeout (`TimedOut`/`WouldBlock`): a
/// caller-set read timeout elapsed, not a fault.
fn is_timeout(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
    )
}

/// Write to the journal, retrying on transient standby backpressure.
///
/// `store` is one of `FixJournal::store` / `store_inbound`, `size` its frame
/// length. On [`WriteError::StandbyNotReady`] (transient backpressure) we spin
/// and retry; a [`WriteError::RecordTooLarge`] misconfiguration surfaces as
/// [`Error::MessageTooLarge`].
///
/// Unbounded on purpose. StandbyNotReady is transient backpressure the conductor
/// clears in sub-ms; the only way this spins forever is a full/failing disk,
/// which must be caught by observability. Spinning beats the alternative of
/// dropping a message from a resend/audit journal.
#[inline]
fn journal_write(
    size: usize,
    mut store: impl FnMut() -> Result<(), WriteError>,
) -> Result<(), Error> {
    loop {
        match store() {
            Ok(()) => return Ok(()),
            Err(WriteError::StandbyNotReady) => std::hint::spin_loop(),
            // Only RecordTooLarge today; WriteError is non-exhaustive, so any
            // other (non-backpressure) journal write error surfaces the same way.
            Err(_) => return Err(Error::MessageTooLarge(size)),
        }
    }
}

/// The journaling emit emitter: encodes each admin into `writer` and journals the
/// committed frame under its seqnum.
///
/// The journaled bytes are the encoded frame — including anything the venue
/// [`SessionCustomizer`] injected. That is deliberate: the outbound archive
/// matches the wire byte-for-byte, which is worth more than redacting
/// credentials from a journal that is already local to the box.
///
/// # Errors
///
/// On a per-emit basis, [`Error::MessageTooLarge`] if an encode did not fit the
/// writer — the state machine has already bumped the outbound seqnum by that
/// point, so a silently dropped message would leave the session wedged until a
/// logon or heartbeat timeout reported a cause pointing away from the encode.
/// The error surfaces instead; nothing is committed or journaled in that case.
// The return type is exactly an `Emitter` over an unnameable journaling closure;
// there is nothing to factor into a `type` alias (the closure has no name).
#[allow(clippy::type_complexity)]
fn journaling_emitter<'a, D: FixDictionary, C: SessionCustomizer>(
    writer: &'a mut MessageWriter<D, C>,
    journal: &'a mut FixJournal,
    config: &'a SessionConfig,
    now: i128,
) -> Emitter<'a, D, C, impl FnMut(u32, &[u8]) -> Result<(), Error> + 'a> {
    Emitter::new(writer, config, now, move |seq, frame| {
        journal_write(frame.len(), || journal.store(seq, frame))
    })
}

/// Copies a pre-built frame into the writer buffer for the wrapper to drain.
///
/// Unlike the original `write_through` this performs no I/O: it only stages bytes.
/// The frame must fit the *empty* buffer capacity — [`FixSession::encode_send_app`] caps
/// app frames below it, so an overflow here is an undersized writer, not a
/// fallback. Because the sans-IO core cannot flush to make room, the buffer must
/// hold the frame as-is.
fn buffer_frame(writer: &mut FrameWriter, frame: &[u8]) -> Result<(), Error> {
    if writer.remaining() < frame.len() {
        return Err(Error::MessageTooLarge(frame.len()));
    }
    let spare = writer.spare();
    spare[..frame.len()].copy_from_slice(frame);
    writer.commit(0, frame.len());
    Ok(())
}

/// Encodes one resend [`ReplayItem`] into the writer. Returns `Err(())` if it
/// does not fit the remaining buffer.
fn encode_resend_item(
    writer: &mut FrameWriter,
    item: &ReplayItem<'_>,
    config: &SessionConfig,
    ts: &[u8],
    begin_string: &'static [u8],
) -> Result<(), ()> {
    match item {
        ReplayItem::GapFill { seq, new_seq } => {
            encode_gap_fill_frame(writer, begin_string, config, ts, *seq, *new_seq)
        }
        ReplayItem::App(orig) => reframe_app(writer, orig, ts, begin_string),
    }
}

/// Writes a resend-replay `SequenceReset-GapFill` frame directly into `writer` (no
/// journaling, no customizer) — the internal replay primitive the [`ResendCursor`]
/// drives, distinct from the user-facing [`FixSession::encode_gap_fill`] send verb.
fn encode_gap_fill_frame(
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

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::time::Duration;

    use nexus_fix_codec::{
        AdminEncode, AsciiTextStr, DecodeError, FieldReader, FieldView, FixAdminMsg, FixDictionary,
        FixHeader, FixTimestamp, FrameFormatter, checksum, find_tag, format_checksum,
    };

    use super::{FixSession, PollOutcome};
    use crate::frame::{FrameReader, FrameWriter};
    use crate::framework::{CompId, Message, MessageReader, MessageWriter, SessionConfig};
    use crate::persist::FixJournal;
    use crate::session::{Emit, LogonIn, SessionState, State};

    /// Fixed UTC-unix-nanos clock. The deterministic core stamps every
    /// `SendingTime(52)` from this, so two runs of the same inputs produce
    /// byte-identical frames — no post-hoc normalization needed.
    const NOW: i128 = 1_780_505_733_000_000_000;

    /// A discarding [`Emit`]: drops every emitted admin. These rig helpers
    /// drive the raw `SessionState` only to advance sequence numbers before
    /// wrapping it in a `FixSession`; the emitted admin is not routed to the
    /// session's writer.
    struct NullEmitter;

    impl Emit for NullEmitter {
        type Error = std::convert::Infallible;
        fn emit<M: AdminEncode>(&mut self, _msg: M) -> Result<(), Self::Error> {
            Ok(())
        }
    }

    /// Drives the initiator Logon exchange on a raw `SessionState`: sends Logon
    /// (outbound seq 1) and accepts the peer's Logon at seq 1, reaching `Active`.
    fn establish_state(state: &mut SessionState) {
        state.connect(&mut NullEmitter).unwrap();
        state
            .on_logon(
                LogonIn {
                    seq: 1,
                    heart_bt_int_s: 30,
                    is_reset_seq_num: false,
                    send_reply: false,
                },
                &mut NullEmitter,
            )
            .unwrap();
    }

    // ── minimal mock dictionary (mirrors tests/transport.rs) ─────────────────

    struct MockDict;

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    enum MockMsgType {}

    struct AdminDecoder<'buf> {
        _buf: &'buf [u8],
    }

    impl<'buf> FixAdminMsg<'buf> for AdminDecoder<'buf> {
        fn decode(buf: &'buf [u8]) -> Result<Self, DecodeError> {
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
        fn sender_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>> {
            find_tag(self.buf, 0, 49).and_then(|s| FieldView::new(s, self.buf))
        }
        fn target_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>> {
            find_tag(self.buf, 0, 56).and_then(|s| FieldView::new(s, self.buf))
        }
        fn poss_dup_flag(&self) -> Option<FieldView<'buf, bool>> {
            find_tag(self.buf, 0, 43).and_then(|s| FieldView::new(s, self.buf))
        }
        fn sending_time(&self) -> Option<FieldView<'buf, FixTimestamp>> {
            None
        }
    }

    // ── test rig ─────────────────────────────────────────────────────────────

    // Engine plays initiator: our SenderCompID is INITIATOR, the peer is ACCEPTOR.
    // Inbound frames therefore carry 49=ACCEPTOR (peer's sender) and 56=INITIATOR.
    fn our_id() -> CompId {
        CompId::new(b"INITIATOR").unwrap()
    }
    fn peer_id() -> CompId {
        CompId::new(b"ACCEPTOR").unwrap()
    }

    /// RAII scratch directory. `FixJournal::open` preallocates tens of megabytes
    /// into each of these, so they must not outlive the test that made them.
    /// `Drop` also runs while unwinding, so a *failing* test cleans up too —
    /// which a manual `remove_dir_all` at the end of the body would not.
    ///
    /// Bind it to a live local (`let dir = tmp_dir(..)`), never `let _ = ..`, or
    /// the directory is removed before the test can use it.
    struct TempDir(PathBuf);

    impl TempDir {
        fn new(suffix: &str) -> Self {
            let mut p = std::env::temp_dir();
            p.push(format!(
                "nexus_fix_session_{}_{}",
                std::process::id(),
                suffix
            ));
            // A previous run killed by a signal can leave the tree behind, and
            // PIDs get recycled -- start from a clean slate.
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

    /// Build a stored app frame at `seq` with a filler `58=Text` field whose
    /// length is derived from `seq` so frame sizes vary across the range. The
    /// original `SendingTime` (52) is a fixed literal (comes from stored bytes,
    /// not the resend clock), so it survives into `OrigSendingTime` (122)
    /// identically in both runs.
    fn app_frame(seq: u32, buf: &mut [u8]) -> usize {
        let mut seq_buf = [0u8; 10];
        let seq_n = nexus_fix_codec::encode_fix_uint(seq, &mut seq_buf);
        // Filler 6..=26 bytes: varies the reframed size around the tiny-buffer
        // boundary without ever exceeding `tiny_cap - REFRAME_HEADROOM`.
        let fill_len = 6 + (seq as usize % 21);
        let filler = vec![b'x'; fill_len];
        let mut fmt = FrameFormatter::new(buf, b"FIX.4.4", b"D");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, our_id().as_bytes()); // engine is the SENDER of stored msgs
        fmt.field(56, peer_id().as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(58, &filler);
        let (start, len) = fmt.finish().unwrap();
        buf.copy_within(start..start + len, 0);
        len
    }

    /// Encode an inbound ResendRequest (35=2) from the peer covering `[begin,end]`
    /// at MsgSeqNum `seq`.
    fn resend_request_frame(seq: u32, begin: u32, end: u32, buf: &mut [u8]) -> usize {
        let mut nb = [0u8; 10];
        let mut bb = [0u8; 10];
        let mut eb = [0u8; 10];
        let n = nexus_fix_codec::encode_fix_uint(seq, &mut nb);
        let bn = nexus_fix_codec::encode_fix_uint(begin, &mut bb);
        let en = nexus_fix_codec::encode_fix_uint(end, &mut eb);
        let mut fmt = FrameFormatter::new(buf, b"FIX.4.4", b"2");
        fmt.field(34, &nb[..n]);
        fmt.field(49, peer_id().as_bytes()); // peer is the SENDER of the request
        fmt.field(56, our_id().as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(7, &bb[..bn]);
        fmt.field(16, &eb[..en]);
        let (start, len) = fmt.finish().unwrap();
        buf.copy_within(start..start + len, 0);
        len
    }

    /// Number of stored app messages and the two interior holes (gap-fills).
    const N: u32 = 30;
    const HOLE_A: u32 = 10;
    const HOLE_B: u32 = 20;

    /// Test bundle over the three-object API: the sans-IO `FixSession` brain plus
    /// its caller-held `reader`/`writer`. The thin methods forward to
    /// `session.poll(&mut reader, &mut writer)` / `session.message(&reader)` and
    /// the reader/writer byte seam, so a test body reads like the pre-un-nesting
    /// one-object form while exercising the split API underneath.
    struct Rig<D: FixDictionary> {
        session: FixSession<D>,
        reader: MessageReader<D>,
        writer: MessageWriter<D>,
    }

    impl<D: FixDictionary> Rig<D> {
        fn read_spare(&mut self) -> &mut [u8] {
            self.reader.spare()
        }
        fn read_filled(&mut self, n: usize) {
            self.reader.filled(n);
        }
        fn outbound(&self) -> &[u8] {
            self.writer.data()
        }
        fn advance_outbound(&mut self, n: usize) {
            self.writer.advance(n);
        }
        fn has_outbound(&self) -> bool {
            !self.writer.is_empty()
        }
        fn poll(&mut self) -> Result<PollOutcome, super::Error> {
            self.session.poll(&mut self.reader, &mut self.writer, NOW)
        }
        fn message(&self) -> Message<'_, D> {
            self.session.message(&self.reader)
        }
        fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), super::Error> {
            self.session.encode_send_app(&mut self.writer, seq, frame)
        }
    }

    /// Build an `Active` [`Rig`] whose outbound journal holds app frames for
    /// seqs `1..=N` except `HOLE_A`/`HOLE_B`, ready to receive a ResendRequest.
    ///
    /// `writer_cap` sizes only the outbound writer — the shared journal content
    /// is byte-identical across runs, and both stamp the resend `SendingTime` from
    /// the same fixed [`NOW`], so the two resends are byte-identical.
    fn build_session(dir: &Path, writer_cap: usize) -> Rig<MockDict> {
        let reader = MessageReader::with_frame_reader(FrameReader::builder().build());
        let writer = MessageWriter::with_frame_writer(
            FrameWriter::builder().buffer_capacity(writer_cap).build(),
        );
        let mut state = SessionState::new(Duration::from_secs(30));
        // Establish (initiator): Logon consumes outbound seq 1, peer's Logon at
        // seq 1 advances next_inbound to 2 and moves to Active.
        establish_state(&mut state);
        // Align outbound with the journal we are about to fill (next = N + 1). The
        // window (256) comfortably exceeds N, so `low_water` saturates to 0 and the
        // whole `[1, N]` range stays providable. Keep next_inbound at 2 for the
        // incoming ResendRequest.
        state.reset_seq_nums(N + 1, 2);

        let journal = FixJournal::open(dir, 0, 256).unwrap();
        let session = FixSession::new(
            state,
            SessionConfig {
                sender: our_id(),
                target: peer_id(),
            },
            journal,
        );
        let mut rig = Rig {
            session,
            reader,
            writer,
        };

        // Store the app messages. `send_app` also stages the frame in the writer;
        // drain it so only the later resend output is captured.
        let mut buf = vec![0u8; 512];
        for seq in 1..=N {
            if seq == HOLE_A || seq == HOLE_B {
                continue; // interior hole → gap-fill on resend
            }
            let len = app_frame(seq, &mut buf);
            rig.send_app(seq, &buf[..len]).unwrap();
            let n = rig.outbound().len();
            rig.advance_outbound(n);
        }
        assert!(!rig.has_outbound(), "writer must be drained before resend");
        rig
    }

    /// Drive a ResendRequest for `[1, N]` to completion by pumping the surfaced
    /// [`ResendCursor`], concatenating every yielded byte. `max_per_batch` is the
    /// item cap per [`next_batch`](super::ResendCursor::next_batch) call (the
    /// writer capacity also bounds it). Returns `(stream, batch_count)` — the number
    /// of non-empty batches yielded before Done.
    fn drive_resend_stream(rig: &mut Rig<MockDict>, max_per_batch: usize) -> (Vec<u8>, usize) {
        let mut req = vec![0u8; 256];
        let len = resend_request_frame(2, 1, N, &mut req);
        let spare = rig.read_spare();
        spare[..len].copy_from_slice(&req[..len]);
        rig.read_filled(len);

        let outcome = rig.poll().expect("poll");
        assert_eq!(
            outcome,
            PollOutcome::Message,
            "an in-window ResendRequest must surface a Message"
        );
        // The cursor is `Copy`, so binding it out of the reader-borrowing `Message`
        // carries no borrow — `session`/`writer` are free to pump it.
        let mut cursor = match rig.message() {
            Message::ResendRequest { cursor } => cursor,
            other => panic!("expected ResendRequest, got {}", variant(&Some(other))),
        };

        let mut stream = Vec::new();
        let mut batches = 0usize;
        while let Some(bytes) = cursor
            .next_batch(&mut rig.session, &mut rig.writer, NOW, max_per_batch)
            .expect("next_batch")
        {
            stream.extend_from_slice(bytes);
            batches += 1;
        }
        (stream, batches)
    }

    /// Split a concatenated stream into frames using the production frame reader
    /// (self-delimiting via BodyLength, checksum-validated).
    fn split_frames(stream: &[u8]) -> Vec<Vec<u8>> {
        let mut reader = FrameReader::builder().build();
        reader.read(stream).expect("stream fits reader");
        let mut frames = Vec::new();
        loop {
            match reader.next() {
                Ok(Some(frame)) => frames.push(frame.to_vec()),
                Ok(None) => break,
                Err(e) => panic!("frame split error: {e:?}"),
            }
        }
        frames
    }

    /// Oracle: a resend that overflows a tiny writer many times (drain → resume)
    /// must produce byte-for-byte the same output as the same resend into a
    /// writer large enough to complete in a single pass. Divergence would mean
    /// the resumable path skipped, duplicated, split, reordered, or mis-reframed
    /// an item across a resume boundary.
    ///
    /// Both runs stamp the resend `SendingTime(52)` from the same fixed [`NOW`]
    /// (the core is a pure function of `(journal, now)`), so the streams are
    /// byte-identical directly — no SendingTime normalization needed.
    #[test]
    fn resumable_resend_matches_single_pass() {
        let dir_big = tmp_dir("resume_big");
        let dir_small = tmp_dir("resume_small");

        // Large writer, unbounded batch: the whole resend drains in one batch.
        let mut big = build_session(dir_big.path(), 64 * 1024);
        let (big_stream, big_batches) = drive_resend_stream(&mut big, usize::MAX);
        assert_eq!(
            big_batches, 1,
            "large-writer unbounded batch must drain the whole resend in one call"
        );

        // Tiny writer, unbounded batch: capacity stops each batch at ~1 reframed
        // item → many capacity-bounded resume boundaries. 200 bytes holds one
        // reframed item (< ~180) but never two (>= ~250), and comfortably exceeds
        // the largest single frame so the empty-buffer MessageTooLarge guard never
        // fires.
        let mut small = build_session(dir_small.path(), 200);
        let (small_stream, small_batches) = drive_resend_stream(&mut small, usize::MAX);

        // The capacity-bounded resume path was actually exercised, not trivially
        // skipped.
        assert!(
            small_batches >= 5,
            "tiny-writer resend must resume across many batches (got {small_batches})"
        );

        // Strong oracle: byte-identical directly (same fixed `now` → same 52).
        let big_frames = split_frames(&big_stream);
        let small_frames = split_frames(&small_stream);
        assert_eq!(
            big_frames.len(),
            small_frames.len(),
            "frame count diverged: single-pass {} vs resumable {}",
            big_frames.len(),
            small_frames.len()
        );
        for (i, (b, s)) in big_frames.iter().zip(small_frames.iter()).enumerate() {
            assert_eq!(
                b,
                s,
                "frame {i} diverged between single-pass and resumable resend\n \
                 single-pass: {}\n resumable:   {}",
                String::from_utf8_lossy(b),
                String::from_utf8_lossy(s),
            );
        }

        // Structural spot-checks on the single-pass stream.
        // Range [1,30] with holes at 10 and 20:
        //   App(1..9), GapFill(10→11), App(11..19), GapFill(20→21), App(21..30).
        // 28 app reframes + 2 coalesced gap-fills = 30 frames.
        assert_eq!(big_frames.len(), 30, "expected 28 apps + 2 gap-fills");

        let mut app_seqs = Vec::new();
        let mut gapfills = Vec::new();
        for f in &big_frames {
            let msg_type = find_tag(f, 0, 35).map(|s| s.slice(f)).unwrap();
            // Every reframed item and every gap-fill carries PossDupFlag=Y.
            let poss_dup = find_tag(f, 0, 43).map(|s| s.slice(f));
            assert_eq!(poss_dup, Some(b"Y".as_ref()), "resend frame must set 43=Y");
            let seq: u32 = find_tag(f, 0, 34)
                .and_then(|s| FieldView::new(s, f.as_slice()))
                .unwrap()
                .get();
            match msg_type {
                b"4" => {
                    // GapFill carries NewSeqNo(36) and GapFillFlag(123)=Y.
                    let gf = find_tag(f, 0, 123).map(|s| s.slice(f));
                    assert_eq!(gf, Some(b"Y".as_ref()), "gap-fill must set 123=Y");
                    let new_seq: u32 = find_tag(f, 0, 36)
                        .and_then(|s| FieldView::new(s, f.as_slice()))
                        .unwrap()
                        .get();
                    gapfills.push((seq, new_seq));
                }
                b"D" => {
                    // Reframed app preserves OrigSendingTime(122) from the store.
                    let orig = find_tag(f, 0, 122).map(|s| s.slice(f));
                    assert_eq!(
                        orig,
                        Some(b"20260615-12:00:00.000".as_ref()),
                        "reframed app must carry 122=<original 52>"
                    );
                    // Field 58 filler must survive the reframe.
                    assert!(find_tag(f, 0, 58).is_some(), "reframed app dropped tag 58");
                    app_seqs.push(seq);
                }
                other => panic!("unexpected resend msg type {:?}", other),
            }
        }

        // Exactly the app seqnums we stored, in order.
        let expected_apps: Vec<u32> = (1..=N).filter(|s| *s != HOLE_A && *s != HOLE_B).collect();
        assert_eq!(
            app_seqs, expected_apps,
            "app reframe seqnums or order wrong"
        );
        // Gap-fills coalesce each hole up to the next stored seqnum.
        assert_eq!(
            gapfills,
            vec![(HOLE_A, HOLE_A + 1), (HOLE_B, HOLE_B + 1)],
            "gap-fill (seq,new_seq) wrong"
        );

        // Wire count must include a FieldReader-visible field parse for sanity:
        // every frame has tags 8/34/52 present.
        for f in &big_frames {
            let tags: Vec<u32> = FieldReader::new(f, 0).map(|fld| fld.tag).collect();
            assert!(tags.contains(&8) && tags.contains(&34) && tags.contains(&52));
        }
    }

    // ── providability check ──────────────────────────────────────────────────

    /// Build an `Active` [`Rig`] whose outbound journal has `window` retained slots
    /// and holds app frames for seqs `1..=stored_max` except `hole`. With a small
    /// `window` and `stored_max > window`, the oldest seqnums have rotated off, so
    /// the retained window is `[stored_max + 1 - window, stored_max]`. next_inbound
    /// is 2, ready for a ResendRequest at seq 2.
    fn windowed_session(dir: &Path, window: usize, stored_max: u32, hole: u32) -> Rig<MockDict> {
        let reader = MessageReader::with_frame_reader(FrameReader::builder().build());
        let writer = MessageWriter::with_frame_writer(
            FrameWriter::builder().buffer_capacity(64 * 1024).build(),
        );
        let mut state = SessionState::new(Duration::from_secs(30));
        establish_state(&mut state);
        state.reset_seq_nums(stored_max + 1, 2);

        let journal = FixJournal::open(dir, 0, window).unwrap();
        let session = FixSession::new(
            state,
            SessionConfig {
                sender: our_id(),
                target: peer_id(),
            },
            journal,
        );
        let mut rig = Rig {
            session,
            reader,
            writer,
        };

        let mut buf = vec![0u8; 512];
        for seq in 1..=stored_max {
            if seq == hole {
                continue;
            }
            let len = app_frame(seq, &mut buf);
            rig.send_app(seq, &buf[..len]).unwrap();
            let n = rig.outbound().len();
            rig.advance_outbound(n);
        }
        assert!(!rig.has_outbound(), "writer must be drained before resend");
        rig
    }

    /// Feed an inbound ResendRequest `[begin, end]` at MsgSeqNum `seq` and poll it.
    fn feed_resend(rig: &mut Rig<MockDict>, seq: u32, begin: u32, end: u32) -> PollOutcome {
        let mut req = vec![0u8; 256];
        let len = resend_request_frame(seq, begin, end, &mut req);
        let spare = rig.read_spare();
        spare[..len].copy_from_slice(&req[..len]);
        rig.read_filled(len);
        rig.poll().expect("poll")
    }

    /// A ResendRequest fully inside the retained window surfaces a cursor that pumps
    /// to Done, replaying stored apps as PossDup and the interior hole as a
    /// coalesced gap-fill.
    #[test]
    fn providable_resend_surfaces_cursor_and_pumps_to_done() {
        // window 8, stored 1..=20 except 17 → retained [13, 20], hole at 17.
        let dir = tmp_dir("providable_cursor");
        let mut rig = windowed_session(dir.path(), 8, 20, 17);

        assert_eq!(feed_resend(&mut rig, 2, 15, 20), PollOutcome::Message);
        let mut cursor = match rig.message() {
            Message::ResendRequest { cursor } => cursor,
            other => panic!(
                "expected ResendRequest cursor, got {}",
                variant(&Some(other))
            ),
        };
        assert_eq!((cursor.begin(), cursor.end()), (15, 20), "cursor range");

        // Pump one item per `next` to Done.
        let mut stream = Vec::new();
        while let Some(bytes) = cursor
            .next(&mut rig.session, &mut rig.writer, NOW)
            .expect("next")
        {
            stream.extend_from_slice(bytes);
        }
        let frames = split_frames(&stream);

        let mut apps = Vec::new();
        let mut gapfills = Vec::new();
        for f in &frames {
            // Every replayed frame carries PossDupFlag=Y.
            assert_eq!(
                find_tag(f, 0, 43).map(|s| s.slice(f)),
                Some(b"Y".as_ref()),
                "resend frame must set 43=Y"
            );
            let seq: u32 = find_tag(f, 0, 34)
                .and_then(|s| FieldView::new(s, f.as_slice()))
                .unwrap()
                .get();
            match find_tag(f, 0, 35).map(|s| s.slice(f)).unwrap() {
                b"4" => {
                    assert_eq!(
                        find_tag(f, 0, 123).map(|s| s.slice(f)),
                        Some(b"Y".as_ref()),
                        "gap-fill must set 123=Y"
                    );
                    let new_seq: u32 = find_tag(f, 0, 36)
                        .and_then(|s| FieldView::new(s, f.as_slice()))
                        .unwrap()
                        .get();
                    gapfills.push((seq, new_seq));
                }
                b"D" => apps.push(seq),
                other => panic!("unexpected resend msg type {other:?}"),
            }
        }
        assert_eq!(apps, vec![15, 16, 18, 19, 20], "app replay seqnums/order");
        assert_eq!(
            gapfills,
            vec![(17, 18)],
            "hole 17 must coalesce to a gap-fill"
        );
    }

    /// `EndSeqNo=0` (open-ended) is clamped to the journal high-water and, when the
    /// clamped range is retained, surfaces a cursor over `[begin, high_water]`.
    #[test]
    fn open_ended_resend_clamps_to_high_water() {
        // window 8, stored 1..=20 (no hole) → retained [13, 20], high_water 20.
        let dir = tmp_dir("open_ended_clamp");
        let mut rig = windowed_session(dir.path(), 8, 20, 0);

        assert_eq!(feed_resend(&mut rig, 2, 15, 0), PollOutcome::Message);
        match rig.message() {
            Message::ResendRequest { cursor } => {
                assert_eq!(
                    (cursor.begin(), cursor.end()),
                    (15, 20),
                    "EndSeqNo=0 must clamp end to high_water"
                );
            }
            other => panic!(
                "expected ResendRequest cursor, got {}",
                variant(&Some(other))
            ),
        }
    }

    /// A `BeginSeqNo` below the retained low-water (rotated off) surfaces
    /// `ResendOutOfRange` — no cursor — carrying both water marks.
    #[test]
    fn resend_begin_below_low_water_is_out_of_range() {
        // window 8, stored 1..=20 → retained [13, 20]; begin 1 < low_water 13.
        let dir = tmp_dir("begin_below_low");
        let mut rig = windowed_session(dir.path(), 8, 20, 0);

        assert_eq!(feed_resend(&mut rig, 2, 1, 20), PollOutcome::Message);
        match rig.message() {
            Message::ResendOutOfRange {
                begin,
                end,
                low_water,
                high_water,
            } => assert_eq!((begin, end, low_water, high_water), (1, 20, 13, 20)),
            other => panic!("expected ResendOutOfRange, got {}", variant(&Some(other))),
        }
    }

    /// A resolved `EndSeqNo` above the high-water (peer ahead of us) surfaces
    /// `ResendOutOfRange` — no cursor — even when `begin` is retained.
    #[test]
    fn resend_end_above_high_water_is_out_of_range() {
        // window 8, stored 1..=20 → retained [13, 20]; end 25 > high_water 20.
        let dir = tmp_dir("end_above_high");
        let mut rig = windowed_session(dir.path(), 8, 20, 0);

        assert_eq!(feed_resend(&mut rig, 2, 15, 25), PollOutcome::Message);
        match rig.message() {
            Message::ResendOutOfRange {
                begin,
                end,
                low_water,
                high_water,
            } => assert_eq!((begin, end, low_water, high_water), (15, 25, 13, 20)),
            other => panic!("expected ResendOutOfRange, got {}", variant(&Some(other))),
        }
    }

    // ── SequenceReset send helpers: exact-frame byte assertions ──────────────

    /// Build the exact admin frame the engine's emit path produces for MsgType
    /// `msg_type` at `seq`, with the session header (34/49/56/52) followed by
    /// `body` fields in order. Mirrors `write_admin_header` + the body encoder so a
    /// byte-for-byte `assert_eq!` pins the emitted frame (incl. field presence,
    /// order, `BodyLength`, and `CheckSum`).
    fn expected_admin_frame(
        msg_type: &[u8],
        seq: u32,
        ts: &[u8],
        body: &[(u32, &[u8])],
    ) -> Vec<u8> {
        let mut seq_buf = [0u8; 10];
        let seq_n = nexus_fix_codec::encode_fix_uint(seq, &mut seq_buf);
        let mut buf = [0u8; 256];
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", msg_type);
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, our_id().as_bytes()); // engine is the SENDER
        fmt.field(56, peer_id().as_bytes());
        fmt.field(52, ts);
        for (tag, val) in body {
            fmt.field(*tag, val);
        }
        let (start, len) = fmt.finish().unwrap();
        buf[start..start + len].to_vec()
    }

    /// `sequence_reset` (Reset mode) emits a `SequenceReset` with `GapFillFlag=N`,
    /// **no** `PossDupFlag`, `MsgSeqNum` = the allocated next outbound seqnum, and
    /// `NewSeqNo` = `new_seq` — and it consumes/advances the outbound seqnum and
    /// journals (a fresh outbound admin).
    #[test]
    fn sequence_reset_reset_mode_byte_exact() {
        let dir = tmp_dir("seqreset_reset_bytes");
        let mut rig = active_session(dir.path(), 4096);
        // After establish: state next_outbound = 2 (Logon consumed seq 1).
        assert_eq!(rig.session.state().next_outbound_seq(), 2);
        let journal_before = rig.session.journal.next_outbound();

        rig.session
            .encode_sequence_reset(&mut rig.writer, NOW, 100)
            .unwrap();

        let mut ts = [0u8; crate::timestamp::UTC_TIMESTAMP_LEN];
        crate::timestamp::format_utc_timestamp(NOW, &mut ts);
        // Reset mode: MsgSeqNum = 2 (allocated), 123=N, 36=100, and NO 43.
        let expected = expected_admin_frame(b"4", 2, &ts, &[(123, b"N"), (36, b"100")]);
        assert_eq!(
            rig.outbound(),
            expected.as_slice(),
            "reset-mode SequenceReset frame bytes"
        );
        assert!(
            find_tag(rig.outbound(), 0, 43).is_none(),
            "reset mode must not set PossDupFlag(43)"
        );

        // Reset mode allocates + advances the outbound seqnum, and journals it.
        assert_eq!(
            rig.session.state().next_outbound_seq(),
            3,
            "reset mode must advance next_outbound"
        );
        assert!(
            rig.session.journal.next_outbound() > journal_before,
            "reset mode must journal (advancing the journal's next_outbound)"
        );
    }

    /// `gap_fill` (GapFill mode) emits a `SequenceReset` with `PossDupFlag=Y` +
    /// `GapFillFlag=Y`, `MsgSeqNum` = `from_seq` (**not** allocated), and `NewSeqNo`
    /// = `new_seq` — and it neither advances the outbound seqnum nor journals.
    #[test]
    fn gap_fill_mode_byte_exact() {
        let dir = tmp_dir("gapfill_bytes");
        let mut rig = active_session(dir.path(), 4096);
        assert_eq!(rig.session.state().next_outbound_seq(), 2);
        let journal_before = rig.session.journal.next_outbound();

        rig.session
            .encode_gap_fill(&mut rig.writer, NOW, 5, 10)
            .unwrap();

        let mut ts = [0u8; crate::timestamp::UTC_TIMESTAMP_LEN];
        crate::timestamp::format_utc_timestamp(NOW, &mut ts);
        // GapFill mode: MsgSeqNum = 5 (from_seq), 43=Y, 123=Y, 36=10.
        let expected = expected_admin_frame(b"4", 5, &ts, &[(43, b"Y"), (123, b"Y"), (36, b"10")]);
        assert_eq!(
            rig.outbound(),
            expected.as_slice(),
            "gap-fill SequenceReset frame bytes"
        );

        // GapFill neither allocates/advances the outbound seqnum nor journals.
        assert_eq!(
            rig.session.state().next_outbound_seq(),
            2,
            "gap_fill must not advance next_outbound"
        );
        assert_eq!(
            rig.session.journal.next_outbound(),
            journal_before,
            "gap_fill must not journal (would rewind next_outbound)"
        );
    }

    #[test]
    fn reframe_stays_within_headroom() {
        // A resend reframe adds PossDupFlag (43=Y), OrigSendingTime (122=...),
        // and a little BodyLength growth. It must never grow a message by more
        // than REFRAME_HEADROOM, so a stored app frame always reframes back into
        // the pre-allocated writer buffer without a runtime allocation.
        let mut orig_buf = [0u8; 512];
        let (s, l) = {
            let mut fmt = FrameFormatter::new(&mut orig_buf, b"FIX.4.4", b"D");
            fmt.field(34, b"5");
            fmt.field(49, b"SENDER");
            fmt.field(56, b"TARGET");
            fmt.field(52, b"20260101-00:00:00.000");
            fmt.field(11, b"ORDER-1");
            fmt.finish().unwrap()
        };
        let orig = &orig_buf[s..s + l];

        let ts = b"20260102-12:34:56.789";
        let mut out = [0u8; 1024];
        let (_start, len) = super::reframe_app_into(&mut out, orig, ts, b"FIX.4.4").unwrap();

        assert!(
            len <= orig.len() + super::REFRAME_HEADROOM,
            "reframe grew message by {} bytes, exceeding REFRAME_HEADROOM ({})",
            len - orig.len(),
            super::REFRAME_HEADROOM
        );
    }

    // ── strict dictionary: admin decode fails on a missing required field ─────

    /// A dictionary whose admin decode rejects a Logon that lacks HeartBtInt
    /// (tag 108). Real generated dictionaries fail the typed decode when a
    /// required field is absent; `MockDict`'s always-`Ok` decoder cannot model
    /// that, so this second dictionary exercises the malformed-admin path.
    struct StrictDict;

    struct StrictAdmin<'buf> {
        _buf: &'buf [u8],
    }

    impl<'buf> FixAdminMsg<'buf> for StrictAdmin<'buf> {
        fn decode(buf: &'buf [u8]) -> Result<Self, DecodeError> {
            // Require HeartBtInt(108) — a well-formed Logon carries it. Its
            // absence stands in for any required-field violation the typed
            // decoder would reject.
            if find_tag(buf, 0, 108).is_some() {
                Ok(Self { _buf: buf })
            } else {
                Err(DecodeError::Truncated)
            }
        }
    }

    impl FixDictionary for StrictDict {
        type MsgType = MockMsgType;
        type Header<'buf> = MockHeader<'buf>;
        type Logon<'buf> = StrictAdmin<'buf>;
        type Logout<'buf> = StrictAdmin<'buf>;
        type Heartbeat<'buf> = StrictAdmin<'buf>;
        type TestRequest<'buf> = StrictAdmin<'buf>;
        type ResendRequest<'buf> = StrictAdmin<'buf>;
        type SequenceReset<'buf> = StrictAdmin<'buf>;
        type Reject<'buf> = StrictAdmin<'buf>;
        const BEGIN_STRING: &'static [u8] = b"FIX.4.4";
        fn is_admin(_: MockMsgType) -> bool {
            false
        }
    }

    /// Build a well-framed Logon (35=A) from the peer at `seq`, optionally
    /// omitting HeartBtInt(108). Comp IDs are peer→engine (49=ACCEPTOR,
    /// 56=INITIATOR) so the frame passes comp-id validation.
    fn peer_logon_frame(seq: u32, with_hbi: bool, buf: &mut [u8]) -> usize {
        let mut seq_buf = [0u8; 10];
        let seq_n = nexus_fix_codec::encode_fix_uint(seq, &mut seq_buf);
        let mut fmt = FrameFormatter::new(buf, b"FIX.4.4", b"A");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, peer_id().as_bytes()); // peer is the SENDER of the Logon
        fmt.field(56, our_id().as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        if with_hbi {
            fmt.field(108, b"30");
        }
        let (start, len) = fmt.finish().unwrap();
        buf.copy_within(start..start + len, 0);
        len
    }

    /// A well-framed, comp-id-valid, valid-seqnum admin message (Logon) whose
    /// *typed* decode fails (missing a required field) must surface as
    /// `Error::Protocol(MalformedMessage)` — never panic. Before the fix,
    /// `process_frame` set `PendingKind` from tag 35 alone and never ran the
    /// typed decode, so `message()`'s `.expect("frame decoded in poll")` panicked
    /// the process on a malformed admin. Regression for the sans-IO refactor
    /// (this is what the pre-refactor transport returned via its per-arm
    /// decode-then-`map_err`).
    #[test]
    fn malformed_admin_errors_not_panics() {
        use crate::framework::SessionError;

        let dir = tmp_dir("malformed_admin");

        let reader = MessageReader::with_frame_reader(FrameReader::builder().build());
        let writer =
            MessageWriter::with_frame_writer(FrameWriter::builder().buffer_capacity(4096).build());
        let mut state = SessionState::new(Duration::from_secs(30));
        // Initiate: engine sends Logon (outbound seq 1), moves to LogonSent, and
        // expects the peer's Logon at inbound seq 1.
        state.connect(&mut NullEmitter).unwrap();

        let journal = FixJournal::open(dir.path(), 0, 256).unwrap();
        let mut rig: Rig<StrictDict> = Rig {
            session: FixSession::new(
                state,
                SessionConfig {
                    sender: our_id(),
                    target: peer_id(),
                },
                journal,
            ),
            reader,
            writer,
        };
        // Drain the opening Logon the engine staged so only inbound is exercised.
        let n = rig.outbound().len();
        rig.advance_outbound(n);

        // Sanity: the *same* frame WITH tag 108 decodes and surfaces as a Message
        // (guards against the frame being rejected for an unrelated reason).
        {
            let dir_ok = tmp_dir("malformed_admin_ok");
            let reader = MessageReader::with_frame_reader(FrameReader::builder().build());
            let writer = MessageWriter::with_frame_writer(
                FrameWriter::builder().buffer_capacity(4096).build(),
            );
            let mut state = SessionState::new(Duration::from_secs(30));
            state.connect(&mut NullEmitter).unwrap();
            let journal = FixJournal::open(dir_ok.path(), 0, 256).unwrap();
            let mut ok_rig: Rig<StrictDict> = Rig {
                session: FixSession::new(
                    state,
                    SessionConfig {
                        sender: our_id(),
                        target: peer_id(),
                    },
                    journal,
                ),
                reader,
                writer,
            };
            let n = ok_rig.outbound().len();
            ok_rig.advance_outbound(n);

            let mut buf = vec![0u8; 256];
            let len = peer_logon_frame(1, true, &mut buf);
            let spare = ok_rig.read_spare();
            spare[..len].copy_from_slice(&buf[..len]);
            ok_rig.read_filled(len);
            assert_eq!(
                ok_rig.poll().expect("valid Logon must not error"),
                PollOutcome::Message,
                "a well-formed Logon (with tag 108) must surface as a Message"
            );
        }

        // The malformed Logon: missing HeartBtInt(108) → typed decode fails.
        let mut buf = vec![0u8; 256];
        let len = peer_logon_frame(1, false, &mut buf);
        let spare = rig.read_spare();
        spare[..len].copy_from_slice(&buf[..len]);
        rig.read_filled(len);

        // Drive poll → message exactly as `recv` does. WITH the fix, `poll` returns
        // the error before ever yielding `Message`, so `message()` is never
        // reached. WITHOUT the fix, `poll` yields `Message` and the `message()`
        // call below panics on `.expect("frame decoded in poll")` — this call is
        // what makes the regression observable end-to-end.
        match rig.poll() {
            Err(super::Error::Protocol(SessionError::MalformedMessage)) => {}
            Ok(PollOutcome::Message) => {
                let _ = rig.message(); // panics without the fix
                panic!("malformed admin surfaced as a Message instead of an error");
            }
            other => {
                panic!("malformed admin must return Protocol(MalformedMessage), got {other:?}")
            }
        }
    }

    /// Build a well-framed, comp-id-valid frame that is MISSING `MsgType(35)` at
    /// `seq`. `FrameFormatter` always writes 35, so the frame is assembled by
    /// hand and framed with the codec's own checksum helper. It frames cleanly
    /// (8/9/10 valid) but trips `process_frame`'s missing-tag-35 reject path.
    fn peer_frame_without_msg_type(seq: u32, out: &mut [u8]) -> usize {
        let push = |b: &mut Vec<u8>, tag: &[u8], val: &[u8]| {
            b.extend_from_slice(tag);
            b.push(b'=');
            b.extend_from_slice(val);
            b.push(0x01);
        };

        // Body: everything the BodyLength counts — no 35.
        let mut body = Vec::new();
        let seq_s = seq.to_string();
        push(&mut body, b"34", seq_s.as_bytes());
        push(&mut body, b"49", peer_id().as_bytes()); // peer is the SENDER
        push(&mut body, b"56", our_id().as_bytes());
        push(&mut body, b"52", b"20260615-12:00:00.000");

        let mut msg = Vec::new();
        push(&mut msg, b"8", b"FIX.4.4");
        let bl = body.len().to_string();
        push(&mut msg, b"9", bl.as_bytes());
        msg.extend_from_slice(&body);
        // Checksum covers 8=… through the end of the body (before 10=).
        let sum = checksum(&msg);
        push(&mut msg, b"10", &format_checksum(sum));

        out[..msg.len()].copy_from_slice(&msg);
        msg.len()
    }

    /// The non-journaling emit site: `process_frame`'s missing-tag-35 path emits a
    /// Reject through an `Emitter` with a no-op `after` (no journaling). If that
    /// Reject does not fit the writer, the failure must surface — not be swallowed
    /// into `Ok`, which would leave the peer's malformed frame silently
    /// unanswered. A deliberately tiny writer forces the Reject encode to fail.
    #[test]
    fn missing_msg_type_reject_encode_overflow_surfaces_error() {
        let dir = tmp_dir("missing35_overflow");

        let reader = MessageReader::with_frame_reader(FrameReader::builder().build());
        // 40 bytes cannot hold a Reject frame (~70+ bytes), so the encode-only
        // reject closure fails and must propagate the error out of `poll`.
        let writer =
            MessageWriter::with_frame_writer(FrameWriter::builder().buffer_capacity(40).build());
        let mut state = SessionState::new(Duration::from_secs(30));
        // Establish on the raw state (drop_emit) so the opening Logon never
        // touches the tiny writer; the session starts Active with a pristine,
        // empty buffer and `next_inbound == 2`. The reject is only emitted from
        // Active/Resending/LogoutPending, so the session must be past the
        // handshake for the missing-35 path to actually encode a Reject.
        establish_state(&mut state);

        let journal = FixJournal::open(dir.path(), 0, 256).unwrap();
        let mut rig: Rig<MockDict> = Rig {
            session: FixSession::new(
                state,
                SessionConfig {
                    sender: our_id(),
                    target: peer_id(),
                },
                journal,
            ),
            reader,
            writer,
        };

        // Inbound seq 2 matches `next_inbound`, so `validate_seq` proceeds to the
        // reject emit rather than gap-filling or disconnecting.
        let mut buf = vec![0u8; 256];
        let len = peer_frame_without_msg_type(2, &mut buf);
        let spare = rig.read_spare();
        spare[..len].copy_from_slice(&buf[..len]);
        rig.read_filled(len);

        match rig.poll() {
            Err(super::Error::MessageTooLarge(_)) => {}
            other => panic!(
                "missing-tag-35 reject that overflows the writer must surface \
                 MessageTooLarge, got {other:?}"
            ),
        }
    }

    // ── Fix B part 1: compaction when the buffer is full below the threshold ──

    /// Build an inbound app frame (35=D) from the peer at `seq` with a `58=Text`
    /// filler of `fill` bytes. Comp IDs are peer→engine (49=ACCEPTOR,56=INITIATOR)
    /// so it passes comp-id validation on an Active session.
    fn inbound_app_frame(seq: u32, fill: usize, buf: &mut [u8]) -> usize {
        let mut seq_buf = [0u8; 10];
        let seq_n = nexus_fix_codec::encode_fix_uint(seq, &mut seq_buf);
        let filler = vec![b'y'; fill];
        let mut fmt = FrameFormatter::new(buf, b"FIX.4.4", b"D");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, peer_id().as_bytes());
        fmt.field(56, our_id().as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(58, &filler);
        let (start, len) = fmt.finish().unwrap();
        buf.copy_within(start..start + len, 0);
        len
    }

    /// Build an Active [`Rig`] (post-logon, `next_inbound == 2`) with the given
    /// reader capacity, ready to receive inbound app frames.
    fn active_session(dir: &Path, reader_cap: usize) -> Rig<MockDict> {
        let reader = MessageReader::with_frame_reader(
            FrameReader::builder().buffer_capacity(reader_cap).build(),
        );
        let writer =
            MessageWriter::with_frame_writer(FrameWriter::builder().buffer_capacity(4096).build());
        let mut state = SessionState::new(Duration::from_secs(30));
        establish_state(&mut state); // peer Logon at seq 1 → Active, next_inbound = 2
        let journal = FixJournal::open(dir, 0, 256).unwrap();
        let mut rig = Rig {
            session: FixSession::new(
                state,
                SessionConfig {
                    sender: our_id(),
                    target: peer_id(),
                },
                journal,
            ),
            reader,
            writer,
        };
        let n = rig.outbound().len();
        rig.advance_outbound(n); // drain the engine's opening Logon
        rig
    }

    /// Fix B: when the reader buffer is full but consumed below the compaction
    /// threshold (`remaining() == 0 && !should_compact()`), `read_spare` must
    /// still compact so the spare is non-empty — otherwise the wrapper reads into
    /// a zero-length slice and false-EOFs. A large frame that needs compaction
    /// mid-stream must be buffered and delivered, not dropped.
    #[test]
    fn full_buffer_below_threshold_compacts_and_delivers() {
        let dir = tmp_dir("compact_below_threshold");

        // Reader cap 512 → compact threshold at 256 bytes consumed.
        const READER_CAP: usize = 512;
        let mut rig = active_session(dir.path(), READER_CAP);

        // Small app (seq 2): once consumed it leaves < 256 bytes behind, so the
        // buffer will be "full but below the compaction threshold" after we top
        // it up — exactly the state Fix B fixes.
        let mut small = vec![0u8; 256];
        let small_len = inbound_app_frame(2, 6, &mut small);
        assert!(
            small_len < 128,
            "small frame ({small_len}) must stay well under the compact threshold"
        );

        // A large app (seq 3) that FITS the buffer on its own but NOT beside the
        // small frame's consumed residue — so completing it requires a compaction
        // that reclaims the small frame's space. (Distinct from scenario (a),
        // where the frame exceeds the buffer outright.)
        let mut large = vec![0u8; 1024];
        let large_len = inbound_app_frame(3, 400, &mut large);
        assert!(
            large_len <= READER_CAP,
            "large frame ({large_len}) must fit the reader buffer ({READER_CAP}) on its own"
        );
        assert!(
            large_len > READER_CAP - small_len,
            "large frame ({large_len}) must not fit beside the small frame's residue \
             ({small_len}) — that is what forces the mid-stream compaction"
        );

        // 1) Deliver the small frame.
        let spare = rig.read_spare();
        spare[..small_len].copy_from_slice(&small[..small_len]);
        rig.read_filled(small_len);
        assert_eq!(
            rig.poll().expect("poll small"),
            PollOutcome::Message,
            "small app must surface"
        );

        // 2) Fill the rest of the buffer with the head of the large frame. The
        //    small frame's bytes are now consumed (< threshold) and the buffer is
        //    full: should_compact() is false, remaining() is 0.
        let head = READER_CAP - small_len;
        let spare = rig.read_spare();
        let take = head.min(spare.len());
        spare[..take].copy_from_slice(&large[..take]);
        rig.read_filled(take);

        // The frame is still incomplete → NeedMoreBytes.
        assert_eq!(
            rig.poll().expect("poll large head"),
            PollOutcome::NeedMoreBytes,
            "partial large frame must ask for more"
        );

        // 3) The fix: read_spare must be NON-EMPTY here (it compacts because the
        //    buffer is full even though should_compact() is false). Without the
        //    fix this slice is empty and the wrapper false-EOFs.
        let spare = rig.read_spare();
        assert!(
            !spare.is_empty(),
            "read_spare must compact a full-but-below-threshold buffer to a \
             non-empty spare (Fix B); empty spare would false-EOF the wrapper"
        );

        // 4) Feed the remainder and confirm the large frame is delivered intact.
        let rest = &large[take..large_len];
        let mut fed = 0;
        while fed < rest.len() {
            let spare = rig.read_spare();
            assert!(
                !spare.is_empty(),
                "spare must stay non-empty while draining"
            );
            let n = (rest.len() - fed).min(spare.len());
            spare[..n].copy_from_slice(&rest[fed..fed + n]);
            rig.read_filled(n);
            fed += n;
        }
        assert_eq!(
            rig.poll().expect("poll large complete"),
            PollOutcome::Message,
            "large app must be delivered after compaction — no false disconnect"
        );
        // The delivered frame is the seq-3 app we sent (byte-for-byte).
        let msg = rig.message();
        assert!(
            matches!(msg, Message::Application { .. }),
            "delivered message must be the reassembled application frame"
        );
    }

    // ── extensibility: the sans-IO seam drives the machine with no transport ──

    /// The public sans-IO seam drives the *entire* state machine with NO
    /// [`recv`](FixSession::recv) and NO `Read`/`Write`/`WireStream` bound — the
    /// extension path a custom transport (kernel bypass, io_uring, AF_XDP) builds
    /// on. Three hand-built objects (no builder, no [`FixParts`]), and only the
    /// byte seam: encode-only [`encode_connect`](FixSession::encode_connect) fills the writer;
    /// [`writer.data()`](MessageWriter::data)/[`advance`](MessageWriter::advance)
    /// drain it; [`reader.spare()`](MessageReader::spare)/[`filled`](MessageReader::filled)
    /// feed inbound bytes; [`poll`](FixSession::poll) advances; and
    /// [`message`](FixSession::message) decodes the surfaced frame.
    #[test]
    fn sans_io_seam_drives_without_recv() {
        let dir = tmp_dir("sans_io_seam");

        // Three objects, hand-built — no transport of any kind. A fresh state so
        // `connect` actually emits the opening Logon into the writer.
        let mut reader =
            MessageReader::<MockDict>::with_frame_reader(FrameReader::builder().build());
        let mut writer =
            MessageWriter::<MockDict>::with_frame_writer(FrameWriter::builder().build());
        let state = SessionState::new(Duration::from_secs(30));
        let journal = FixJournal::open(dir.path(), 0, 256).unwrap();
        let mut session = FixSession::new(
            state,
            SessionConfig {
                sender: our_id(),
                target: peer_id(),
            },
            journal,
        );

        // Encode-only send stages the opening Logon (outbound seq 1, state →
        // LogonSent); drain it via the byte seam.
        session.encode_connect(&mut writer, NOW).unwrap();
        assert!(
            !writer.data().is_empty(),
            "encode_connect must stage an outbound Logon into the writer"
        );
        let n = writer.data().len();
        writer.advance(n);
        assert!(
            writer.data().is_empty(),
            "outbound drains purely via data()/advance()"
        );

        // Feed the peer's Logon ack through the inbound byte seam.
        let mut buf = vec![0u8; 256];
        let len = peer_logon_frame(1, true, &mut buf);
        let spare = reader.spare();
        spare[..len].copy_from_slice(&buf[..len]);
        reader.filled(len);

        // Advance the machine and decode the surfaced frame — all sans-IO.
        assert_eq!(
            session.poll(&mut reader, &mut writer, NOW).expect("poll"),
            PollOutcome::Message
        );
        assert!(matches!(
            session.message(&reader),
            Message::LogonAcknowledged { .. }
        ));
        assert_eq!(
            session.state().state(),
            State::Active,
            "the Logon ack drove the machine to Active with no recv/transport"
        );
    }

    #[test]
    fn connect_clears_terminated_for_reconnect() {
        let dir = tmp_dir("reconnect_terminated");
        let mut writer =
            MessageWriter::<MockDict>::with_frame_writer(FrameWriter::builder().build());
        let mut session = FixSession::new(
            SessionState::new(Duration::from_secs(30)),
            SessionConfig {
                sender: our_id(),
                target: peer_id(),
            },
            FixJournal::open(dir.path(), 0, 256).unwrap(),
        );

        // A clean logout or fatal error leaves `recv` terminated (set here via the
        // wrapper-author API, as `recv` itself would).
        session.mark_terminated();
        assert!(session.is_terminated());

        // The carry-over session reconnects: a fresh `connect` revives it so `recv`
        // works again. Without this, `recv` would return `Closed` forever.
        session.encode_connect(&mut writer, NOW).unwrap();
        assert!(
            !session.is_terminated(),
            "encode_connect must clear terminated so the carry-over session can reconnect"
        );
    }

    // ── user-driven admin sends: encode-only vs combined ─────────────────────

    /// A minimal `Read + Write` transport: reads always report `WouldBlock` (no
    /// inbound in these tests), writes append to a buffer so the combined-form
    /// tests can assert the exact bytes that reached the wire.
    #[derive(Default)]
    struct MockConn {
        written: Vec<u8>,
    }

    impl std::io::Read for MockConn {
        fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::new(
                std::io::ErrorKind::WouldBlock,
                "no data",
            ))
        }
    }

    impl std::io::Write for MockConn {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.written.extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    /// `MsgType(35)` of a frame, or `None`.
    fn msg_type(frame: &[u8]) -> Option<&[u8]> {
        find_tag(frame, 0, 35).map(|s| s.slice(frame))
    }

    /// The encode-only admin sends stage a well-formed frame into the writer with
    /// no transport: Heartbeat (echoing a TestReqID), TestRequest (fresh
    /// TestReqID), and ResendRequest (BeginSeqNo). This is the sans-IO seam a
    /// custom transport drains via `data()`/`advance()`.
    #[test]
    fn encode_admin_sends_fill_writer() {
        let dir = tmp_dir("encode_admin_sends");
        // Active initiator; the opening Logon consumed outbound seq 1 and was
        // drained, so these admin sends start at seq 2.
        let mut rig = active_session(dir.path(), 4096);

        // Heartbeat echoing a TestReqID(112).
        rig.session
            .encode_heartbeat(
                &mut rig.writer,
                NOW,
                Some(AsciiTextStr::try_from_bytes(b"PROBE").unwrap()),
            )
            .unwrap();
        {
            let out = rig.writer.data();
            assert!(!out.is_empty(), "encode_heartbeat must stage a frame");
            assert_eq!(msg_type(out), Some(b"0".as_ref()), "must be a Heartbeat");
            assert_eq!(
                find_tag(out, 0, 112).map(|s| s.slice(out)),
                Some(b"PROBE".as_ref()),
                "Heartbeat must echo the TestReqID"
            );
        }
        let n = rig.writer.data().len();
        rig.writer.advance(n);

        // TestRequest carrying a fresh TestReqID(112).
        rig.session
            .encode_test_request(&mut rig.writer, NOW)
            .unwrap();
        {
            let out = rig.writer.data();
            assert_eq!(msg_type(out), Some(b"1".as_ref()), "must be a TestRequest");
            assert!(
                find_tag(out, 0, 112).is_some(),
                "TestRequest must carry a TestReqID(112)"
            );
        }
        let n = rig.writer.data().len();
        rig.writer.advance(n);

        // ResendRequest covering [begin, ∞): BeginSeqNo(7)=begin, EndSeqNo(16)=0.
        rig.session
            .encode_resend_request(&mut rig.writer, NOW, 2)
            .unwrap();
        let out = rig.writer.data();
        assert_eq!(
            msg_type(out),
            Some(b"2".as_ref()),
            "must be a ResendRequest"
        );
        assert_eq!(
            find_tag(out, 0, 7).map(|s| s.slice(out)),
            Some(b"2".as_ref()),
            "BeginSeqNo(7) must be the requested begin"
        );
        assert_eq!(
            find_tag(out, 0, 16).map(|s| s.slice(out)),
            Some(b"0".as_ref()),
            "open-ended ResendRequest encodes EndSeqNo(16)=0"
        );
    }

    /// The combined admin sends encode + flush in one call: the writer is drained
    /// and the exact frame reaches the transport. Covers each new admin send in
    /// the combined form over a `Read + Write` mock.
    #[test]
    fn combined_admin_sends_flush_to_transport() {
        let dir = tmp_dir("combined_admin_sends");
        let mut rig = active_session(dir.path(), 4096);
        let mut conn = MockConn::default();

        // Heartbeat (unsolicited keepalive).
        rig.session
            .heartbeat(&mut rig.writer, &mut conn, NOW, None)
            .unwrap();
        assert!(
            rig.writer.is_empty(),
            "combined heartbeat must drain the writer"
        );
        assert_eq!(
            msg_type(&conn.written),
            Some(b"0".as_ref()),
            "the transport must have received a Heartbeat"
        );

        // TestRequest.
        conn.written.clear();
        rig.session
            .test_request(&mut rig.writer, &mut conn, NOW)
            .unwrap();
        assert!(rig.writer.is_empty());
        assert_eq!(msg_type(&conn.written), Some(b"1".as_ref()));

        // ResendRequest.
        conn.written.clear();
        rig.session
            .resend_request(&mut rig.writer, &mut conn, NOW, 2)
            .unwrap();
        assert!(rig.writer.is_empty());
        assert_eq!(msg_type(&conn.written), Some(b"2".as_ref()));
        // The framed bytes on the wire are self-delimiting and checksum-valid:
        // the production frame reader accepts exactly one frame.
        let frames = split_frames(&conn.written);
        assert_eq!(frames.len(), 1, "combined send must flush one whole frame");
        assert_eq!(msg_type(&frames[0]), Some(b"2".as_ref()));
    }

    // ── the recv borrow guarantee (contract §5) ──────────────────────────────

    /// A blocking `Read + Write` that replays queued inbound bytes and captures
    /// writes — feeds the borrow-guarantee test one frame, then `WouldBlock`.
    struct ReplayConn {
        inbound: std::collections::VecDeque<u8>,
        written: Vec<u8>,
    }

    impl ReplayConn {
        fn new(frame: &[u8]) -> Self {
            Self {
                inbound: frame.iter().copied().collect(),
                written: Vec::new(),
            }
        }
    }

    impl std::io::Read for ReplayConn {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.inbound.is_empty() {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::WouldBlock,
                    "drained",
                ));
            }
            let n = buf.len().min(self.inbound.len());
            for slot in buf.iter_mut().take(n) {
                *slot = self.inbound.pop_front().unwrap();
            }
            Ok(n)
        }
    }

    impl std::io::Write for ReplayConn {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.written.extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    /// An inbound TestRequest (35=1) from the peer at `seq`. `id` writes
    /// `TestReqID(112)` when `Some` (raw bytes, so a test can inject non-ASCII);
    /// `None` omits tag 112 entirely.
    fn peer_test_request(seq: u32, id: Option<&[u8]>, buf: &mut [u8]) -> usize {
        let mut seq_buf = [0u8; 10];
        let seq_n = nexus_fix_codec::encode_fix_uint(seq, &mut seq_buf);
        let mut fmt = FrameFormatter::new(buf, b"FIX.4.4", b"1");
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, peer_id().as_bytes());
        fmt.field(56, our_id().as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        if let Some(id) = id {
            fmt.field(112, id);
        }
        let (start, len) = fmt.finish().unwrap();
        buf.copy_within(start..start + len, 0);
        len
    }

    /// The borrow guarantee (contract §5): `recv`'s returned `Message<'r>` ties to
    /// `reader` **only**, so the reply can mutate `&mut session` / `&mut writer` /
    /// `&mut conn` while a borrowed payload (a `TestReqID`, a `LogonDecision`) is
    /// still alive. This is a *compile*-guarantee first (if the borrow leaked to
    /// `&mut self` neither arm would type-check) and a run-check second (the reply
    /// reaches the wire carrying the borrowed data).
    #[test]
    fn recv_borrow_guarantee_reply_while_payload_borrowed() {
        // Part 1 — recv → TestRequest { id } → heartbeat(&mut writer, .., Some(id)).
        {
            let dir = tmp_dir("borrow_test_request");
            let mut reader =
                MessageReader::<MockDict>::with_frame_reader(FrameReader::builder().build());
            let mut writer =
                MessageWriter::<MockDict>::with_frame_writer(FrameWriter::builder().build());
            let mut state = SessionState::new(Duration::from_secs(30));
            establish_state(&mut state); // Active initiator, next_inbound = 2
            let journal = FixJournal::open(dir.path(), 0, 256).unwrap();
            let mut session = FixSession::new(
                state,
                SessionConfig {
                    sender: our_id(),
                    target: peer_id(),
                },
                journal,
            );

            let mut buf = vec![0u8; 256];
            let len = peer_test_request(2, Some(b"PING"), &mut buf);
            let mut conn = ReplayConn::new(&buf[..len]);

            match session
                .recv(&mut reader, &mut writer, &mut conn, NOW)
                .unwrap()
            {
                Some(Message::TestRequest { id }) => {
                    // `id` borrows `reader`; the reply mutates session/writer/conn —
                    // four disjoint borrows, no copy-out.
                    session
                        .heartbeat(&mut writer, &mut conn, NOW, Some(id))
                        .unwrap();
                }
                other => panic!("expected TestRequest, got {}", variant(&other)),
            }
            assert_eq!(
                find_tag(&conn.written, 0, 112).map(|s| s.slice(&conn.written)),
                Some(b"PING".as_ref()),
                "the echoed Heartbeat carries the borrowed TestReqID"
            );
        }

        // Part 2 — recv → LogonRequest(decision) → decision.accept(&mut session, ..).
        {
            let dir = tmp_dir("borrow_logon_decision");
            let mut reader =
                MessageReader::<MockDict>::with_frame_reader(FrameReader::builder().build());
            let mut writer =
                MessageWriter::<MockDict>::with_frame_writer(FrameWriter::builder().build());
            // Disconnected acceptor: the peer's Logon surfaces a decision.
            let state = SessionState::new(Duration::from_secs(30));
            let journal = FixJournal::open(dir.path(), 0, 256).unwrap();
            let mut session = FixSession::new(
                state,
                SessionConfig {
                    sender: our_id(),
                    target: peer_id(),
                },
                journal,
            );

            let mut buf = vec![0u8; 256];
            let len = peer_logon_frame(1, true, &mut buf);
            let mut conn = ReplayConn::new(&buf[..len]);

            match session
                .recv(&mut reader, &mut writer, &mut conn, NOW)
                .unwrap()
            {
                Some(Message::LogonRequest(decision)) => {
                    // `decision` borrows `reader`; accept mutates session/writer/conn.
                    decision
                        .accept(&mut session, &mut writer, &mut conn, NOW)
                        .unwrap();
                }
                other => panic!("expected LogonRequest, got {}", variant(&other)),
            }
            assert_eq!(
                session.state().state(),
                State::Active,
                "accepting the Logon brings the session up"
            );
            assert_eq!(
                msg_type(&conn.written),
                Some(b"A".as_ref()),
                "the Logon reply reached the wire"
            );
        }
    }

    /// A TestRequest whose `TestReqID(112)` is absent must surface as an `Err`
    /// (`MissingField { tag: 112 }`) in the fallible receive path — never a
    /// silently-empty `Message::TestRequest`. This is the precondition the
    /// unchecked `AsciiTextStr` borrow in `message()` relies on.
    #[test]
    fn test_request_missing_112_surfaces_malformed() {
        use crate::framework::SessionError;

        let dir = tmp_dir("tr_missing_112");
        let mut rig = active_session(dir.path(), 4096); // Active, next_inbound = 2
        let mut buf = vec![0u8; 256];
        let len = peer_test_request(2, None, &mut buf); // no tag 112
        let spare = rig.read_spare();
        spare[..len].copy_from_slice(&buf[..len]);
        rig.read_filled(len);
        match rig.poll() {
            Err(super::Error::Protocol(SessionError::MissingField { tag: 112 })) => {}
            other => panic!("a TestRequest missing 112 must be MissingField(112), got {other:?}"),
        }
    }

    /// A TestRequest whose `TestReqID(112)` is present but non-ASCII must surface as
    /// an `Err` (`MalformedField { tag: 112 }`) — the codec's validating
    /// `&AsciiTextStr` parse catches it, so no non-ASCII bytes ever reach the
    /// unchecked borrow in `message()`.
    #[test]
    fn test_request_non_ascii_112_surfaces_malformed() {
        use crate::framework::SessionError;

        let dir = tmp_dir("tr_non_ascii_112");
        let mut rig = active_session(dir.path(), 4096);
        let mut buf = vec![0u8; 256];
        // 0xFF / 0xFE are non-printable-ASCII (and not SOH), so they frame cleanly
        // but fail `AsciiTextStr` validation.
        let len = peer_test_request(2, Some(&[0xFF, 0xFE]), &mut buf);
        let spare = rig.read_spare();
        spare[..len].copy_from_slice(&buf[..len]);
        rig.read_filled(len);
        match rig.poll() {
            Err(super::Error::Protocol(SessionError::MalformedField { tag: 112 })) => {}
            other => {
                panic!(
                    "a TestRequest with non-ASCII 112 must be MalformedField(112), got {other:?}"
                )
            }
        }
    }

    /// Name a surfaced message for panic messages (avoids requiring `Debug` on the
    /// `Message`'s decoder payloads).
    fn variant<D: FixDictionary>(m: &Option<Message<'_, D>>) -> &'static str {
        match m {
            None => "None",
            Some(Message::Application { .. }) => "Application",
            Some(Message::TestRequest { .. }) => "TestRequest",
            Some(Message::GapDetected { .. }) => "GapDetected",
            Some(Message::LogonRequest(_)) => "LogonRequest",
            Some(Message::LogonResetRequest(_)) => "LogonResetRequest",
            Some(Message::LogoutRequest { .. }) => "LogoutRequest",
            Some(Message::Heartbeat { .. }) => "Heartbeat",
            Some(Message::ResendRequest { .. }) => "ResendRequest",
            Some(Message::ResendOutOfRange { .. }) => "ResendOutOfRange",
            Some(Message::SequenceReset { .. }) => "SequenceReset",
            Some(Message::Reject { .. }) => "Reject",
            Some(Message::LogonAcknowledged { .. }) => "LogonAcknowledged",
            Some(Message::LoggedOut { .. }) => "LoggedOut",
        }
    }
}
