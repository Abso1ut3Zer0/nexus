//! Sans-IO FIX session core.
//!
//! [`FixSession`] owns everything a FIX session needs *except the socket*: the
//! frame reader/writer, the [`SessionState`] machine, the [`FixJournal`], and the
//! [`SessionConfig`]. It never performs I/O. A wrapper (e.g.
//! [`crate::transport::FixConnection`]) drives it by filling the inbound buffer
//! from a socket and draining the outbound buffer to a socket.
//!
//! # Byte-buffer seam
//!
//! Inbound: the wrapper reads socket bytes into [`read_spare`](FixSession::read_spare),
//! commits the count with [`read_filled`](FixSession::read_filled), then calls
//! [`poll`](FixSession::poll) to process the next buffered frame.
//!
//! Outbound: protocol handling enqueues bytes into the writer buffer; the wrapper
//! drains them via [`outbound`](FixSession::outbound) / [`advance_outbound`](FixSession::advance_outbound).
//!
//! # The poll/message split
//!
//! Returning a borrowed [`Message`] directly from a loop that also reads more
//! bytes hits the borrow checker (the classic NLL conditional-borrow wall). So
//! [`poll`](FixSession::poll) returns a *non-borrowing* [`PollOutcome`] after
//! processing one frame into a stable buffer (`reader.frame`), and
//! [`message`](FixSession::message) borrows that stable buffer to reconstruct the
//! typed [`Message`]. The wrapper loops on `poll`, servicing
//! [`PollOutcome::NeedMoreBytes`] (read the socket) and
//! [`PollOutcome::ResendPending`] (drain outbound), and calls `message()` once
//! [`PollOutcome::Message`] is returned.

use std::time::Instant;

use nexus_fix_codec::{
    FieldReader, FixAdminMsg, FixDictionary, FixHeader, FrameFormatter, NoCustomizer,
    SessionCustomizer, encode_fix_uint, find_tag, parse_fix_bool, parse_fix_seqnum, parse_fix_uint,
};
use nexus_journal::WriteError;

use crate::frame::{FrameError, FrameWriter};
use crate::framework::{
    Emitter, Message, MessageReader, MessageWriter, SessionConfig, SessionError,
};
use crate::persist::{FixJournal, ReplayItem};
use crate::session::{
    AppIn, Control, DisconnectReason, HeartbeatIn, LogonIn, LogoutIn, RejectIn, RejectInboundIn,
    ResendRequestIn, SequenceResetIn, SessionState, State, TestRequestIn,
};
use crate::timestamp::UTC_TIMESTAMP_LEN;

/// Error surfaced by the sans-IO session core.
///
/// Note: unlike the wrapper, the core never performs I/O, so it never produces
/// [`Error::Io`] on its own. The `Io` variant exists so the wrapper's `From<io::Error>`
/// can live on this shared type (the wrapper adds the socket errors).
#[derive(Debug)]
pub enum Error {
    Io(std::io::Error),
    MessageTooLarge(usize),
    Protocol(SessionError),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
/// timestamp>`), and a little `BodyLength` digit growth. [`FixSession::send_app`]
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
    /// No complete frame is buffered. The wrapper must read more bytes into
    /// [`read_spare`](FixSession::read_spare) and commit with
    /// [`read_filled`](FixSession::read_filled), then poll again.
    NeedMoreBytes,
    /// A resend is in progress and the outbound buffer filled. The wrapper must
    /// drain [`outbound`](FixSession::outbound) and poll again to continue it.
    ResendPending,
    /// The frame was processed but there is nothing to surface to the application
    /// (an out-of-sequence app suppressed pending resend, or a session-level
    /// reject was emitted). The wrapper should surface this as `Ok(None)`.
    Suppressed,
    /// The session disconnected. The wrapper surfaces
    /// `Message::Disconnected { reason }`.
    Disconnected(DisconnectReason),
}

/// Resumable resend state. A resend can enqueue more bytes than the outbound
/// buffer holds; on overflow the wrapper drains the buffer and re-polls, which
/// resumes here. `drained` counts fully-encoded [`ReplayItem`]s so re-deriving
/// `journal.resend(begin, end).skip(drained)` yields the remaining items with
/// identical wire output (`resend` is deterministic for a fixed journal state).
#[derive(Debug, Clone, Copy)]
struct ResendState {
    begin: u32,
    end: u32,
    drained: usize,
    ts: [u8; UTC_TIMESTAMP_LEN],
}

/// Sans-IO FIX session: state machine + framing + journal, no socket.
///
/// See the [module docs](self) for the byte-buffer seam and the poll/message
/// split.
///
/// `C` is the per-venue [`SessionCustomizer`] applied to outbound admin
/// messages; it defaults to [`NoCustomizer`], so plain-FIX callers write
/// `FixSession<Fix44>` and pay nothing.
pub struct FixSession<D: FixDictionary, C = NoCustomizer> {
    reader: MessageReader<D>,
    writer: MessageWriter<D, C>,
    state: SessionState,
    journal: FixJournal,
    config: SessionConfig,
    garbage_frames: u64,
    /// In-progress resend, if any (see [`ResendState`]).
    resend: Option<ResendState>,
    /// The verdict the state machine last returned. [`message`](Self::message)
    /// reconstructs the borrowed [`Message`] from it after a
    /// [`PollOutcome::Message`]; see [`Control`].
    pending: Control,
}

/// Lets a [`nexus_net::WireStream`] transport fill the session's inbound buffer
/// directly (`poll_fill_into(&mut session, …)`), skipping the intermediate
/// `&mut [u8]` copy. Forwards to the existing byte seam:
/// [`read_spare`](FixSession::read_spare) / [`read_filled`](FixSession::read_filled).
impl<D: FixDictionary, C: SessionCustomizer> nexus_net::ParserSink for FixSession<D, C> {
    #[inline]
    fn spare(&mut self) -> &mut [u8] {
        self.read_spare()
    }

    #[inline]
    fn filled(&mut self, n: usize) {
        self.read_filled(n);
    }
}

impl<D: FixDictionary> FixSession<D, NoCustomizer> {
    /// Builds a session with default (empty) frame buffers. Prefer
    /// [`from_buffers`](Self::from_buffers) to size the reader/writer up front.
    pub fn new(state: SessionState, config: SessionConfig, journal: FixJournal) -> Self {
        Self::new_with_customizer(state, config, journal, NoCustomizer)
    }
}

impl<D: FixDictionary, C: SessionCustomizer> FixSession<D, C> {
    /// Builds a session with default (empty) frame buffers and a per-venue
    /// [`SessionCustomizer`].
    pub fn new_with_customizer(
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
        customizer: C,
    ) -> Self {
        Self {
            reader: MessageReader::new(),
            writer: MessageWriter::with_customizer(customizer),
            state,
            journal,
            config,
            garbage_frames: 0,
            resend: None,
            pending: Control::None,
        }
    }

    /// Builds a session from pre-sized reader and writer buffers.
    ///
    /// The writer carries the customizer; pass a
    /// [`MessageWriter::with_frame_writer_and_customizer`] to use one.
    pub fn from_buffers(
        reader: MessageReader<D>,
        writer: MessageWriter<D, C>,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> Self {
        Self {
            reader,
            writer,
            state,
            journal,
            config,
            garbage_frames: 0,
            resend: None,
            pending: Control::None,
        }
    }

    // ── introspection ────────────────────────────────────────────────────────

    pub fn state(&self) -> &SessionState {
        &self.state
    }

    pub fn state_mut(&mut self) -> &mut SessionState {
        &mut self.state
    }

    pub fn garbage_frame_count(&self) -> u64 {
        self.garbage_frames
    }

    /// Whether the session should still be read from (not disconnected).
    pub fn wants_read(&self) -> bool {
        self.state.state() != State::Disconnected
    }

    /// Whether the outbound buffer has bytes waiting to be written.
    pub fn wants_write(&self) -> bool {
        !self.writer.is_empty()
    }

    pub fn allocate_seq(&mut self) -> Result<u32, SessionError> {
        self.state.allocate_seq(Instant::now())
    }

    /// Writer capacity in bytes (fixed at construction).
    pub fn writer_capacity(&self) -> usize {
        self.writer.capacity()
    }

    /// Inbound reader buffer capacity in bytes (fixed at construction).
    ///
    /// The largest single frame the reader can buffer. A wrapper reports this as
    /// the size in [`Error::MessageTooLarge`] when [`read_spare`](Self::read_spare)
    /// returns an empty slice — the buffer is full with one incomplete frame that
    /// cannot grow.
    pub fn reader_capacity(&self) -> usize {
        self.reader.inner.capacity()
    }

    // ── inbound byte-buffer seam ─────────────────────────────────────────────

    /// Spare region of the inbound buffer for the wrapper to read socket bytes
    /// into. Commit the number actually read with [`read_filled`](Self::read_filled).
    ///
    /// Compacts on the usual `should_compact()` threshold, but *also* whenever the
    /// buffer is full (`remaining() == 0`) even below that threshold. Without the
    /// full-buffer case a buffer that is full but <50% consumed would return an
    /// empty spare slice; the wrapper's `stream.read(&mut [])` then returns
    /// `Ok(0)` and is misread as EOF/disconnect. Compacting reclaims all consumed
    /// space, so the spare is non-empty whenever there is anything to reclaim. If
    /// nothing is reclaimable (a single incomplete frame already fills the whole
    /// buffer) the spare stays empty, and the wrapper turns that into
    /// [`Error::MessageTooLarge`] rather than reading into a zero-length slice.
    pub fn read_spare(&mut self) -> &mut [u8] {
        if self.reader.inner.should_compact() || self.reader.inner.remaining() == 0 {
            self.reader.inner.compact();
        }
        self.reader.inner.spare()
    }

    /// Commit `n` bytes read into [`read_spare`](Self::read_spare).
    pub fn read_filled(&mut self, n: usize) {
        self.reader.inner.filled(n);
    }

    // ── outbound byte-buffer seam ────────────────────────────────────────────

    pub fn has_outbound(&self) -> bool {
        !self.writer.is_empty()
    }

    pub fn outbound(&self) -> &[u8] {
        self.writer.data()
    }

    pub fn advance_outbound(&mut self, n: usize) {
        self.writer.advance(n);
    }

    // ── protocol actions (enqueue only, no I/O) ──────────────────────────────

    /// Enqueues a Logon (initiate the session). Outbound bytes land in the writer
    /// buffer; the wrapper drains them.
    pub fn connect(&mut self, now: Instant) -> Result<(), Error> {
        let mut emitter = journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
        self.state.connect(now, &mut emitter)?;
        Ok(())
    }

    /// Enqueues a Logon with `ResetSeqNumFlag=Y`.
    pub fn connect_reset(&mut self, now: Instant) -> Result<(), Error> {
        let mut emitter = journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
        self.state.connect_reset(now, &mut emitter)?;
        Ok(())
    }

    /// Enqueues an in-session sequence reset handshake.
    pub fn reset_sequence(&mut self, now: Instant) -> Result<(), Error> {
        let mut emitter = journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
        self.state.reset_sequence(now, &mut emitter)?;
        Ok(())
    }

    /// Enqueues a Logout.
    pub fn logout(&mut self, now: Instant) -> Result<(), Error> {
        let mut emitter = journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
        self.state.logout(now, &mut emitter)?;
        Ok(())
    }

    /// Journals then enqueues an application frame at sequence `seq`.
    ///
    /// The frame must fit the pre-allocated writer with [`REFRAME_HEADROOM`] to
    /// spare (so a later resend reframe fits). Larger frames return
    /// [`Error::MessageTooLarge`] before any journal or buffer write; size the
    /// writer up front for the workload.
    pub fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        if frame.len() > self.writer.capacity().saturating_sub(REFRAME_HEADROOM) {
            return Err(Error::MessageTooLarge(frame.len()));
        }
        journal_write(frame.len(), || self.journal.store(seq, frame))?;
        buffer_frame(&mut self.writer.inner, frame)
    }

    /// Advances heartbeat/test-request timers; enqueues any resulting admin
    /// messages. Returns `Some(reason)` if the timeout drove a disconnect.
    pub fn on_timeout(&mut self, now: Instant) -> Result<Option<DisconnectReason>, Error> {
        let ctrl = {
            let mut emitter = journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
            self.state.on_timeout(now, &mut emitter)?
        };
        Ok(if let Control::Disconnected { reason } = ctrl {
            Some(reason)
        } else {
            None
        })
    }

    // ── inbound processing ───────────────────────────────────────────────────

    /// Processes the next buffered inbound frame, driving the state machine,
    /// journaling, and enqueuing any outbound admin. Returns a non-borrowing
    /// [`PollOutcome`]; call [`message`](Self::message) after
    /// [`PollOutcome::Message`].
    ///
    /// See the [module docs](self) for the wrapper's poll loop.
    pub fn poll(&mut self, now: Instant) -> Result<PollOutcome, Error> {
        // Resume an in-progress resend before touching new inbound.
        if self.resend.is_some() {
            if self.drive_resend()? {
                return Ok(PollOutcome::ResendPending);
            }
            // Resend finished: surface the ResendRequest that triggered it.
            self.pending = Control::ResendRequest;
            return Ok(PollOutcome::Message);
        }

        // Keep the journal's inbound cursor aligned with the state machine.
        let n = self.state.next_inbound_seq();
        if n != self.journal.next_inbound() {
            self.journal.set_next_inbound(n);
        }

        // Pull the next complete frame into the stable buffer.
        loop {
            if self.reader.inner.should_compact() {
                self.reader.inner.compact();
            }
            match self.reader.inner.next() {
                Err(FrameError::MessageTooLarge { size }) => {
                    return Err(Error::MessageTooLarge(size));
                }
                Err(FrameError::Garbage { .. }) => {
                    self.garbage_frames += 1;
                }
                Ok(None) => return Ok(PollOutcome::NeedMoreBytes),
                Ok(Some(raw)) => {
                    self.reader.frame.clear();
                    self.reader.frame.extend_from_slice(raw);
                    break;
                }
            }
        }

        self.process_frame(now)
    }

    /// Reconstructs the typed [`Message`] for the frame just processed by
    /// [`poll`](Self::poll). Only valid immediately after a [`PollOutcome::Message`]
    /// (or a [`PollOutcome::Disconnected`], which also maps to
    /// `Message::Disconnected`); the borrow is over the stable frame buffer.
    pub fn message(&self) -> Message<'_, D> {
        let frame = &self.reader.frame[..];
        match self.pending {
            Control::Logon { acknowledged } => {
                let msg = D::Logon::decode(frame).expect("frame decoded in poll");
                if acknowledged {
                    Message::LogonAcknowledged { msg }
                } else {
                    Message::LogonRequest { msg }
                }
            }
            Control::Logout => {
                let msg = D::Logout::decode(frame).expect("frame decoded in poll");
                Message::LogoutRequest { msg }
            }
            Control::Heartbeat => {
                let msg = D::Heartbeat::decode(frame).expect("frame decoded in poll");
                Message::Heartbeat { msg }
            }
            Control::TestRequest => {
                let msg = D::TestRequest::decode(frame).expect("frame decoded in poll");
                Message::TestRequest { msg }
            }
            Control::ResendRequest => {
                let msg = D::ResendRequest::decode(frame).expect("frame decoded in poll");
                Message::ResendRequest { msg }
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
            Control::Disconnected { reason } => Message::Disconnected { reason },
            Control::None | Control::Proceed => {
                unreachable!("message() called without a pending message")
            }
        }
    }

    /// Full protocol handling for the frame in `reader.frame`. Mirrors the
    /// original `recv` body: comp-id validation, inbound journaling, per-type
    /// state driving, and outbound admin/resend enqueue.
    fn process_frame(&mut self, now: Instant) -> Result<PollOutcome, Error> {
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
            {
                let mut emitter =
                    journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
                self.state.on_comp_id_mismatch(now, &mut emitter)?;
            }
            // Always surface CompIdMismatch here, mirroring the original driver:
            // the handler disconnects the state machine; the reason is fixed.
            return Ok(self.dispose(Control::Disconnected {
                reason: DisconnectReason::CompIdMismatch,
            }));
        }

        // Well-framed and comp-id-valid: archive the inbound message for
        // visibility/audit. Garbage and foreign (comp-id-mismatched) frames are
        // not journaled — they never reach here.
        journal_write(frame.len(), || self.journal.store_inbound(frame))?;

        let frame = &self.reader.frame[..];
        let raw_type = if let Some(s) = find_tag(frame, 0, 35) {
            s.slice(frame)
        } else {
            // The missing-tag-35 reject is NOT journaled (matches the original):
            // this call site gives the `Emitter` a no-op `after` closure, while
            // every other site uses the journaling emitter.
            let mut emitter = Emitter::new(&mut self.writer, &self.config, |_seq, _frame| Ok(()));
            self.state.on_reject_inbound(
                RejectInboundIn {
                    seq,
                    ref_tag_id: Some(35),
                    session_reject_reason: 1,
                    is_poss_dup: poss_dup,
                },
                now,
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
                        journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
                    self.state.on_logon(
                        LogonIn {
                            seq,
                            heart_bt_int_s: hbi,
                            is_reset_seq_num: reset,
                            send_reply: !was_logon_sent,
                        },
                        now,
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
                        journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
                    self.state.on_logout(
                        LogoutIn {
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        now,
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
                        journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
                    self.state.on_heartbeat(
                        HeartbeatIn {
                            echo_id,
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        now,
                        &mut emitter,
                    )?
                };
                Ok(self.dispose(ctrl))
            }
            b"1" => {
                // Validate the typed decode before any side effect (see `b"A"`).
                D::TestRequest::decode(frame)
                    .map_err(|_| Error::Protocol(SessionError::MalformedMessage))?;
                let test_req_id =
                    find_tag(frame, 0, 112).map_or_else(|| b"".as_ref(), |s| s.slice(frame));
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
                    self.state.on_test_request(
                        TestRequestIn {
                            test_req_id,
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        now,
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
                        journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
                    self.state.on_resend_request(
                        ResendRequestIn {
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        now,
                        &mut emitter,
                    )?
                };
                // ResendRequest is the one kind the driver acts on beyond
                // surfacing the message: it drives the replay from the locally
                // parsed `begin`/`end`.
                match ctrl {
                    Control::ResendRequest => {
                        let re = if end == 0 {
                            self.state.next_outbound_seq().saturating_sub(1)
                        } else {
                            end.min(self.state.next_outbound_seq().saturating_sub(1))
                        };
                        self.begin_resend(begin, re);
                        if self.drive_resend()? {
                            // Buffer filled mid-resend: wrapper drains, re-polls.
                            return Ok(PollOutcome::ResendPending);
                        }
                        self.pending = Control::ResendRequest;
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
                        journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
                    self.state.on_sequence_reset(
                        SequenceResetIn {
                            seq,
                            new_seq,
                            is_poss_dup: poss_dup,
                            is_gap_fill: gap_fill,
                        },
                        now,
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
                        journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
                    self.state.on_reject(
                        RejectIn {
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        now,
                        &mut emitter,
                    )?
                };
                Ok(self.dispose(ctrl))
            }
            _ => {
                let ctrl = {
                    let mut emitter =
                        journaling_emitter(&mut self.writer, &mut self.journal, &self.config);
                    self.state.on_app(
                        AppIn {
                            seq,
                            is_poss_dup: poss_dup,
                        },
                        now,
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
            Control::Disconnected { reason } => PollOutcome::Disconnected(reason),
            Control::Proceed => unreachable!("Proceed is transient; handlers never return it"),
            _ => PollOutcome::Message,
        }
    }

    // ── resend ───────────────────────────────────────────────────────────────

    /// Starts a resend of `[begin, end]`, capturing the timestamp once (matching
    /// the original `do_resend`, which formats one `SendingTime` for the batch).
    fn begin_resend(&mut self, begin: u32, end: u32) {
        use std::time::{SystemTime, UNIX_EPOCH};

        let unix_nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as i128;
        let mut ts = [0u8; UTC_TIMESTAMP_LEN];
        crate::timestamp::format_utc_timestamp(unix_nanos, &mut ts);
        self.resend = Some(ResendState {
            begin,
            end,
            drained: 0,
            ts,
        });
    }

    /// Encodes as many pending resend items as fit the outbound buffer.
    ///
    /// Returns `Ok(true)` if the buffer filled and the resend is not yet complete
    /// (wrapper must drain and re-poll); `Ok(false)` when the resend finished (the
    /// state is cleared).
    ///
    /// Item-granular resume: `drained` counts fully-encoded items, and
    /// `resend(begin, end)` is re-derived each call. The original flushed the
    /// buffer and retried the *same whole item* into an empty buffer on overflow;
    /// resuming at item granularity reproduces that exact wire output without
    /// splitting an item.
    fn drive_resend(&mut self) -> Result<bool, Error> {
        let rs = self
            .resend
            .expect("drive_resend with no resend in progress");
        let mut encoded = rs.drained;
        for item in self.journal.resend(rs.begin, rs.end).skip(rs.drained) {
            let ok = encode_resend_item(
                &mut self.writer.inner,
                &item,
                &self.config,
                &rs.ts,
                D::BEGIN_STRING,
            );
            if ok.is_err() {
                // Buffer full: leave the item for the next poll (after a drain).
                // `send_app`'s headroom guarantees the item fits an *empty*
                // buffer; if the buffer is already empty and it still fails, the
                // writer is sized too small — a configuration error.
                if self.writer.is_empty() {
                    self.resend = None;
                    return Err(Error::MessageTooLarge(
                        self.writer.inner.remaining().saturating_add(1),
                    ));
                }
                self.resend = Some(ResendState {
                    drained: encoded,
                    ..rs
                });
                return Ok(true);
            }
            encoded += 1;
        }
        self.resend = None;
        Ok(false)
    }
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
) -> Emitter<'a, D, C, impl FnMut(u32, &[u8]) -> Result<(), Error> + 'a> {
    Emitter::new(writer, config, move |seq, frame| {
        journal_write(frame.len(), || journal.store(seq, frame))
    })
}

/// Copies a pre-built frame into the writer buffer for the wrapper to drain.
///
/// Unlike the original `write_through` this performs no I/O: it only stages bytes.
/// The frame must fit the *empty* buffer capacity — [`FixSession::send_app`] caps
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
            encode_gap_fill(writer, begin_string, config, ts, *seq, *new_seq)
        }
        ReplayItem::App(orig) => reframe_app(writer, orig, ts, begin_string),
    }
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

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::time::{Duration, Instant};

    use nexus_fix_codec::{
        AdminEncode, AsciiTextStr, DecodeError, FieldReader, FieldView, FixAdminMsg, FixDictionary,
        FixHeader, FixTimestamp, FrameFormatter, checksum, find_tag, format_checksum,
    };

    use super::{FixSession, PollOutcome};
    use crate::frame::{FrameReader, FrameWriter};
    use crate::framework::{CompId, Message, MessageReader, MessageWriter, SessionConfig};
    use crate::persist::FixJournal;
    use crate::session::{Emit, LogonIn, SessionState};

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
    fn establish_state(state: &mut SessionState, now: Instant) {
        state.connect(now, &mut NullEmitter).unwrap();
        state
            .on_logon(
                LogonIn {
                    seq: 1,
                    heart_bt_int_s: 30,
                    is_reset_seq_num: false,
                    send_reply: false,
                },
                now,
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

    /// Build an `Active` session whose outbound journal holds app frames for
    /// seqs `1..=N` except `HOLE_A`/`HOLE_B`, ready to receive a ResendRequest.
    ///
    /// `writer_cap` sizes only the outbound writer — the shared journal content
    /// is byte-identical across runs, so the two resends differ only in the
    /// resend `SendingTime` (normalized away by the oracle).
    fn build_session(dir: &Path, writer_cap: usize) -> FixSession<MockDict> {
        let reader = MessageReader::with_frame_reader(FrameReader::builder().build());
        let writer = MessageWriter::with_frame_writer(
            FrameWriter::builder().buffer_capacity(writer_cap).build(),
        );
        let mut state = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        // Establish (initiator): Logon consumes outbound seq 1, peer's Logon at
        // seq 1 advances next_inbound to 2 and moves to Active.
        establish_state(&mut state, now);
        // Align outbound with the journal we are about to fill (next = N + 1) so
        // the resend `end` clamp (`re.min(next_outbound - 1)`) does not chop the
        // range. Keep next_inbound at 2 for the incoming ResendRequest.
        state.reset_seq_nums(N + 1, 2);

        let journal = FixJournal::open(dir, 0, 256).unwrap();
        let mut session = FixSession::from_buffers(
            reader,
            writer,
            state,
            SessionConfig {
                sender: our_id(),
                target: peer_id(),
            },
            journal,
        );

        // Store the app messages. `send_app` also stages the frame in the writer;
        // drain it so only the later resend output is captured.
        let mut buf = vec![0u8; 512];
        for seq in 1..=N {
            if seq == HOLE_A || seq == HOLE_B {
                continue; // interior hole → gap-fill on resend
            }
            let len = app_frame(seq, &mut buf);
            session.send_app(seq, &buf[..len]).unwrap();
            let n = session.outbound().len();
            session.advance_outbound(n);
        }
        assert!(
            !session.has_outbound(),
            "writer must be drained before resend"
        );
        session
    }

    /// Drive a ResendRequest for `[1, N]` to completion, concatenating every
    /// outbound byte. Returns `(stream, resend_pending_count)`.
    ///
    /// The loop fully drains the writer after each `poll`, so every resumed
    /// `drive_resend` sees a freshly auto-reset (full-capacity) buffer — exactly
    /// the "flush the buffer, retry the item into an empty buffer" contract the
    /// resumable path replaced.
    fn drive_resend_stream(session: &mut FixSession<MockDict>) -> (Vec<u8>, usize) {
        let now = Instant::now();
        let mut req = vec![0u8; 256];
        let len = resend_request_frame(2, 1, N, &mut req);
        let spare = session.read_spare();
        spare[..len].copy_from_slice(&req[..len]);
        session.read_filled(len);

        let mut stream = Vec::new();
        let mut pending = 0usize;
        loop {
            let outcome = session.poll(now).expect("poll");
            // Drain everything currently staged, then decide.
            while session.has_outbound() {
                let data = session.outbound();
                stream.extend_from_slice(data);
                let n = data.len();
                session.advance_outbound(n);
            }
            match outcome {
                PollOutcome::ResendPending => pending += 1,
                PollOutcome::Message => break, // ResendRequest surfaced: resend done
                other => panic!("unexpected outcome during resend: {other:?}"),
            }
        }
        (stream, pending)
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

    /// Canonicalize the resend `SendingTime` (52) to a fixed value and recompute
    /// the checksum (10), reusing the codec's own `checksum`/`format_checksum` so
    /// the normalization can never drift from the encoder. Every resend `52` is
    /// exactly `UTC_TIMESTAMP_LEN` bytes, so the overwrite is length-preserving —
    /// BodyLength (9) is untouched. `OrigSendingTime` (122) is left intact, so a
    /// bug that mangled it would still surface.
    fn normalize_sending_time(mut frame: Vec<u8>) -> Vec<u8> {
        const CANON: &[u8; 21] = b"11111111-11:11:11.111";
        if let Some(span) = find_tag(&frame, 0, 52) {
            let (o, l) = (span.offset as usize, span.len as usize);
            assert_eq!(l, CANON.len(), "resend SendingTime must be fixed width");
            frame[o..o + l].copy_from_slice(CANON);
            // Recompute checksum: sum bytes from `8=` up to (not including) the
            // trailing `10=DDD\x01` (last 7 bytes), matching the codec.
            let body_end = frame.len() - 7;
            let sum = checksum(&frame[..body_end]);
            let digits = format_checksum(sum);
            let dstart = frame.len() - 4; // three digits then SOH
            frame[dstart..dstart + 3].copy_from_slice(&digits);
        }
        frame
    }

    fn normalize_stream(stream: &[u8]) -> Vec<Vec<u8>> {
        split_frames(stream)
            .into_iter()
            .map(normalize_sending_time)
            .collect()
    }

    /// Oracle: a resend that overflows a tiny writer many times (drain → resume)
    /// must produce byte-for-byte the same output as the same resend into a
    /// writer large enough to complete in a single pass. Divergence would mean
    /// the resumable path skipped, duplicated, split, reordered, or mis-reframed
    /// an item across a resume boundary.
    #[test]
    fn resumable_resend_matches_single_pass() {
        let dir_big = tmp_dir("resume_big");
        let dir_small = tmp_dir("resume_small");

        // Large writer: whole resend fits in one pass.
        let mut big = build_session(dir_big.path(), 64 * 1024);
        let (big_stream, big_pending) = drive_resend_stream(&mut big);
        assert_eq!(big_pending, 0, "large-writer resend must be a single pass");

        // Tiny writer: ~1 reframed item per cycle → many drain/resume boundaries.
        // 200 bytes holds one reframed item (< ~180) but never two (>= ~250),
        // and comfortably exceeds the largest single frame so the empty-buffer
        // MessageTooLarge guard never fires.
        let mut small = build_session(dir_small.path(), 200);
        let (small_stream, small_pending) = drive_resend_stream(&mut small);

        // The path was actually exercised, not trivially skipped.
        assert!(
            small_pending >= 5,
            "tiny-writer resend must hit ResendPending repeatedly (got {small_pending})"
        );

        // Strong oracle: identical after normalizing the resend SendingTime.
        let big_frames = normalize_stream(&big_stream);
        let small_frames = normalize_stream(&small_stream);
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

        // Structural spot-checks on the (canonical) single-pass stream.
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
        let now = Instant::now();

        let reader = MessageReader::with_frame_reader(FrameReader::builder().build());
        let writer =
            MessageWriter::with_frame_writer(FrameWriter::builder().buffer_capacity(4096).build());
        let mut state = SessionState::new(Duration::from_secs(30));
        // Initiate: engine sends Logon (outbound seq 1), moves to LogonSent, and
        // expects the peer's Logon at inbound seq 1.
        state.connect(now, &mut NullEmitter).unwrap();

        let journal = FixJournal::open(dir.path(), 0, 256).unwrap();
        let mut session: FixSession<StrictDict> = FixSession::from_buffers(
            reader,
            writer,
            state,
            SessionConfig {
                sender: our_id(),
                target: peer_id(),
            },
            journal,
        );
        // Drain the opening Logon the engine staged so only inbound is exercised.
        let n = session.outbound().len();
        session.advance_outbound(n);

        // Sanity: the *same* frame WITH tag 108 decodes and surfaces as a Message
        // (guards against the frame being rejected for an unrelated reason).
        {
            let dir_ok = tmp_dir("malformed_admin_ok");
            let reader = MessageReader::with_frame_reader(FrameReader::builder().build());
            let writer = MessageWriter::with_frame_writer(
                FrameWriter::builder().buffer_capacity(4096).build(),
            );
            let mut state = SessionState::new(Duration::from_secs(30));
            state.connect(now, &mut NullEmitter).unwrap();
            let journal = FixJournal::open(dir_ok.path(), 0, 256).unwrap();
            let mut ok_session: FixSession<StrictDict> = FixSession::from_buffers(
                reader,
                writer,
                state,
                SessionConfig {
                    sender: our_id(),
                    target: peer_id(),
                },
                journal,
            );
            let n = ok_session.outbound().len();
            ok_session.advance_outbound(n);

            let mut buf = vec![0u8; 256];
            let len = peer_logon_frame(1, true, &mut buf);
            let spare = ok_session.read_spare();
            spare[..len].copy_from_slice(&buf[..len]);
            ok_session.read_filled(len);
            assert_eq!(
                ok_session.poll(now).expect("valid Logon must not error"),
                PollOutcome::Message,
                "a well-formed Logon (with tag 108) must surface as a Message"
            );
        }

        // The malformed Logon: missing HeartBtInt(108) → typed decode fails.
        let mut buf = vec![0u8; 256];
        let len = peer_logon_frame(1, false, &mut buf);
        let spare = session.read_spare();
        spare[..len].copy_from_slice(&buf[..len]);
        session.read_filled(len);

        // Drive poll → message exactly as the wrapper's `recv` does. WITH the fix,
        // `poll` returns the error before ever yielding `Message`, so `message()`
        // is never reached. WITHOUT the fix, `poll` yields `Message` and the
        // `message()` call below panics on `.expect("frame decoded in poll")` —
        // this call is what makes the regression observable end-to-end.
        match session.poll(now) {
            Err(super::Error::Protocol(SessionError::MalformedMessage)) => {}
            Ok(PollOutcome::Message) => {
                let _ = session.message(); // panics without the fix
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
        let now = Instant::now();

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
        establish_state(&mut state, now);

        let journal = FixJournal::open(dir.path(), 0, 256).unwrap();
        let mut session: FixSession<MockDict> = FixSession::from_buffers(
            reader,
            writer,
            state,
            SessionConfig {
                sender: our_id(),
                target: peer_id(),
            },
            journal,
        );

        // Inbound seq 2 matches `next_inbound`, so `validate_seq` proceeds to the
        // reject emit rather than gap-filling or disconnecting.
        let mut buf = vec![0u8; 256];
        let len = peer_frame_without_msg_type(2, &mut buf);
        let spare = session.read_spare();
        spare[..len].copy_from_slice(&buf[..len]);
        session.read_filled(len);

        match session.poll(now) {
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

    /// Build an Active session (post-logon, `next_inbound == 2`) with the given
    /// reader capacity, ready to receive inbound app frames.
    fn active_session(dir: &Path, reader_cap: usize) -> FixSession<MockDict> {
        let reader = MessageReader::with_frame_reader(
            FrameReader::builder().buffer_capacity(reader_cap).build(),
        );
        let writer =
            MessageWriter::with_frame_writer(FrameWriter::builder().buffer_capacity(4096).build());
        let mut state = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish_state(&mut state, now); // peer Logon at seq 1 → Active, next_inbound = 2
        let journal = FixJournal::open(dir, 0, 256).unwrap();
        let mut session = FixSession::from_buffers(
            reader,
            writer,
            state,
            SessionConfig {
                sender: our_id(),
                target: peer_id(),
            },
            journal,
        );
        let n = session.outbound().len();
        session.advance_outbound(n); // drain the engine's opening Logon
        session
    }

    /// Fix B: when the reader buffer is full but consumed below the compaction
    /// threshold (`remaining() == 0 && !should_compact()`), `read_spare` must
    /// still compact so the spare is non-empty — otherwise the wrapper reads into
    /// a zero-length slice and false-EOFs. A large frame that needs compaction
    /// mid-stream must be buffered and delivered, not dropped.
    #[test]
    fn full_buffer_below_threshold_compacts_and_delivers() {
        let dir = tmp_dir("compact_below_threshold");
        let now = Instant::now();

        // Reader cap 512 → compact threshold at 256 bytes consumed.
        const READER_CAP: usize = 512;
        let mut session = active_session(dir.path(), READER_CAP);

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
        let spare = session.read_spare();
        spare[..small_len].copy_from_slice(&small[..small_len]);
        session.read_filled(small_len);
        assert_eq!(
            session.poll(now).expect("poll small"),
            PollOutcome::Message,
            "small app must surface"
        );

        // 2) Fill the rest of the buffer with the head of the large frame. The
        //    small frame's bytes are now consumed (< threshold) and the buffer is
        //    full: should_compact() is false, remaining() is 0.
        let head = READER_CAP - small_len;
        let spare = session.read_spare();
        let take = head.min(spare.len());
        spare[..take].copy_from_slice(&large[..take]);
        session.read_filled(take);

        // The frame is still incomplete → NeedMoreBytes.
        assert_eq!(
            session.poll(now).expect("poll large head"),
            PollOutcome::NeedMoreBytes,
            "partial large frame must ask for more"
        );

        // 3) The fix: read_spare must be NON-EMPTY here (it compacts because the
        //    buffer is full even though should_compact() is false). Without the
        //    fix this slice is empty and the wrapper false-EOFs.
        let spare = session.read_spare();
        assert!(
            !spare.is_empty(),
            "read_spare must compact a full-but-below-threshold buffer to a \
             non-empty spare (Fix B); empty spare would false-EOF the wrapper"
        );

        // 4) Feed the remainder and confirm the large frame is delivered intact.
        let rest = &large[take..large_len];
        let mut fed = 0;
        while fed < rest.len() {
            let spare = session.read_spare();
            assert!(
                !spare.is_empty(),
                "spare must stay non-empty while draining"
            );
            let n = (rest.len() - fed).min(spare.len());
            spare[..n].copy_from_slice(&rest[fed..fed + n]);
            session.read_filled(n);
            fed += n;
        }
        assert_eq!(
            session.poll(now).expect("poll large complete"),
            PollOutcome::Message,
            "large app must be delivered after compaction — no false disconnect"
        );
        // The delivered frame is the seq-3 app we sent (byte-for-byte).
        let msg = session.message();
        assert!(
            matches!(msg, Message::Application { .. }),
            "delivered message must be the reassembled application frame"
        );
    }
}
