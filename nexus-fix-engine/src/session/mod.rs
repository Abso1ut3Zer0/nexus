mod event;
mod input;

use std::time::Duration;

pub use event::{Control, DisconnectReason, State};
pub use input::*;
use nexus_fix_codec::{
    AdminEncode, AsciiTextStr, Heartbeat, Logon, LogonReset, Logout, Reject, ResendRequest,
    SequenceReset, TestRequest,
};

use crate::framework::SessionError;

const SEQ_MAX: u32 = i32::MAX as u32;

/// Emits the outbound admin messages the state machine produces.
///
/// The one generic method is why this is a trait and not a closure: `emit` must
/// be generic over the concrete [`AdminEncode`] message type, and a closure
/// cannot be generic over its parameter. Each [`SessionState`] handler takes a
/// `&mut E: Emit` and calls `emitter.emit(ResendRequest { .. })` with the
/// concrete struct — the type is never erased into a sum and matched back apart.
///
/// The driver supplies the production impl (`Emitter`), which encodes the frame
/// and journals it; tests supply a recording or discarding emitter. Each admin
/// carries its own pre-allocated `MsgSeqNum(34)` in `seq`; for a GapFill-mode
/// `SequenceReset` that is the start of the gap-filled range (encoded
/// `PossDupFlag=Y`), for every other message the next consumed outbound seqnum.
pub trait Emit {
    /// The error an [`emit`](Self::emit) can produce — an encode overflow or a
    /// journal write failure, per the driver's policy.
    type Error;

    /// Encode and dispatch one admin message.
    fn emit<M: AdminEncode>(&mut self, msg: M) -> Result<(), Self::Error>;
}

/// Bumps the next outbound sequence number, returning early with a graceful
/// disconnect if it is exhausted.
///
/// [`SessionState::bump_outbound`] returns `Option<u32>` (`None` on exhaustion),
/// but the exhaustion path returns a *success* value at the handler level
/// (`Ok(Control::Disconnected { reason: SeqNumExhausted })`, which the driver then
/// surfaces as `Err(TransportError::UnexpectedDisconnect)`) rather than the handler
/// itself producing an `Err`, so it cannot ride `?`. This macro packages the
/// `match` + early `return` so the ~8 handler sites that consume an outbound
/// seqnum share one definition of disconnect-on-exhaustion.
macro_rules! seq {
    ($self:ident) => {
        match $self.bump_outbound() {
            Some(s) => s,
            None => return Ok($self.disconnect(DisconnectReason::SeqNumExhausted)),
        }
    };
}

/// Pure FIX session state machine.
///
/// Owns sequence numbers and state transitions. The framework above owns the
/// transport, clock, and wire encoding. Each typed handler receives pre-decoded
/// admin fields plus an [`Emit`] for outbound admin messages, and returns a
/// [`Control`] verdict. Never allocates.
///
/// The session holds **no timers**: keepalive and liveness are the caller's
/// policy, built from [`heartbeat_interval`](Self::heartbeat_interval). Nothing
/// here reads a clock.
pub struct SessionState {
    state: State,
    hb: Duration,
    next_outbound: u32,
    next_inbound: u32,
    gap_high: u32,
    /// Monotonic `TestReqID(112)` source for user-driven liveness probes
    /// ([`test_request`](Self::test_request)). Kept separate from
    /// [`reset_counter`](Self::reset_counter) so a liveness probe issued while a
    /// sequence-reset handshake is mid-flight cannot perturb the reset's
    /// drain-echo match.
    liveness_counter: u64,
    /// Monotonic `TestReqID(112)` source for the in-session reset handshake
    /// ([`reset_sequence`](Self::reset_sequence)); the drain confirm in
    /// [`on_heartbeat`](Self::on_heartbeat) matches against exactly this value.
    reset_counter: u64,
}

impl SessionState {
    /// Creates a disconnected session with sequence numbers at 1.
    pub const fn new(heart_bt_int: Duration) -> Self {
        Self {
            state: State::Disconnected,
            hb: heart_bt_int,
            next_outbound: 1,
            next_inbound: 1,
            gap_high: 0,
            liveness_counter: 0,
            reset_counter: 0,
        }
    }

    /// The negotiated heartbeat interval (`HeartBtInt(108)`), updated to the
    /// peer's value at Logon.
    ///
    /// The session holds no timers; this is the one value it exposes so the
    /// caller can build their own heartbeat ticker and peer-liveness timers.
    pub const fn heartbeat_interval(&self) -> Duration {
        self.hb
    }

    /// Current lifecycle state.
    pub const fn state(&self) -> State {
        self.state
    }

    /// Next expected inbound `MsgSeqNum(34)`.
    pub const fn next_inbound_seq(&self) -> u32 {
        self.next_inbound
    }

    /// Next outbound `MsgSeqNum(34)`.
    pub const fn next_outbound_seq(&self) -> u32 {
        self.next_outbound
    }

    /// Restores outbound and inbound sequence numbers from a recovered journal.
    /// Call before connecting to resume a prior session without gaps.
    pub fn reset_seq_nums(&mut self, next_outbound: u32, next_inbound: u32) {
        self.next_outbound = next_outbound;
        self.next_inbound = next_inbound;
    }

    /// Allocates the next outbound sequence number for an application message.
    ///
    /// Returns `Err(SeqNumExhausted)` when `next_outbound` has reached `i32::MAX`.
    /// Returns `Err(ResetInProgress)` while an in-session reset handshake is active.
    pub fn allocate_seq(&mut self) -> Result<u32, SessionError> {
        if matches!(
            self.state,
            State::AwaitingResetDrain | State::AwaitingResetAck
        ) {
            return Err(SessionError::ResetInProgress);
        }
        if self.next_outbound > SEQ_MAX {
            return Err(SessionError::SeqNumExhausted);
        }
        let s = self.next_outbound;
        self.next_outbound += 1;
        Ok(s)
    }

    /// Bumps the next outbound sequence number. Returns `None` when exhausted
    /// (`next_outbound > i32::MAX`); the caller decides the disconnect (see the
    /// [`seq!`] macro). No internal side effect on exhaustion.
    fn bump_outbound(&mut self) -> Option<u32> {
        if self.next_outbound > SEQ_MAX {
            return None;
        }
        let s = self.next_outbound;
        self.next_outbound += 1;
        Some(s)
    }

    /// Initiates a session: sends a Logon. No-op if not disconnected.
    ///
    /// Emits: Logon.
    pub fn connect<E: Emit>(&mut self, emitter: &mut E) -> Result<Control, E::Error> {
        if self.state != State::Disconnected {
            return Ok(Control::None);
        }
        let seq = seq!(self);
        emitter.emit(Logon {
            seq,
            heart_bt_int_s: self.hb.as_secs() as u32,
        })?;
        self.state = State::LogonSent;
        Ok(Control::None)
    }

    /// Initiates a session with `ResetSeqNumFlag(141)=Y`: resets both sequence
    /// counters to 1 and sends a Logon. Returns `Err(SessionError::InvalidState)`
    /// if not disconnected.
    ///
    /// Emits: LogonReset.
    pub fn connect_reset<E: Emit>(&mut self, emitter: &mut E) -> Result<Control, E::Error>
    where
        E::Error: From<SessionError>,
    {
        if self.state != State::Disconnected {
            return Err(SessionError::InvalidState.into());
        }
        self.next_outbound = 1;
        self.next_inbound = 1;
        let seq = seq!(self);
        emitter.emit(LogonReset {
            seq,
            heart_bt_int_s: self.hb.as_secs() as u32,
        })?;
        self.state = State::LogonSent;
        Ok(Control::None)
    }

    /// Initiates an in-session sequence reset. Only valid while `Active`.
    ///
    /// Sends a TestRequest to drain in-flight messages. On the Heartbeat reply
    /// the engine sends `Logon(141=Y, seqNum=1)` and enters `AwaitingResetAck`.
    /// The reset completes when the counterparty's `Logon(141=Y)` arrives.
    /// `allocate_seq` returns `ResetInProgress` until the handshake completes.
    /// Returns `Err(SessionError::InvalidState)` if not Active.
    ///
    /// Emits: TestRequest.
    pub fn reset_sequence<E: Emit>(&mut self, emitter: &mut E) -> Result<Control, E::Error>
    where
        E::Error: From<SessionError>,
    {
        if self.state != State::Active {
            return Err(SessionError::InvalidState.into());
        }
        self.reset_counter += 1;
        let seq = seq!(self);
        emitter.emit(TestRequest {
            seq,
            id: self.reset_counter,
        })?;
        self.state = State::AwaitingResetDrain;
        Ok(Control::None)
    }

    /// Initiates a clean logout. No-op unless in an active state.
    ///
    /// `reason`, if given, rides the wire as `Text(58)`.
    ///
    /// Emits: Logout.
    pub fn logout<E: Emit>(
        &mut self,
        reason: Option<&AsciiTextStr>,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        if !matches!(self.state, State::Active | State::Resending) {
            return Ok(Control::None);
        }
        let seq = seq!(self);
        emitter.emit(Logout { seq, reason })?;
        self.state = State::LogoutPending;
        Ok(Control::None)
    }

    /// Sends a Heartbeat (35=0), optionally echoing a peer's `TestReqID(112)`.
    ///
    /// The engine no longer auto-emits a Heartbeat when answering a TestRequest;
    /// this is the user-driven replacement. It allocates the next outbound seqnum and
    /// emits, but performs no state transition and no sequence validation — the
    /// caller decides when to send (a keepalive tick, or a manual reply). `echo`
    /// is the raw `TestReqID` bytes to mirror back, or `None` for an unsolicited
    /// keepalive.
    ///
    /// Emits: Heartbeat.
    pub fn heartbeat<E: Emit>(
        &mut self,
        echo: Option<&[u8]>,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let seq = seq!(self);
        emitter.emit(Heartbeat { seq, echo })?;
        Ok(Control::None)
    }

    /// Sends a TestRequest (35=1) carrying a fresh `TestReqID(112)`.
    ///
    /// The user-driven liveness probe (contract timer 2): it allocates the next
    /// outbound seqnum, bumps the monotonic liveness `TestReqID` counter, and
    /// emits. No state transition — unlike [`reset_sequence`](Self::reset_sequence),
    /// which also sends a TestRequest but as the first leg of a reset handshake and
    /// off a *separate* counter. Peer liveness is proven by *any* inbound message,
    /// so the caller never needs to match the returned id.
    ///
    /// Emits: TestRequest.
    pub fn test_request<E: Emit>(&mut self, emitter: &mut E) -> Result<Control, E::Error> {
        self.liveness_counter += 1;
        let seq = seq!(self);
        emitter.emit(TestRequest {
            seq,
            id: self.liveness_counter,
        })?;
        Ok(Control::None)
    }

    /// Sends a ResendRequest (35=2) covering `[begin, ∞)` (encoded `EndSeqNo(16)=0`).
    ///
    /// The engine no longer auto-emits a ResendRequest on a detected gap; this is
    /// the user-driven replacement. It allocates the next outbound seqnum and
    /// emits. No state transition — the caller drives recovery. `begin` is the
    /// first missing inbound seqnum.
    ///
    /// Emits: ResendRequest.
    pub fn resend_request<E: Emit>(
        &mut self,
        begin: u32,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let seq = seq!(self);
        emitter.emit(ResendRequest { seq, begin })?;
        Ok(Control::None)
    }

    /// Sends a SequenceReset-Reset (35=4, `GapFillFlag=N`) forcing the peer's
    /// expected inbound seqnum to `new_seq` unconditionally — the "force the peer
    /// forward" answer to a [`Control::ResendOutOfRange`] whose `EndSeqNo` exceeds
    /// what we sent (the peer is ahead of us).
    ///
    /// Allocates the next outbound seqnum for `MsgSeqNum(34)` and advances it, like
    /// every other outbound verb (a Reset-mode SequenceReset is a fresh outbound
    /// admin; the receiver ignores its `MsgSeqNum`). No state transition. Distinct
    /// from [`reset_sequence`](Self::reset_sequence), the in-session reset
    /// *handshake* (a TestRequest/Logon exchange), and from
    /// [`gap_fill`](Self::gap_fill), the GapFill-mode SequenceReset.
    ///
    /// Emits: SequenceReset.
    pub fn sequence_reset<E: Emit>(
        &mut self,
        new_seq: u32,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let seq = seq!(self);
        emitter.emit(SequenceReset {
            seq,
            new_seq,
            gap_fill: false,
        })?;
        Ok(Control::None)
    }

    /// Sends a SequenceReset-GapFill (35=4, `GapFillFlag=Y` + `PossDupFlag=Y`)
    /// standing in for the skipped outbound range `[from_seq, new_seq)` — the answer
    /// to a [`Control::ResendOutOfRange`] whose `BeginSeqNo` rotated off the replay
    /// window.
    ///
    /// **Unlike every other outbound verb it does NOT allocate or advance the
    /// outbound seqnum.** A gap-fill carries the seqnum of the first message it
    /// replaces (`from_seq` → `MsgSeqNum(34)`) — the seqnum the peer is waiting on —
    /// so consuming a fresh one would open a new gap on the peer instead of closing
    /// theirs. `new_seq` is the `NewSeqNo(36)` the peer should expect next. The user
    /// answers `ResendOutOfRange { begin, .. }` with `gap_fill(begin, <resume
    /// seqnum>)`; `from_seq`/`new_seq` are their recovery policy.
    ///
    /// Emits: SequenceReset (at `from_seq`, no seqnum consumed).
    pub fn gap_fill<E: Emit>(
        &mut self,
        from_seq: u32,
        new_seq: u32,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        emitter.emit(SequenceReset {
            seq: from_seq,
            new_seq,
            gap_fill: true,
        })?;
        Ok(Control::None)
    }

    /// Handles a received Logon — dispatched on the current [`State`], since a
    /// Logon means a different thing depending on where the session is:
    ///
    /// - `LogonSent` — the *initiator's* incoming ack. Establishment seq handling
    ///   (too-low → Logout + disconnect, gap → ResendRequest, in-sync → `Active`)
    ///   stays engine-driven here — it is bringing the session up, not steady-state
    ///   flow — and returns [`Control::Logon`] with `acknowledged = true`.
    /// - `Disconnected` — the *acceptor's* incoming opening Logon. Surfaced as
    ///   [`Control::LogonRequest`] / [`Control::LogonResetRequest`]; the user answers
    ///   via [`accept_logon`](Self::accept_logon) / [`reject_logon`](Self::reject_logon).
    ///   No emit, no transition.
    /// - `Active` / `Resending` with `141=Y` — a peer-initiated in-session reset,
    ///   surfaced the same way (`seq` must be 1).
    /// - `AwaitingResetAck` — the peer's confirmation of a reset *we* initiated.
    ///
    /// The initiator/acceptor role is read from the state (`LogonSent` = we sent the
    /// opening Logon), so no separate flag is needed.
    ///
    /// Emits (initiator-establishment mechanism only): Logout | ResendRequest.
    pub fn on_logon<E: Emit>(
        &mut self,
        msg: LogonIn,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let LogonIn {
            seq,
            heart_bt_int_s,
            is_reset_seq_num,
        } = msg;

        match self.state {
            // We initiated an in-session reset; this is the peer's confirming
            // Logon(141=Y, seq=1). No emit.
            State::AwaitingResetAck => {
                if !is_reset_seq_num || seq != 1 {
                    return Ok(self.disconnect(DisconnectReason::ProtocolViolation));
                }
                self.hb = Duration::from_secs(u64::from(heart_bt_int_s));
                self.next_inbound = 2;
                self.state = State::Active;
                Ok(Control::Logon { acknowledged: true })
            }

            // We sent the opening Logon; this is the ack. Establishment seq
            // handling stays engine-driven (bringing the session up, not
            // steady-state flow — only steady-state gaps surface as GapDetected).
            State::LogonSent => {
                if is_reset_seq_num {
                    self.next_inbound = 1;
                }
                self.hb = Duration::from_secs(u64::from(heart_bt_int_s));

                if seq < self.next_inbound {
                    let logout_seq = seq!(self);
                    emitter.emit(Logout {
                        seq: logout_seq,
                        reason: None,
                    })?;
                    return Ok(self.disconnect(DisconnectReason::SeqNumTooLow));
                }
                if seq > self.next_inbound {
                    self.gap_high = seq;
                    let rr_seq = seq!(self);
                    emitter.emit(ResendRequest {
                        seq: rr_seq,
                        begin: self.next_inbound,
                    })?;
                    self.state = State::Resending;
                } else {
                    self.next_inbound += 1;
                    self.state = State::Active;
                }
                Ok(Control::Logon { acknowledged: true })
            }

            // Fresh connection; we are the acceptor. Surface the decision — no
            // emit, no transition; `accept_logon` does the reply + advance on the
            // user's call.
            State::Disconnected => Ok(if is_reset_seq_num {
                Control::LogonResetRequest {
                    seq,
                    heart_bt_int_s,
                }
            } else {
                Control::LogonRequest {
                    seq,
                    heart_bt_int_s,
                }
            }),

            // Established; a Logon(141=Y) now is a peer-initiated in-session reset.
            // Surface it the same way — `seq` must be 1.
            State::Active | State::Resending if is_reset_seq_num => {
                if seq != 1 {
                    return Ok(self.disconnect(DisconnectReason::ProtocolViolation));
                }
                Ok(Control::LogonResetRequest {
                    seq,
                    heart_bt_int_s,
                })
            }

            // Anything else — a non-reset Logon while active, a logout in flight,
            // mid-reset drain: nothing to answer.
            _ => Ok(Control::None),
        }
    }

    /// Accepts a counterparty-initiated Logon surfaced as
    /// [`Control::LogonRequest`] / [`Control::LogonResetRequest`]: emits the reply
    /// (a Logon, or a LogonReset when `is_reset`), applies the negotiated
    /// `HeartBtInt`, and advances the session — the reply + state work `on_logon`
    /// used to do inline, now gated on the user's decision.
    ///
    /// Dispatches on the current state: from `Disconnected` this is an acceptor
    /// opening a session (with the establishment seq-check preserved: a gap emits a
    /// ResendRequest and enters `Resending`, a too-low seqnum emits a Logout and
    /// disconnects); from `Active`/`Resending` it is the reply leg of a
    /// peer-initiated in-session reset.
    ///
    /// `seq`/`heart_bt_int_s`/`is_reset` are the fields captured from the peer
    /// Logon when the decision was surfaced.
    ///
    /// Emits: Logon | LogonReset | Logout | ResendRequest.
    pub fn accept_logon<E: Emit>(
        &mut self,
        seq: u32,
        heart_bt_int_s: u32,
        is_reset: bool,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        // Peer-initiated reset while active: the decision was surfaced from
        // Active/Resending, and `seq == 1` was already validated by `on_logon`.
        if matches!(self.state, State::Active | State::Resending) {
            self.hb = Duration::from_secs(u64::from(heart_bt_int_s));
            self.next_outbound = 1;
            let reply_seq = seq!(self);
            emitter.emit(LogonReset {
                seq: reply_seq,
                heart_bt_int_s: self.hb.as_secs() as u32,
            })?;
            self.next_inbound = 2;
            self.state = State::Active;
            return Ok(Control::Logon {
                acknowledged: false,
            });
        }

        // Disconnected acceptor: reply + establishment seq-check.
        if is_reset {
            self.next_inbound = 1;
            self.next_outbound = 1;
        }
        self.hb = Duration::from_secs(u64::from(heart_bt_int_s));
        let reply_seq = seq!(self);
        if is_reset {
            emitter.emit(LogonReset {
                seq: reply_seq,
                heart_bt_int_s,
            })?;
        } else {
            emitter.emit(Logon {
                seq: reply_seq,
                heart_bt_int_s,
            })?;
        }

        if seq < self.next_inbound {
            let logout_seq = seq!(self);
            emitter.emit(Logout {
                seq: logout_seq,
                reason: None,
            })?;
            return Ok(self.disconnect(DisconnectReason::SeqNumTooLow));
        }
        if seq > self.next_inbound {
            self.gap_high = seq;
            let rr_seq = seq!(self);
            emitter.emit(ResendRequest {
                seq: rr_seq,
                begin: self.next_inbound,
            })?;
            self.state = State::Resending;
        } else {
            self.next_inbound += 1;
            self.state = State::Active;
        }
        Ok(Control::Logon {
            acknowledged: false,
        })
    }

    /// Rejects a counterparty-initiated Logon: emits a Logout and disconnects.
    ///
    /// The user's policy hook for refusing a session (e.g. failed authentication).
    /// Answers a [`Control::LogonRequest`] / [`Control::LogonResetRequest`] the
    /// user declined. `reason`, if given, rides the wire as `Text(58)`.
    ///
    /// Emits: Logout.
    pub fn reject_logon<E: Emit>(
        &mut self,
        reason: Option<&AsciiTextStr>,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let seq = seq!(self);
        emitter.emit(Logout { seq, reason })?;
        self.state = State::Disconnected;
        Ok(Control::None)
    }

    /// Handles a received Logout.
    ///
    /// A Logout confirming *our* initiated logout (state `LogoutPending`, in
    /// sequence) completes the exchange and surfaces as [`Control::LoggedOut`]. A
    /// peer-*initiated* Logout while `Active`/`Resending` surfaces as
    /// [`Control::Logout`] ([`Message::LogoutRequest`](crate::Message::LogoutRequest));
    /// the reply is now user-driven (`logout(..)`), no longer engine-emitted.
    ///
    /// Emits (only the too-low Logout via `validate_seq`): Logout.
    pub fn on_logout<E: Emit>(
        &mut self,
        msg: LogoutIn,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let LogoutIn { seq, is_poss_dup } = msg;
        if self.state == State::LogonSent {
            return Ok(self.logged_out());
        }
        if matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            match self.validate_seq(seq, is_poss_dup, emitter)? {
                Control::Proceed => {
                    if self.state == State::LogoutPending {
                        // Confirm of our own initiated logout: terminal.
                        return Ok(self.logged_out());
                    }
                    // Peer-initiated logout: surface it; the user replies with
                    // `logout(..)`. No auto-reply, no state change.
                    return Ok(Control::Logout);
                }
                // Gap (GapDetected) / duplicate (None) / too-low (Disconnected):
                // propagated; none surfaces the Logout.
                ctrl => return Ok(ctrl),
            }
        }
        // Out-of-state (e.g. mid-reset) Logout — surfaced for the user to answer.
        Ok(Control::Logout)
    }

    /// Handles a received Heartbeat. `echo_id` is `TestReqID(112)` parsed as `u64`, if present.
    ///
    /// Emits (some via `validate_seq`): LogonReset | ResendRequest | Logout.
    pub fn on_heartbeat<E: Emit>(
        &mut self,
        msg: HeartbeatIn,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let HeartbeatIn {
            echo_id,
            seq,
            is_poss_dup,
        } = msg;

        if self.state == State::AwaitingResetDrain {
            let echo_matches = echo_id == Some(self.reset_counter);
            if echo_matches && seq == self.next_inbound {
                // Drain confirmed: all in-flight messages received, send LogonReset.
                self.next_inbound += 1;
                self.next_outbound = 1;
                let logon_seq = seq!(self);
                emitter.emit(LogonReset {
                    seq: logon_seq,
                    heart_bt_int_s: self.hb.as_secs() as u32,
                })?;
                self.state = State::AwaitingResetAck;
                return Ok(Control::Heartbeat);
            }
            // Not the drain confirm: validate sequence normally.
            match self.validate_seq(seq, is_poss_dup, emitter)? {
                Control::Proceed => self.check_resend_done(),
                // Gap/duplicate: suppressed, not surfaced.
                ctrl => return Ok(ctrl),
            }
            return Ok(Control::Heartbeat);
        }

        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending | State::AwaitingResetAck
        ) {
            return Ok(Control::Heartbeat);
        }
        match self.validate_seq(seq, is_poss_dup, emitter)? {
            Control::Proceed => self.check_resend_done(),
            // Gap/duplicate: suppressed, not surfaced.
            ctrl => return Ok(ctrl),
        }
        Ok(Control::Heartbeat)
    }

    /// Handles a received TestRequest.
    ///
    /// The engine no longer auto-emits the Heartbeat echo: an in-sequence
    /// TestRequest surfaces as [`Control::TestRequest`]
    /// ([`Message::TestRequest`](crate::Message::TestRequest) carrying the
    /// `TestReqID`), and the user answers with `heartbeat(Some(id))`. A gap/dup is
    /// a recovery event, propagated (never surfaced).
    ///
    /// Emits (only the too-low Logout via `validate_seq`): Logout.
    pub fn on_test_request<E: Emit>(
        &mut self,
        msg: TestRequestIn,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let TestRequestIn { seq, is_poss_dup } = msg;
        if !matches!(
            self.state,
            State::Active
                | State::Resending
                | State::LogoutPending
                | State::AwaitingResetDrain
                | State::AwaitingResetAck
        ) {
            return Ok(Control::TestRequest);
        }
        match self.validate_seq(seq, is_poss_dup, emitter)? {
            Control::Proceed => self.check_resend_done(),
            // Gap (GapDetected) / duplicate (None): propagated, not surfaced.
            ctrl => return Ok(ctrl),
        }
        Ok(Control::TestRequest)
    }

    /// Handles a received ResendRequest. On an in-sequence request returns
    /// [`Control::ResendRequest`] so the driver drives the replay walk via
    /// `FixJournal::resend` (it parses `begin`/`end` locally). A gap, duplicate,
    /// or out-of-state request returns [`Control::None`]: the driver does not
    /// replay, and there is nothing to surface.
    ///
    /// Emits (via `validate_seq`): ResendRequest | Logout.
    pub fn on_resend_request<E: Emit>(
        &mut self,
        msg: ResendRequestIn,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let ResendRequestIn { seq, is_poss_dup } = msg;
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Ok(Control::None);
        }
        match self.validate_seq(seq, is_poss_dup, emitter)? {
            Control::Proceed => {
                self.check_resend_done();
                Ok(Control::ResendRequest)
            }
            Control::None => Ok(Control::None),
            ctrl => Ok(ctrl),
        }
    }

    /// Handles a received SequenceReset or GapFill.
    ///
    /// `is_gap_fill = false` is Reset mode: ignores `MsgSeqNum`, sets
    /// `next_inbound` to `new_seq`. `is_gap_fill = true` is GapFill mode:
    /// validates sequence, advances `next_inbound` to `new_seq`.
    ///
    /// Emits (some via `validate_seq`): Reject | ResendRequest | Logout.
    pub fn on_sequence_reset<E: Emit>(
        &mut self,
        msg: SequenceResetIn,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let SequenceResetIn {
            seq,
            new_seq,
            is_poss_dup,
            is_gap_fill,
        } = msg;
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Ok(Control::SequenceReset);
        }
        if is_gap_fill {
            // Honor the frame's PossDupFlag: a below-expected GapFill carrying
            // PossDup=Y is a benign duplicate (the overlapping-ResendRequest
            // race) — discarded, not a disconnect (FIX 4.4 / QuickFIX). Without
            // PossDup it is a genuine too-low error.
            match self.validate_seq(seq, is_poss_dup, emitter)? {
                // In-sequence GapFill only: advance next_inbound to NewSeqNo. A
                // gap/dup must not advance — it is a recovery event.
                Control::Proceed => {
                    if new_seq > self.next_inbound {
                        self.next_inbound = new_seq;
                    }
                    self.check_resend_done();
                }
                // Gap/duplicate: suppressed, not surfaced.
                ctrl => return Ok(ctrl),
            }
        } else {
            // Reset mode: ignores MsgSeqNum. A backward/zero NewSeqNo is rejected.
            if new_seq == 0 || new_seq < self.next_inbound {
                if let Some(reject_seq) = self.bump_outbound() {
                    emitter.emit(Reject {
                        seq: reject_seq,
                        ref_seq_num: seq,
                        ref_tag_id: Some(36),
                        session_reject_reason: 5,
                        reason: None,
                    })?;
                }
                return Ok(Control::SequenceReset);
            }
            self.next_inbound = new_seq;
            self.check_resend_done();
        }
        Ok(Control::SequenceReset)
    }

    /// Handles a received Reject.
    ///
    /// Emits (via `validate_seq`): ResendRequest | Logout.
    pub fn on_reject<E: Emit>(
        &mut self,
        msg: RejectIn,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let RejectIn { seq, is_poss_dup } = msg;
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Ok(Control::Reject);
        }
        match self.validate_seq(seq, is_poss_dup, emitter)? {
            Control::Proceed => self.check_resend_done(),
            // Gap/duplicate: suppressed, not surfaced.
            ctrl => return Ok(ctrl),
        }
        Ok(Control::Reject)
    }

    /// Handles an in-sequence application message. Returns
    /// [`Control::Application`] when the sequence is in order, [`Control::None`]
    /// when it is a gap/duplicate or the session is not active (nothing to
    /// surface), or [`Control::Disconnected`] on a too-low seqnum.
    ///
    /// Emits (via `validate_seq`): ResendRequest | Logout.
    pub fn on_app<E: Emit>(&mut self, msg: AppIn, emitter: &mut E) -> Result<Control, E::Error> {
        let AppIn { seq, is_poss_dup } = msg;
        if !matches!(
            self.state,
            State::Active
                | State::Resending
                | State::LogoutPending
                | State::AwaitingResetDrain
                | State::AwaitingResetAck
        ) {
            return Ok(Control::None);
        }
        match self.validate_seq(seq, is_poss_dup, emitter)? {
            Control::Proceed => {}
            ctrl => return Ok(ctrl),
        }
        self.check_resend_done();
        Ok(Control::Application)
    }

    /// Sends a session-level Reject (35=3) for a received message that cannot be processed.
    ///
    /// Validates sequence then sends a Reject for the rejected message's `seq`. A
    /// gap sends ResendRequest instead.
    /// The session remains alive. No-op if the session is not in an active state.
    ///
    /// Emits (some via `validate_seq`): Reject | ResendRequest | Logout.
    pub fn on_reject_inbound<E: Emit>(
        &mut self,
        msg: RejectInboundIn,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        let RejectInboundIn {
            seq,
            ref_tag_id,
            session_reject_reason,
            is_poss_dup,
        } = msg;
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Ok(Control::None);
        }
        match self.validate_seq(seq, is_poss_dup, emitter)? {
            Control::Proceed => {}
            ctrl => return Ok(ctrl),
        }
        // `seq` is the rejected inbound message's seqnum (`RefSeqNum`); the Reject
        // we send carries its own freshly allocated outbound seqnum.
        let reject_seq = seq!(self);
        emitter.emit(Reject {
            seq: reject_seq,
            ref_seq_num: seq,
            ref_tag_id,
            session_reject_reason,
            reason: None,
        })?;
        Ok(Control::None)
    }

    /// Handles a CompID mismatch detected by the framework. Sends Logout and disconnects.
    ///
    /// Emits: Logout.
    pub fn on_comp_id_mismatch<E: Emit>(&mut self, emitter: &mut E) -> Result<Control, E::Error> {
        if self.state == State::Disconnected {
            return Ok(Control::None);
        }
        let seq = seq!(self);
        emitter.emit(Logout { seq, reason: None })?;
        Ok(self.disconnect(DisconnectReason::CompIdMismatch))
    }

    /// Validates an inbound sequence number. Returns:
    /// - [`Control::Proceed`] — seq matched and advanced; caller keeps processing.
    /// - [`Control::GapDetected`] — a gap (seq above expected) that opens recovery:
    ///   the engine records `gap_high` and enters `Resending`, but the
    ///   ResendRequest is now *user-driven* (surfaced as
    ///   [`Message::GapDetected`](crate::Message::GapDetected)). A further gap while
    ///   already `Resending` is suppressed as [`Control::None`], not re-surfaced.
    /// - [`Control::None`] — a `poss_dup`-too-low frame (a benign duplicate,
    ///   ignored). Propagated as the caller's verdict: the message is suppressed.
    /// - [`Control::Disconnected`] — a too-low seqnum without `poss_dup`, or
    ///   outbound exhaustion while emitting the Logout.
    ///
    /// Emits (only the too-low Logout): Logout.
    fn validate_seq<E: Emit>(
        &mut self,
        seq: u32,
        poss_dup: bool,
        emitter: &mut E,
    ) -> Result<Control, E::Error> {
        if seq > self.next_inbound {
            if self.gap_high < seq {
                self.gap_high = seq;
            }
            // Already recovering: a further gap is suppressed (the user has one
            // outstanding ResendRequest to drive). Otherwise open recovery and
            // surface the gap so the user sends the ResendRequest.
            if self.state == State::Resending {
                return Ok(Control::None);
            }
            let begin = self.next_inbound;
            if self.state == State::Active {
                self.state = State::Resending;
            }
            return Ok(Control::GapDetected { begin });
        }
        if seq < self.next_inbound {
            if poss_dup {
                return Ok(Control::None);
            }
            let logout_seq = seq!(self);
            emitter.emit(Logout {
                seq: logout_seq,
                reason: None,
            })?;
            return Ok(self.disconnect(DisconnectReason::SeqNumTooLow));
        }
        self.next_inbound += 1;
        Ok(Control::Proceed)
    }

    /// Transitions to `Disconnected` and returns the matching verdict.
    fn disconnect(&mut self, reason: DisconnectReason) -> Control {
        self.state = State::Disconnected;
        Control::Disconnected { reason }
    }

    /// Clean, negotiated logout: the same terminal state transition as
    /// [`disconnect`](Self::disconnect), but the graceful `Control::LoggedOut`
    /// verdict — surfaced as `Message::LoggedOut`, not an error.
    fn logged_out(&mut self) -> Control {
        self.state = State::Disconnected;
        Control::LoggedOut
    }

    fn check_resend_done(&mut self) {
        if self.state == State::Resending && self.next_inbound > self.gap_high {
            self.state = State::Active;
        }
    }
}

#[cfg(test)]
mod tests {
    use nexus_fix_codec::{
        AdminHeader, AdminMsgOut, AsciiTextStr, DecodeError, FieldView, FixAdminMsg, FixDictionary,
        FixHeader, FixTimestamp, FrameFormatter, NoCustomizer, find_tag, parse_fix_uint,
    };

    use super::*;

    // ── minimal dictionary so the recording emitter can encode admin frames ─────

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

    // ── recording emitter: captures each emitted admin as its encoded frame ─────

    /// An [`Emit`] that encodes each emitted message through the real
    /// `AdminEncode` path (into a `MockDict` frame) and records the frame bytes.
    /// Assertions decode the captured frame — `MsgType(35)` and body tags — so
    /// they pin the actual wire output, not a captured enum. `Error` is
    /// `SessionError` (trivially `From<SessionError>`), so the same emitter drives
    /// both the plain handlers and the reset initiators whose wrong-state guard
    /// requires `E::Error: From<SessionError>`.
    struct RecordingEmitter {
        frames: Vec<Vec<u8>>,
    }

    impl RecordingEmitter {
        fn new() -> Self {
            Self { frames: Vec::new() }
        }
        fn len(&self) -> usize {
            self.frames.len()
        }
        fn clear(&mut self) {
            self.frames.clear();
        }
        /// `MsgType(35)` of the `i`-th recorded frame.
        fn mt(&self, i: usize) -> &[u8] {
            find_tag(&self.frames[i], 0, 35)
                .map(|s| s.slice(&self.frames[i]))
                .expect("frame carries MsgType(35)")
        }
        /// A body tag parsed as `u32`.
        fn num(&self, i: usize, tag: u32) -> Option<u32> {
            find_tag(&self.frames[i], 0, tag)
                .and_then(|s| parse_fix_uint(s.slice(&self.frames[i])).ok())
        }
        /// A body tag's raw bytes.
        fn val(&self, i: usize, tag: u32) -> Option<&[u8]> {
            find_tag(&self.frames[i], 0, tag).map(|s| s.slice(&self.frames[i]))
        }
        /// Whether a body tag is present.
        fn has(&self, i: usize, tag: u32) -> bool {
            find_tag(&self.frames[i], 0, tag).is_some()
        }
    }

    impl Emit for RecordingEmitter {
        type Error = SessionError;

        fn emit<M: AdminEncode>(&mut self, msg: M) -> Result<(), SessionError> {
            let mut buf = [0u8; 512];
            let hdr = AdminHeader {
                seq: msg.seq(),
                sender: b"SENDER",
                target: b"TARGET",
                ts: b"20260101-00:00:00.000",
            };
            let mut fmt = FrameFormatter::new(&mut buf, MockDict::BEGIN_STRING, M::MSG_TYPE);
            msg.encode::<MockDict>(&mut fmt, &hdr);
            msg.customize(
                &mut NoCustomizer,
                &mut AdminMsgOut::new(&mut fmt, &hdr, M::MSG_TYPE, M::owned::<MockDict>()),
            );
            let (start, len) = fmt.finish().expect("admin frame fits the scratch buffer");
            self.frames.push(buf[start..start + len].to_vec());
            Ok(())
        }
    }

    fn establish(s: &mut SessionState) {
        let mut recorder = RecordingEmitter::new();
        s.connect(&mut recorder).unwrap();
        s.on_logon(
            LogonIn {
                seq: 1,
                heart_bt_int_s: 30,
                is_reset_seq_num: false,
            },
            &mut recorder,
        )
        .unwrap();
    }

    #[test]
    fn allocate_seq_errors_at_i32_max() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        s.next_outbound = SEQ_MAX + 1;
        assert_eq!(s.allocate_seq(), Err(SessionError::SeqNumExhausted));
    }

    #[test]
    fn bump_outbound_disconnects_at_i32_max() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        s.next_outbound = SEQ_MAX + 1;
        let ctrl = s.logout(None, &mut RecordingEmitter::new()).unwrap();
        assert_eq!(
            ctrl,
            Control::Disconnected {
                reason: DisconnectReason::SeqNumExhausted
            }
        );
    }

    #[test]
    fn logout_reason_rides_text_58() {
        // A `Some(reason)` threads through the state machine into the emitted
        // Logout's `Text(58)`; `None` omits the field. The RecordingEmitter
        // encodes the real `AdminEncode` frame, so this pins the wire output.
        let reason = AsciiTextStr::try_from_str("shutting down").unwrap();

        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        let mut with = RecordingEmitter::new();
        s.logout(Some(reason), &mut with).unwrap();
        assert_eq!(with.mt(0), b"5");
        assert_eq!(with.val(0, 58), Some(b"shutting down".as_slice()));

        let mut s2 = SessionState::new(Duration::from_secs(30));
        establish(&mut s2);
        let mut without = RecordingEmitter::new();
        s2.logout(None, &mut without).unwrap();
        assert_eq!(without.mt(0), b"5");
        assert!(!without.has(0, 58), "a bare Logout carries no Text(58)");
    }

    #[test]
    fn reject_logon_reason_rides_text_58() {
        // Rejecting a peer Logon emits a Logout; a `Some(reason)` rides as
        // `Text(58)`.
        let reason = AsciiTextStr::try_from_str("auth failed").unwrap();
        let mut s = SessionState::new(Duration::from_secs(30));
        let mut rec = RecordingEmitter::new();
        s.reject_logon(Some(reason), &mut rec).unwrap();
        assert_eq!(rec.mt(0), b"5");
        assert_eq!(rec.val(0, 58), Some(b"auth failed".as_slice()));
        assert_eq!(s.state(), State::Disconnected);
    }

    #[test]
    fn connect_reset_clears_seqnums() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        s.allocate_seq().unwrap();
        // Reach Disconnected via a clean logout: we initiate (→ LogoutPending),
        // the peer's in-sequence Logout confirms it (→ Disconnected).
        s.logout(None, &mut RecordingEmitter::new()).unwrap();
        s.on_logout(
            LogoutIn {
                seq: 2,
                is_poss_dup: false,
            },
            &mut RecordingEmitter::new(),
        )
        .unwrap();
        assert_eq!(s.state(), State::Disconnected);
        let mut recorder = RecordingEmitter::new();
        s.connect_reset(&mut recorder).unwrap();
        assert_eq!(recorder.len(), 1);
        // LogonReset is 35=A carrying ResetSeqNumFlag(141)=Y, at seqnum 1.
        assert_eq!(recorder.mt(0), b"A");
        assert!(recorder.has(0, 141), "LogonReset must carry 141=Y");
        assert_eq!(recorder.num(0, 34), Some(1));
        assert_eq!(s.next_outbound_seq(), 2);
        assert_eq!(s.next_inbound_seq(), 1);
    }

    #[test]
    fn connect_reset_wrong_state_returns_err() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        // The wrong-state guard returns before any emit; the emitter records nothing.
        assert_eq!(
            s.connect_reset(&mut RecordingEmitter::new()),
            Err(SessionError::InvalidState)
        );
    }

    #[test]
    fn reset_sequence_wrong_state_returns_err() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let mut recorder = RecordingEmitter::new();
        assert_eq!(
            s.reset_sequence(&mut recorder),
            Err(SessionError::InvalidState)
        ); // Disconnected
        s.connect(&mut recorder).unwrap();
        assert_eq!(
            s.reset_sequence(&mut recorder),
            Err(SessionError::InvalidState)
        ); // LogonSent
    }

    #[test]
    fn in_session_reset_initiator_roundtrip() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        s.allocate_seq().unwrap(); // seq 2
        s.allocate_seq().unwrap(); // seq 3

        // Initiate reset: sends TestRequest, enters AwaitingResetDrain.
        let mut recorder = RecordingEmitter::new();
        s.reset_sequence(&mut recorder).unwrap();
        assert_eq!(s.state(), State::AwaitingResetDrain);
        assert_eq!(recorder.len(), 1);
        // TestRequest (35=1) carrying TestReqID(112)=1.
        assert_eq!(recorder.mt(0), b"1");
        assert_eq!(recorder.num(0, 112), Some(1));

        // allocate_seq blocked.
        assert_eq!(s.allocate_seq(), Err(SessionError::ResetInProgress));

        // Non-drain heartbeat: wrong echo — drain NOT triggered.
        recorder.clear();
        s.on_heartbeat(
            HeartbeatIn {
                echo_id: None,
                seq: 2,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap();
        assert_eq!(s.state(), State::AwaitingResetDrain);
        assert_eq!(recorder.len(), 0);

        // Drain heartbeat: correct echo + seq in order → sends LogonReset(seq=1), → AwaitingResetAck.
        recorder.clear();
        s.on_heartbeat(
            HeartbeatIn {
                echo_id: Some(1),
                seq: 3,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap();
        assert_eq!(s.state(), State::AwaitingResetAck);
        assert_eq!(s.next_outbound_seq(), 2); // LogonReset consumed seq 1
        assert_eq!(recorder.len(), 1);
        assert_eq!(recorder.mt(0), b"A");
        assert!(recorder.has(0, 141), "reset Logon must carry 141=Y");
        assert_eq!(recorder.num(0, 34), Some(1));

        // Peer acks with Logon(141=Y, seq=1): reset complete, → Active.
        recorder.clear();
        let ctrl = s
            .on_logon(
                LogonIn {
                    seq: 1,
                    heart_bt_int_s: 30,
                    is_reset_seq_num: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(s.state(), State::Active);
        assert_eq!(s.next_inbound_seq(), 2);
        assert_eq!(ctrl, Control::Logon { acknowledged: true });
    }

    #[test]
    fn in_flight_app_delivered_during_drain() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        s.allocate_seq().unwrap(); // seq 2

        let mut recorder = RecordingEmitter::new();
        s.reset_sequence(&mut recorder).unwrap(); // → AwaitingResetDrain
        assert_eq!(s.state(), State::AwaitingResetDrain);

        // App message arrives with old inbound seq while draining.
        recorder.clear();
        let ctrl = s
            .on_app(
                AppIn {
                    seq: 2,
                    is_poss_dup: false,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(ctrl, Control::Application);
        assert_eq!(s.next_inbound_seq(), 3);
        assert_eq!(s.state(), State::AwaitingResetDrain);
    }

    #[test]
    fn in_session_reset_responder() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        s.allocate_seq().unwrap(); // seq 2
        s.allocate_seq().unwrap(); // seq 3

        // Peer sends Logon(141=Y, seq=1) while we are Active: surfaces a reset
        // decision (no auto-reply), which the user then accepts.
        let mut recorder = RecordingEmitter::new();
        let ctrl = s
            .on_logon(
                LogonIn {
                    seq: 1,
                    heart_bt_int_s: 30,
                    is_reset_seq_num: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(
            ctrl,
            Control::LogonResetRequest {
                seq: 1,
                heart_bt_int_s: 30
            }
        );
        assert_eq!(
            recorder.len(),
            0,
            "no reply emitted before the user accepts"
        );
        assert_eq!(s.state(), State::Active, "state unchanged until accept");

        // The user accepts: the LogonReset reply is emitted and the reset completes.
        let ctrl = s.accept_logon(1, 30, true, &mut recorder).unwrap();
        assert_eq!(s.state(), State::Active);
        assert_eq!(s.next_outbound_seq(), 2); // reply Logon consumed seq 1
        assert_eq!(s.next_inbound_seq(), 2);
        assert_eq!(recorder.len(), 1);
        // Reply is a LogonReset (35=A, 141=Y) at seqnum 1.
        assert_eq!(recorder.mt(0), b"A");
        assert!(recorder.has(0, 141), "reply must carry 141=Y");
        assert_eq!(recorder.num(0, 34), Some(1));
        assert_eq!(
            ctrl,
            Control::Logon {
                acknowledged: false
            }
        );
    }

    #[test]
    fn reset_ack_without_flag_disconnects() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        let mut recorder = RecordingEmitter::new();
        s.reset_sequence(&mut recorder).unwrap();
        s.on_heartbeat(
            HeartbeatIn {
                echo_id: Some(1),
                seq: 2,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap(); // → AwaitingResetAck

        // Peer replies without 141=Y.
        let ctrl = s
            .on_logon(
                LogonIn {
                    seq: 1,
                    heart_bt_int_s: 30,
                    is_reset_seq_num: false,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(
            ctrl,
            Control::Disconnected {
                reason: DisconnectReason::ProtocolViolation
            }
        );
    }

    #[test]
    fn sequence_reset_backward_sends_reject() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        let mut recorder = RecordingEmitter::new();
        let ctrl = s
            .on_sequence_reset(
                SequenceResetIn {
                    seq: 100,
                    new_seq: 1,
                    is_poss_dup: false,
                    is_gap_fill: false,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(ctrl, Control::SequenceReset);
        assert_eq!(recorder.len(), 1);
        // Reject (35=3): RefSeqNum(45)=100, RefTagID(371)=36, SessionRejectReason(373)=5.
        assert_eq!(recorder.mt(0), b"3");
        assert_eq!(recorder.num(0, 45), Some(100));
        assert_eq!(recorder.val(0, 371), Some(b"36".as_ref()));
        assert_eq!(recorder.num(0, 373), Some(5));
        assert_eq!(s.next_inbound_seq(), 2, "next_inbound must not advance");
    }

    #[test]
    fn reject_inbound_sends_reject_and_advances_seq() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        let mut recorder = RecordingEmitter::new();
        s.on_reject_inbound(
            RejectInboundIn {
                seq: 2,
                ref_tag_id: Some(35),
                session_reject_reason: 1,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap();
        assert_eq!(recorder.len(), 1);
        // Reject: RefSeqNum(45)=2, RefTagID(371)=35, SessionRejectReason(373)=1.
        assert_eq!(recorder.mt(0), b"3");
        assert_eq!(recorder.num(0, 45), Some(2));
        assert_eq!(recorder.val(0, 371), Some(b"35".as_ref()));
        assert_eq!(recorder.num(0, 373), Some(1));
        assert_eq!(s.next_inbound_seq(), 3);
    }

    #[test]
    fn reject_inbound_gap_surfaces_gap_detected() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        let mut recorder = RecordingEmitter::new();
        // A gap on the to-be-rejected message opens recovery: the engine surfaces
        // GapDetected (the user drives the ResendRequest) and emits nothing.
        let ctrl = s
            .on_reject_inbound(
                RejectInboundIn {
                    seq: 5,
                    ref_tag_id: Some(35),
                    session_reject_reason: 1,
                    is_poss_dup: false,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(ctrl, Control::GapDetected { begin: 2 });
        assert_eq!(recorder.len(), 0, "gap emits nothing; the user resends");
        assert_eq!(s.state(), State::Resending);
        assert_eq!(
            s.next_inbound_seq(),
            2,
            "next_inbound must not advance on gap"
        );
    }

    // ── suppression on gap/duplicate for the admin handlers ──────────────────
    //
    // The session layer surfaces only in-sequence, first-time admin messages.
    // An out-of-sequence frame is a recovery event (emit a ResendRequest, do not
    // surface); a PossDup duplicate below the expected seqnum is ignored (no
    // ResendRequest, no disconnect, not surfaced). Each handler returns
    // `Control::None` in both cases. In-sequence, it surfaces its own kind.

    /// Advances `next_inbound` from 2 to 3 by consuming an in-sequence app at
    /// seq 2, so a later `seq 2` PossDup frame is a genuine duplicate (< 3).
    fn consume_seq_2(s: &mut SessionState) {
        assert_eq!(
            s.on_app(
                AppIn {
                    seq: 2,
                    is_poss_dup: false,
                },
                &mut RecordingEmitter::new()
            )
            .unwrap(),
            Control::Application
        );
        assert_eq!(s.next_inbound_seq(), 3);
    }

    #[test]
    fn heartbeat_out_of_sequence_surfaces_gap_detected() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s); // next_inbound = 2
        let mut recorder = RecordingEmitter::new();
        // seq 5 > 2: gap. The Heartbeat itself is not surfaced; the gap is.
        let ctrl = s
            .on_heartbeat(
                HeartbeatIn {
                    echo_id: None,
                    seq: 5,
                    is_poss_dup: false,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(ctrl, Control::GapDetected { begin: 2 });
        assert_eq!(recorder.len(), 0, "gap emits nothing; the user resends");
        assert_eq!(s.state(), State::Resending);
    }

    #[test]
    fn heartbeat_duplicate_suppressed_no_resend() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        consume_seq_2(&mut s); // next_inbound = 3
        let mut recorder = RecordingEmitter::new();
        // seq 2 < 3 with PossDup: duplicate.
        let ctrl = s
            .on_heartbeat(
                HeartbeatIn {
                    echo_id: None,
                    seq: 2,
                    is_poss_dup: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(
            ctrl,
            Control::None,
            "duplicate Heartbeat must be suppressed"
        );
        assert_eq!(recorder.len(), 0, "duplicate must not emit a ResendRequest");
        assert_eq!(s.state(), State::Active, "duplicate must not disconnect");
    }

    #[test]
    fn heartbeat_in_sequence_surfaces() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        let mut recorder = RecordingEmitter::new();
        let ctrl = s
            .on_heartbeat(
                HeartbeatIn {
                    echo_id: None,
                    seq: 2,
                    is_poss_dup: false,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(ctrl, Control::Heartbeat);
        assert_eq!(recorder.len(), 0);
    }

    #[test]
    fn test_request_out_of_sequence_surfaces_gap_detected() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        let mut recorder = RecordingEmitter::new();
        let ctrl = s
            .on_test_request(
                TestRequestIn {
                    seq: 5,
                    is_poss_dup: false,
                },
                &mut recorder,
            )
            .unwrap();
        // A gap surfaces GapDetected and emits nothing — no Heartbeat echo (which
        // is Proceed-only) and no engine ResendRequest (the user drives it).
        assert_eq!(ctrl, Control::GapDetected { begin: 2 });
        assert_eq!(recorder.len(), 0);
        assert_eq!(s.state(), State::Resending);
    }

    #[test]
    fn test_request_duplicate_suppressed_no_echo() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        consume_seq_2(&mut s); // next_inbound = 3
        let mut recorder = RecordingEmitter::new();
        let ctrl = s
            .on_test_request(
                TestRequestIn {
                    seq: 2,
                    is_poss_dup: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(
            ctrl,
            Control::None,
            "duplicate TestRequest must be suppressed"
        );
        assert_eq!(
            recorder.len(),
            0,
            "duplicate must not emit a Heartbeat echo or ResendRequest"
        );
        assert_eq!(s.state(), State::Active);
    }

    #[test]
    fn reject_out_of_sequence_surfaces_gap_detected() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        let mut recorder = RecordingEmitter::new();
        let ctrl = s
            .on_reject(
                RejectIn {
                    seq: 5,
                    is_poss_dup: false,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(ctrl, Control::GapDetected { begin: 2 });
        assert_eq!(recorder.len(), 0, "gap emits nothing; the user resends");
        assert_eq!(s.state(), State::Resending);
    }

    #[test]
    fn reject_duplicate_suppressed_no_resend() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        consume_seq_2(&mut s); // next_inbound = 3
        let mut recorder = RecordingEmitter::new();
        let ctrl = s
            .on_reject(
                RejectIn {
                    seq: 2,
                    is_poss_dup: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(ctrl, Control::None, "duplicate Reject must be suppressed");
        assert_eq!(recorder.len(), 0);
        assert_eq!(s.state(), State::Active);
    }

    #[test]
    fn sequence_reset_gap_fill_out_of_sequence_suppressed_and_resends() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s); // next_inbound = 2
        let mut recorder = RecordingEmitter::new();
        // GapFill (is_gap_fill = true) at seq 5 > 2: out of sequence.
        let ctrl = s
            .on_sequence_reset(
                SequenceResetIn {
                    seq: 5,
                    new_seq: 9,
                    is_poss_dup: false,
                    is_gap_fill: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(
            ctrl,
            Control::GapDetected { begin: 2 },
            "out-of-sequence GapFill must surface a gap"
        );
        assert_eq!(recorder.len(), 0, "gap emits nothing; the user resends");
        assert_eq!(s.state(), State::Resending);
        // Proceed-only work (advance to new_seq) must NOT run on a gap.
        assert_eq!(
            s.next_inbound_seq(),
            2,
            "next_inbound must not advance to new_seq on a gap"
        );
    }

    #[test]
    fn sequence_reset_gap_fill_below_expected_possdup_discarded() {
        // A below-expected GapFill carrying PossDup=Y is a benign duplicate (the
        // classic overlapping-ResendRequest race) — discarded, session survives,
        // next_inbound unchanged. Matches FIX 4.4 / QuickFIX.
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        consume_seq_2(&mut s); // next_inbound = 3
        let mut recorder = RecordingEmitter::new();
        // seq 2 < 3, PossDup = true.
        let ctrl = s
            .on_sequence_reset(
                SequenceResetIn {
                    seq: 2,
                    new_seq: 9,
                    is_poss_dup: true,
                    is_gap_fill: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(
            ctrl,
            Control::None,
            "a below-expected GapFill with PossDup is discarded, not a disconnect"
        );
        assert_eq!(
            s.next_inbound_seq(),
            3,
            "next_inbound must not advance on the discarded GapFill"
        );
    }

    #[test]
    fn sequence_reset_gap_fill_below_expected_no_possdup_disconnects() {
        // Without PossDup, a below-expected GapFill is a genuine too-low error.
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        consume_seq_2(&mut s); // next_inbound = 3
        let mut recorder = RecordingEmitter::new();
        // seq 2 < 3, PossDup = false.
        let ctrl = s
            .on_sequence_reset(
                SequenceResetIn {
                    seq: 2,
                    new_seq: 9,
                    is_poss_dup: false,
                    is_gap_fill: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(
            ctrl,
            Control::Disconnected {
                reason: DisconnectReason::SeqNumTooLow
            },
            "a below-expected GapFill without PossDup disconnects"
        );
        assert_eq!(
            s.next_inbound_seq(),
            3,
            "next_inbound must not advance on the too-low GapFill"
        );
    }

    #[test]
    fn sequence_reset_gap_fill_in_sequence_surfaces_and_advances() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s); // next_inbound = 2
        let mut recorder = RecordingEmitter::new();
        // In-sequence GapFill at seq 2 advancing to new_seq 7.
        let ctrl = s
            .on_sequence_reset(
                SequenceResetIn {
                    seq: 2,
                    new_seq: 7,
                    is_poss_dup: false,
                    is_gap_fill: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(ctrl, Control::SequenceReset);
        assert_eq!(s.next_inbound_seq(), 7, "in-sequence GapFill advances");
        assert_eq!(recorder.len(), 0);
    }

    #[test]
    fn logout_out_of_sequence_suppressed_and_resends() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s); // Active, next_inbound = 2
        let mut recorder = RecordingEmitter::new();
        // seq 5 > 2: gap. A gap Logout must be suppressed (ResendRequest), NOT
        // treated as a logout exchange.
        let ctrl = s
            .on_logout(
                LogoutIn {
                    seq: 5,
                    is_poss_dup: false,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(
            ctrl,
            Control::GapDetected { begin: 2 },
            "a gap Logout surfaces the gap, not the Logout"
        );
        assert_eq!(recorder.len(), 0, "gap emits nothing; the user resends");
        assert_eq!(
            s.state(),
            State::Resending,
            "gap Logout must not disconnect the session"
        );
    }

    #[test]
    fn logout_duplicate_suppressed_no_disconnect() {
        let mut s = SessionState::new(Duration::from_secs(30));
        establish(&mut s);
        consume_seq_2(&mut s); // next_inbound = 3
        let mut recorder = RecordingEmitter::new();
        // seq 2 < 3 with PossDup: duplicate Logout — ignored, session survives.
        let ctrl = s
            .on_logout(
                LogoutIn {
                    seq: 2,
                    is_poss_dup: true,
                },
                &mut recorder,
            )
            .unwrap();
        assert_eq!(ctrl, Control::None, "duplicate Logout must be suppressed");
        assert_eq!(recorder.len(), 0);
        assert_eq!(
            s.state(),
            State::Active,
            "duplicate Logout must not disconnect the session"
        );
    }
}
