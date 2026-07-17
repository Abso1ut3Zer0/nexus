mod event;

use std::time::{Duration, Instant};

pub use event::{Control, DisconnectReason, State};
use nexus_fix_codec::{
    AdminEncode, Heartbeat, Logon, LogonReset, Logout, Reject, ResendRequest, TestReqId,
    TestRequest,
};

use crate::framework::SessionError;

const SEQ_MAX: u32 = i32::MAX as u32;

/// Sink for the outbound admin messages the state machine emits.
///
/// The one generic method is why this is a trait and not a closure: `emit` must
/// be generic over the concrete [`AdminEncode`] message type, and a closure
/// cannot be generic over its parameter. Each [`SessionState`] handler takes a
/// `&mut S: AdminSink` and calls `sink.emit(ResendRequest { .. })` with the
/// concrete struct — the type is never erased into a sum and matched back apart.
///
/// The driver supplies the production impl (`Emitter`), which encodes the frame
/// and journals it; tests supply a recording or discarding sink. Each admin
/// carries its own pre-allocated `MsgSeqNum(34)` in `seq`; for a GapFill-mode
/// `SequenceReset` that is the start of the gap-filled range (encoded
/// `PossDupFlag=Y`), for every other message the next consumed outbound seqnum.
pub trait AdminSink {
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
/// but the exhaustion path returns a *success* value (`Ok(Control::Disconnected)`,
/// surfaced as `Message::Disconnected`) rather than an `Err`, so it cannot ride
/// `?`. This macro packages the `match` + early `return` so the ~8 handler sites
/// that consume an outbound seqnum share one definition of disconnect-on-exhaustion.
macro_rules! seq {
    ($self:ident, $now:ident) => {
        match $self.bump_outbound($now) {
            Some(s) => s,
            None => return Ok($self.disconnect(DisconnectReason::SeqNumExhausted)),
        }
    };
}

/// Pure FIX session state machine.
///
/// Owns sequence numbers, timers, and state transitions. The framework above
/// owns the transport, clock, and wire encoding. Each typed handler receives
/// pre-decoded admin fields plus an [`AdminSink`] for outbound admin messages,
/// and returns a [`Control`] verdict. Never allocates.
pub struct SessionState {
    state: State,
    hb: Duration,
    next_outbound: u32,
    next_inbound: u32,
    gap_high: u32,
    last_sent: Option<Instant>,
    last_received: Option<Instant>,
    test_request_sent: Option<Instant>,
    state_entered: Option<Instant>,
    test_req_counter: u64,
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
            last_sent: None,
            last_received: None,
            test_request_sent: None,
            state_entered: None,
            test_req_counter: 0,
        }
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

    /// Allocates the next outbound sequence number for an application message
    /// and updates the outbound activity timestamp used by the heartbeat timer.
    ///
    /// Returns `Err(SeqNumExhausted)` when `next_outbound` has reached `i32::MAX`.
    /// Returns `Err(ResetInProgress)` while an in-session reset handshake is active.
    pub fn allocate_seq(&mut self, now: Instant) -> Result<u32, SessionError> {
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
        self.last_sent = Some(now);
        Ok(s)
    }

    /// Bumps the next outbound sequence number, updating the outbound activity
    /// timestamp. Returns `None` when exhausted (`next_outbound > i32::MAX`); the
    /// caller decides the disconnect (see the [`seq!`] macro). No internal side
    /// effect on exhaustion.
    fn bump_outbound(&mut self, now: Instant) -> Option<u32> {
        if self.next_outbound > SEQ_MAX {
            return None;
        }
        let s = self.next_outbound;
        self.next_outbound += 1;
        self.last_sent = Some(now);
        Some(s)
    }

    /// Earliest instant at which [`on_timeout`](Self::on_timeout) has work.
    pub fn next_timeout(&self) -> Option<Instant> {
        match self.state {
            State::Disconnected => None,
            State::LogonSent
            | State::LogoutPending
            | State::AwaitingResetDrain
            | State::AwaitingResetAck => self.state_entered.map(|t| t + self.hb),
            State::Active | State::Resending => {
                let outbound = self.last_sent.map(|t| t + self.hb);
                let inbound = self.test_request_sent.map_or_else(
                    || self.last_received.map(|t| t + self.inbound_grace()),
                    |t| Some(t + self.hb),
                );
                match (outbound, inbound) {
                    (Some(a), Some(b)) => Some(a.min(b)),
                    (a, b) => a.or(b),
                }
            }
        }
    }

    /// Initiates a session: sends a Logon. No-op if not disconnected.
    ///
    /// Emits: Logon.
    pub fn connect<S: AdminSink>(
        &mut self,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        if self.state != State::Disconnected {
            return Ok(Control::None);
        }
        let seq = seq!(self, now);
        sink.emit(Logon {
            seq,
            heart_bt_int_s: self.hb.as_secs() as u32,
        })?;
        self.state = State::LogonSent;
        self.state_entered = Some(now);
        self.last_received = Some(now);
        Ok(Control::None)
    }

    /// Initiates a session with `ResetSeqNumFlag(141)=Y`: resets both sequence
    /// counters to 1 and sends a Logon. Returns `Err(SessionError::InvalidState)`
    /// if not disconnected.
    ///
    /// Emits: LogonReset.
    pub fn connect_reset<S: AdminSink>(
        &mut self,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error>
    where
        S::Error: From<SessionError>,
    {
        if self.state != State::Disconnected {
            return Err(SessionError::InvalidState.into());
        }
        self.next_outbound = 1;
        self.next_inbound = 1;
        let seq = seq!(self, now);
        sink.emit(LogonReset {
            seq,
            heart_bt_int_s: self.hb.as_secs() as u32,
        })?;
        self.state = State::LogonSent;
        self.state_entered = Some(now);
        self.last_received = Some(now);
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
    pub fn reset_sequence<S: AdminSink>(
        &mut self,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error>
    where
        S::Error: From<SessionError>,
    {
        if self.state != State::Active {
            return Err(SessionError::InvalidState.into());
        }
        self.test_req_counter += 1;
        let seq = seq!(self, now);
        sink.emit(TestRequest {
            seq,
            id: self.test_req_counter,
        })?;
        self.test_request_sent = Some(now);
        self.state = State::AwaitingResetDrain;
        self.state_entered = Some(now);
        Ok(Control::None)
    }

    /// Initiates a clean logout. No-op unless in an active state.
    ///
    /// Emits: Logout.
    pub fn logout<S: AdminSink>(
        &mut self,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        if !matches!(self.state, State::Active | State::Resending) {
            return Ok(Control::None);
        }
        let seq = seq!(self, now);
        sink.emit(Logout { seq })?;
        self.state = State::LogoutPending;
        self.state_entered = Some(now);
        Ok(Control::None)
    }

    /// Fires due timers: logon/logout/reset timeouts, heartbeat emission, and
    /// TestRequest probing. Call at or after [`next_timeout`](Self::next_timeout).
    ///
    /// Returns [`Control::Disconnected`] if a timeout drove a disconnect,
    /// otherwise [`Control::None`].
    ///
    /// Emits: Heartbeat | TestRequest | Logout.
    pub fn on_timeout<S: AdminSink>(
        &mut self,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        match self.state {
            State::Disconnected => {}
            State::LogonSent => {
                if let Some(t) = self.state_entered
                    && now.duration_since(t) >= self.hb
                {
                    return Ok(self.disconnect(DisconnectReason::LogonTimeout));
                }
            }
            State::LogoutPending => {
                if let Some(t) = self.state_entered
                    && now.duration_since(t) >= self.hb
                {
                    return Ok(self.disconnect(DisconnectReason::LogoutTimeout));
                }
            }
            State::AwaitingResetDrain | State::AwaitingResetAck => {
                if let Some(t) = self.state_entered
                    && now.duration_since(t) >= self.hb
                {
                    return Ok(self.disconnect(DisconnectReason::ResetTimeout));
                }
            }
            State::Active | State::Resending => {
                if let Some(t) = self.test_request_sent {
                    if now.duration_since(t) >= self.hb {
                        let seq = seq!(self, now);
                        sink.emit(Logout { seq })?;
                        return Ok(self.disconnect(DisconnectReason::TestRequestTimeout));
                    }
                } else if let Some(t) = self.last_received
                    && now.duration_since(t) >= self.inbound_grace()
                {
                    self.test_req_counter += 1;
                    let seq = seq!(self, now);
                    sink.emit(TestRequest {
                        seq,
                        id: self.test_req_counter,
                    })?;
                    self.test_request_sent = Some(now);
                }
                if let Some(t) = self.last_sent
                    && now.duration_since(t) >= self.hb
                {
                    let seq = seq!(self, now);
                    sink.emit(Heartbeat { seq, echo: None })?;
                }
            }
        }
        Ok(Control::None)
    }

    /// Handles a received Logon.
    ///
    /// Set `send_reply = true` when acting as acceptor; the session emits a Logon
    /// reply via `sink`. Pass `false` for the initiator's incoming reply. Returns
    /// [`Control::Logon`] with `acknowledged = !send_reply`.
    ///
    /// Emits: Logon | LogonReset | Logout | ResendRequest.
    pub fn on_logon<S: AdminSink>(
        &mut self,
        seq: u32,
        heart_bt_int_s: u32,
        reset_seq_num: bool,
        send_reply: bool,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        // Acceptor sends its own Logon reply; the initiator receives an ack.
        // `acknowledged` is the mirror of `send_reply`.
        let acknowledged = !send_reply;
        self.last_received = Some(now);
        self.test_request_sent = None;

        // Reset ack: we initiated the reset and peer is confirming.
        if self.state == State::AwaitingResetAck {
            if !reset_seq_num || seq != 1 {
                return Ok(self.disconnect(DisconnectReason::ProtocolViolation));
            }
            self.hb = Duration::from_secs(u64::from(heart_bt_int_s));
            self.next_inbound = 2;
            self.state = State::Active;
            self.state_entered = None;
            return Ok(Control::Logon { acknowledged });
        }

        // Peer-initiated reset while we are active.
        if matches!(self.state, State::Active | State::Resending) && reset_seq_num {
            if seq != 1 {
                return Ok(self.disconnect(DisconnectReason::ProtocolViolation));
            }
            self.hb = Duration::from_secs(u64::from(heart_bt_int_s));
            self.next_outbound = 1;
            let reply_seq = seq!(self, now);
            sink.emit(LogonReset {
                seq: reply_seq,
                heart_bt_int_s: self.hb.as_secs() as u32,
            })?;
            self.next_inbound = 2;
            self.state = State::Active;
            return Ok(Control::Logon { acknowledged });
        }

        // Normal logon: acceptor or initiator's ack.
        let valid = if send_reply {
            self.state == State::Disconnected
        } else {
            self.state == State::LogonSent
        };
        if !valid {
            return Ok(Control::Logon { acknowledged });
        }

        if reset_seq_num {
            self.next_inbound = 1;
            if send_reply {
                self.next_outbound = 1;
            }
        }
        self.hb = Duration::from_secs(u64::from(heart_bt_int_s));

        if send_reply {
            let reply_seq = seq!(self, now);
            if reset_seq_num {
                sink.emit(LogonReset {
                    seq: reply_seq,
                    heart_bt_int_s,
                })?;
            } else {
                sink.emit(Logon {
                    seq: reply_seq,
                    heart_bt_int_s,
                })?;
            }
        }

        if seq < self.next_inbound {
            let logout_seq = seq!(self, now);
            sink.emit(Logout { seq: logout_seq })?;
            return Ok(self.disconnect(DisconnectReason::SeqNumTooLow));
        }

        if seq > self.next_inbound {
            self.gap_high = seq;
            let rr_seq = seq!(self, now);
            sink.emit(ResendRequest {
                seq: rr_seq,
                begin: self.next_inbound,
            })?;
            self.state = State::Resending;
        } else {
            self.next_inbound += 1;
            self.state = State::Active;
        }
        Ok(Control::Logon { acknowledged })
    }

    /// Handles a received Logout.
    ///
    /// Emits (some via `validate_seq`): ResendRequest | Logout.
    pub fn on_logout<S: AdminSink>(
        &mut self,
        seq: u32,
        poss_dup: bool,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        self.last_received = Some(now);
        self.test_request_sent = None;
        if self.state == State::LogonSent {
            return Ok(self.disconnect(DisconnectReason::Logout));
        }
        if matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            match self.validate_seq(seq, poss_dup, now, sink)? {
                // In-sequence Logout: complete the exchange and disconnect.
                Control::Proceed => {
                    if self.state != State::LogoutPending {
                        let logout_seq = seq!(self, now);
                        sink.emit(Logout { seq: logout_seq })?;
                    }
                    return Ok(self.disconnect(DisconnectReason::Logout));
                }
                // Gap/duplicate: suppressed (ResendRequest already emitted, or a
                // PossDup-too-low frame ignored). Too-low without PossDup:
                // disconnect. Neither surfaces the Logout.
                ctrl => return Ok(ctrl),
            }
        }
        // Out-of-state (e.g. mid-reset) Logout. The in-sequence path above always
        // disconnects, so this is the only path that surfaces a Logout message.
        Ok(Control::Logout)
    }

    /// Handles a received Heartbeat. `echo_id` is `TestReqID(112)` parsed as `u64`, if present.
    ///
    /// Emits (some via `validate_seq`): LogonReset | ResendRequest | Logout.
    pub fn on_heartbeat<S: AdminSink>(
        &mut self,
        seq: u32,
        poss_dup: bool,
        echo_id: Option<u64>,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        self.last_received = Some(now);
        self.test_request_sent = None;

        if self.state == State::AwaitingResetDrain {
            let echo_matches = echo_id == Some(self.test_req_counter);
            if echo_matches && seq == self.next_inbound {
                // Drain confirmed: all in-flight messages received, send LogonReset.
                self.next_inbound += 1;
                self.next_outbound = 1;
                let logon_seq = seq!(self, now);
                sink.emit(LogonReset {
                    seq: logon_seq,
                    heart_bt_int_s: self.hb.as_secs() as u32,
                })?;
                self.state = State::AwaitingResetAck;
                self.state_entered = Some(now);
                return Ok(Control::Heartbeat);
            }
            // Not the drain confirm: validate sequence normally.
            match self.validate_seq(seq, poss_dup, now, sink)? {
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
        match self.validate_seq(seq, poss_dup, now, sink)? {
            Control::Proceed => self.check_resend_done(),
            // Gap/duplicate: suppressed, not surfaced.
            ctrl => return Ok(ctrl),
        }
        Ok(Control::Heartbeat)
    }

    /// Handles a received TestRequest. Replies with a Heartbeat echoing the TestReqID.
    ///
    /// Emits (some via `validate_seq`): Heartbeat | ResendRequest | Logout.
    pub fn on_test_request<S: AdminSink>(
        &mut self,
        seq: u32,
        poss_dup: bool,
        test_req_id: &[u8],
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
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
        self.last_received = Some(now);
        self.test_request_sent = None;
        match self.validate_seq(seq, poss_dup, now, sink)? {
            // In-sequence only: reply with the echoing Heartbeat. A gap/dup must
            // not trigger a Heartbeat reply — it is a recovery event.
            Control::Proceed => {
                let hb_seq = seq!(self, now);
                sink.emit(Heartbeat {
                    seq: hb_seq,
                    echo: Some(TestReqId::new(test_req_id)),
                })?;
                self.check_resend_done();
            }
            // Gap/duplicate: suppressed, not surfaced.
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
    pub fn on_resend_request<S: AdminSink>(
        &mut self,
        seq: u32,
        poss_dup: bool,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Ok(Control::None);
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        match self.validate_seq(seq, poss_dup, now, sink)? {
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
    /// `gap_fill = false` is Reset mode: ignores `MsgSeqNum`, sets
    /// `next_inbound` to `new_seq`. `gap_fill = true` is GapFill mode:
    /// validates sequence, advances `next_inbound` to `new_seq`.
    ///
    /// Emits (some via `validate_seq`): Reject | ResendRequest | Logout.
    pub fn on_sequence_reset<S: AdminSink>(
        &mut self,
        seq: u32,
        new_seq: u32,
        gap_fill: bool,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Ok(Control::SequenceReset);
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        if gap_fill {
            match self.validate_seq(seq, false, now, sink)? {
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
                if let Some(reject_seq) = self.bump_outbound(now) {
                    sink.emit(Reject {
                        seq: reject_seq,
                        ref_seq_num: seq,
                        ref_tag_id: Some(36),
                        session_reject_reason: 5,
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
    pub fn on_reject<S: AdminSink>(
        &mut self,
        seq: u32,
        poss_dup: bool,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Ok(Control::Reject);
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        match self.validate_seq(seq, poss_dup, now, sink)? {
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
    pub fn on_app<S: AdminSink>(
        &mut self,
        seq: u32,
        poss_dup: bool,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
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
        self.last_received = Some(now);
        self.test_request_sent = None;
        match self.validate_seq(seq, poss_dup, now, sink)? {
            Control::Proceed => {}
            ctrl => return Ok(ctrl),
        }
        self.check_resend_done();
        Ok(Control::Application)
    }

    /// Sends a session-level Reject (35=3) for a received message that cannot be processed.
    ///
    /// Validates sequence then sends a Reject for `inbound_seq`. A gap sends ResendRequest instead.
    /// The session remains alive. No-op if the session is not in an active state.
    ///
    /// Emits (some via `validate_seq`): Reject | ResendRequest | Logout.
    pub fn on_reject_inbound<S: AdminSink>(
        &mut self,
        inbound_seq: u32,
        poss_dup: bool,
        ref_tag_id: Option<u32>,
        session_reject_reason: u8,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Ok(Control::None);
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        match self.validate_seq(inbound_seq, poss_dup, now, sink)? {
            Control::Proceed => {}
            ctrl => return Ok(ctrl),
        }
        let seq = seq!(self, now);
        sink.emit(Reject {
            seq,
            ref_seq_num: inbound_seq,
            ref_tag_id,
            session_reject_reason,
        })?;
        Ok(Control::None)
    }

    /// Handles a CompID mismatch detected by the framework. Sends Logout and disconnects.
    ///
    /// Emits: Logout.
    pub fn on_comp_id_mismatch<S: AdminSink>(
        &mut self,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        if self.state == State::Disconnected {
            return Ok(Control::None);
        }
        let seq = seq!(self, now);
        sink.emit(Logout { seq })?;
        Ok(self.disconnect(DisconnectReason::CompIdMismatch))
    }

    /// Validates an inbound sequence number, emitting a ResendRequest on a gap or
    /// a Logout on a too-low seqnum. Returns:
    /// - [`Control::Proceed`] — seq matched and advanced; caller keeps processing.
    /// - [`Control::None`] — a gap (ResendRequest emitted) or a `poss_dup`-too-low
    ///   frame (ignored). The caller propagates this as its own verdict, so the
    ///   message is suppressed: an out-of-sequence or duplicate frame is a recovery
    ///   event, never surfaced to the application.
    /// - [`Control::Disconnected`] — a too-low seqnum without `poss_dup`, or
    ///   outbound exhaustion while emitting.
    ///
    /// Emits: ResendRequest | Logout.
    fn validate_seq<S: AdminSink>(
        &mut self,
        seq: u32,
        poss_dup: bool,
        now: Instant,
        sink: &mut S,
    ) -> Result<Control, S::Error> {
        if seq > self.next_inbound {
            if self.gap_high < seq {
                self.gap_high = seq;
            }
            if self.state != State::Resending {
                let rr_seq = seq!(self, now);
                sink.emit(ResendRequest {
                    seq: rr_seq,
                    begin: self.next_inbound,
                })?;
                if self.state == State::Active {
                    self.state = State::Resending;
                }
            }
            return Ok(Control::None);
        }
        if seq < self.next_inbound {
            if poss_dup {
                return Ok(Control::None);
            }
            let logout_seq = seq!(self, now);
            sink.emit(Logout { seq: logout_seq })?;
            return Ok(self.disconnect(DisconnectReason::SeqNumTooLow));
        }
        self.next_inbound += 1;
        Ok(Control::Proceed)
    }

    /// Transitions to `Disconnected` and returns the matching verdict.
    fn disconnect(&mut self, reason: DisconnectReason) -> Control {
        self.state = State::Disconnected;
        self.test_request_sent = None;
        self.state_entered = None;
        Control::Disconnected { reason }
    }

    fn check_resend_done(&mut self) {
        if self.state == State::Resending && self.next_inbound > self.gap_high {
            self.state = State::Active;
        }
    }

    fn inbound_grace(&self) -> Duration {
        self.hb + self.hb / 5
    }
}

#[cfg(test)]
mod tests {
    use nexus_fix_codec::{
        AdminHeader, AdminMsgOut, AsciiTextStr, DecodeError, FieldView, FixAdminMsg, FixDictionary,
        FixHeader, FixTimestamp, FrameFormatter, NoCustomizer, find_tag, parse_fix_uint,
    };

    use super::*;

    // ── minimal dictionary so the recording sink can encode admin frames ─────

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

    // ── recording sink: captures each emitted admin as its encoded frame ─────

    /// An [`AdminSink`] that encodes each emitted message through the real
    /// `AdminEncode` path (into a `MockDict` frame) and records the frame bytes.
    /// Assertions decode the captured frame — `MsgType(35)` and body tags — so
    /// they pin the actual wire output, not a captured enum. `Error` is
    /// `SessionError` (trivially `From<SessionError>`), so the same sink drives
    /// both the plain handlers and the reset initiators whose wrong-state guard
    /// requires `S::Error: From<SessionError>`.
    struct Rec {
        frames: Vec<Vec<u8>>,
    }

    impl Rec {
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

    impl AdminSink for Rec {
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

    fn establish(s: &mut SessionState, now: Instant) {
        let mut rec = Rec::new();
        s.connect(now, &mut rec).unwrap();
        s.on_logon(1, 30, false, false, now, &mut rec).unwrap();
    }

    #[test]
    fn allocate_seq_errors_at_i32_max() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        s.next_outbound = SEQ_MAX + 1;
        assert_eq!(s.allocate_seq(now), Err(SessionError::SeqNumExhausted));
    }

    #[test]
    fn bump_outbound_disconnects_at_i32_max() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        s.next_outbound = SEQ_MAX + 1;
        let ctrl = s.logout(now, &mut Rec::new()).unwrap();
        assert_eq!(
            ctrl,
            Control::Disconnected {
                reason: DisconnectReason::SeqNumExhausted
            }
        );
    }

    #[test]
    fn connect_reset_clears_seqnums() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        s.allocate_seq(now).unwrap();
        s.on_logout(2, false, now, &mut Rec::new()).unwrap();
        assert_eq!(s.state(), State::Disconnected);
        let mut rec = Rec::new();
        s.connect_reset(now, &mut rec).unwrap();
        assert_eq!(rec.len(), 1);
        // LogonReset is 35=A carrying ResetSeqNumFlag(141)=Y, at seqnum 1.
        assert_eq!(rec.mt(0), b"A");
        assert!(rec.has(0, 141), "LogonReset must carry 141=Y");
        assert_eq!(rec.num(0, 34), Some(1));
        assert_eq!(s.next_outbound_seq(), 2);
        assert_eq!(s.next_inbound_seq(), 1);
    }

    #[test]
    fn connect_reset_wrong_state_returns_err() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        // The wrong-state guard returns before any emit; the sink records nothing.
        assert_eq!(
            s.connect_reset(now, &mut Rec::new()),
            Err(SessionError::InvalidState)
        );
    }

    #[test]
    fn reset_sequence_wrong_state_returns_err() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        let mut rec = Rec::new();
        assert_eq!(
            s.reset_sequence(now, &mut rec),
            Err(SessionError::InvalidState)
        ); // Disconnected
        s.connect(now, &mut rec).unwrap();
        assert_eq!(
            s.reset_sequence(now, &mut rec),
            Err(SessionError::InvalidState)
        ); // LogonSent
    }

    #[test]
    fn in_session_reset_initiator_roundtrip() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        s.allocate_seq(now).unwrap(); // seq 2
        s.allocate_seq(now).unwrap(); // seq 3

        // Initiate reset: sends TestRequest, enters AwaitingResetDrain.
        let mut rec = Rec::new();
        s.reset_sequence(now, &mut rec).unwrap();
        assert_eq!(s.state(), State::AwaitingResetDrain);
        assert_eq!(rec.len(), 1);
        // TestRequest (35=1) carrying TestReqID(112)=1.
        assert_eq!(rec.mt(0), b"1");
        assert_eq!(rec.num(0, 112), Some(1));

        // allocate_seq blocked.
        assert_eq!(s.allocate_seq(now), Err(SessionError::ResetInProgress));

        // Non-drain heartbeat: wrong echo — drain NOT triggered.
        rec.clear();
        s.on_heartbeat(2, false, None, now, &mut rec).unwrap();
        assert_eq!(s.state(), State::AwaitingResetDrain);
        assert_eq!(rec.len(), 0);

        // Drain heartbeat: correct echo + seq in order → sends LogonReset(seq=1), → AwaitingResetAck.
        rec.clear();
        s.on_heartbeat(3, false, Some(1), now, &mut rec).unwrap();
        assert_eq!(s.state(), State::AwaitingResetAck);
        assert_eq!(s.next_outbound_seq(), 2); // LogonReset consumed seq 1
        assert_eq!(rec.len(), 1);
        assert_eq!(rec.mt(0), b"A");
        assert!(rec.has(0, 141), "reset Logon must carry 141=Y");
        assert_eq!(rec.num(0, 34), Some(1));

        // Peer acks with Logon(141=Y, seq=1): reset complete, → Active.
        rec.clear();
        let ctrl = s.on_logon(1, 30, true, false, now, &mut rec).unwrap();
        assert_eq!(s.state(), State::Active);
        assert_eq!(s.next_inbound_seq(), 2);
        assert_eq!(ctrl, Control::Logon { acknowledged: true });
    }

    #[test]
    fn in_flight_app_delivered_during_drain() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        s.allocate_seq(now).unwrap(); // seq 2

        let mut rec = Rec::new();
        s.reset_sequence(now, &mut rec).unwrap(); // → AwaitingResetDrain
        assert_eq!(s.state(), State::AwaitingResetDrain);

        // App message arrives with old inbound seq while draining.
        rec.clear();
        let ctrl = s.on_app(2, false, now, &mut rec).unwrap();
        assert_eq!(ctrl, Control::Application);
        assert_eq!(s.next_inbound_seq(), 3);
        assert_eq!(s.state(), State::AwaitingResetDrain);
    }

    #[test]
    fn in_session_reset_responder() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        s.allocate_seq(now).unwrap(); // seq 2
        s.allocate_seq(now).unwrap(); // seq 3

        // Peer sends Logon(141=Y, seq=1) while we are Active.
        let mut rec = Rec::new();
        let ctrl = s.on_logon(1, 30, true, true, now, &mut rec).unwrap();
        assert_eq!(s.state(), State::Active);
        assert_eq!(s.next_outbound_seq(), 2); // reply Logon consumed seq 1
        assert_eq!(s.next_inbound_seq(), 2);
        assert_eq!(rec.len(), 1);
        // Reply is a LogonReset (35=A, 141=Y) at seqnum 1.
        assert_eq!(rec.mt(0), b"A");
        assert!(rec.has(0, 141), "reply must carry 141=Y");
        assert_eq!(rec.num(0, 34), Some(1));
        // send_reply = true → this Logon is one we answer, not an ack.
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
        let now = Instant::now();
        establish(&mut s, now);
        let mut rec = Rec::new();
        s.reset_sequence(now, &mut rec).unwrap();
        s.on_heartbeat(2, false, Some(1), now, &mut rec).unwrap(); // → AwaitingResetAck

        // Peer replies without 141=Y.
        let ctrl = s.on_logon(1, 30, false, false, now, &mut rec).unwrap();
        assert_eq!(
            ctrl,
            Control::Disconnected {
                reason: DisconnectReason::ProtocolViolation
            }
        );
    }

    #[test]
    fn reset_timeout_disconnects() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        let mut rec = Rec::new();
        s.reset_sequence(now, &mut rec).unwrap();
        s.on_heartbeat(2, false, Some(1), now, &mut rec).unwrap(); // → AwaitingResetAck
        let ctrl = s
            .on_timeout(now + Duration::from_secs(31), &mut rec)
            .unwrap();
        assert_eq!(
            ctrl,
            Control::Disconnected {
                reason: DisconnectReason::ResetTimeout
            }
        );
    }

    #[test]
    fn sequence_reset_backward_sends_reject() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        let mut rec = Rec::new();
        let ctrl = s.on_sequence_reset(100, 1, false, now, &mut rec).unwrap();
        assert_eq!(ctrl, Control::SequenceReset);
        assert_eq!(rec.len(), 1);
        // Reject (35=3): RefSeqNum(45)=100, RefTagID(371)=36, SessionRejectReason(373)=5.
        assert_eq!(rec.mt(0), b"3");
        assert_eq!(rec.num(0, 45), Some(100));
        assert_eq!(rec.val(0, 371), Some(b"36".as_ref()));
        assert_eq!(rec.num(0, 373), Some(5));
        assert_eq!(s.next_inbound_seq(), 2, "next_inbound must not advance");
    }

    #[test]
    fn reject_inbound_sends_reject_and_advances_seq() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        let mut rec = Rec::new();
        s.on_reject_inbound(2, false, Some(35), 1, now, &mut rec)
            .unwrap();
        assert_eq!(rec.len(), 1);
        // Reject: RefSeqNum(45)=2, RefTagID(371)=35, SessionRejectReason(373)=1.
        assert_eq!(rec.mt(0), b"3");
        assert_eq!(rec.num(0, 45), Some(2));
        assert_eq!(rec.val(0, 371), Some(b"35".as_ref()));
        assert_eq!(rec.num(0, 373), Some(1));
        assert_eq!(s.next_inbound_seq(), 3);
    }

    #[test]
    fn reject_inbound_gap_sends_resend_request() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        let mut rec = Rec::new();
        s.on_reject_inbound(5, false, Some(35), 1, now, &mut rec)
            .unwrap();
        assert_eq!(rec.len(), 1);
        // ResendRequest (35=2) with BeginSeqNo(7)=2.
        assert_eq!(rec.mt(0), b"2", "expected ResendRequest");
        assert_eq!(rec.num(0, 7), Some(2));
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
    fn consume_seq_2(s: &mut SessionState, now: Instant) {
        assert_eq!(
            s.on_app(2, false, now, &mut Rec::new()).unwrap(),
            Control::Application
        );
        assert_eq!(s.next_inbound_seq(), 3);
    }

    #[test]
    fn heartbeat_out_of_sequence_suppressed_and_resends() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now); // next_inbound = 2
        let mut rec = Rec::new();
        // seq 5 > 2: gap.
        let ctrl = s.on_heartbeat(5, false, None, now, &mut rec).unwrap();
        assert_eq!(ctrl, Control::None, "gap Heartbeat must be suppressed");
        assert_eq!(rec.len(), 1);
        assert_eq!(rec.mt(0), b"2", "gap must emit a ResendRequest");
        assert_eq!(rec.num(0, 7), Some(2));
        assert_eq!(s.state(), State::Resending);
    }

    #[test]
    fn heartbeat_duplicate_suppressed_no_resend() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        consume_seq_2(&mut s, now); // next_inbound = 3
        let mut rec = Rec::new();
        // seq 2 < 3 with PossDup: duplicate.
        let ctrl = s.on_heartbeat(2, true, None, now, &mut rec).unwrap();
        assert_eq!(
            ctrl,
            Control::None,
            "duplicate Heartbeat must be suppressed"
        );
        assert_eq!(rec.len(), 0, "duplicate must not emit a ResendRequest");
        assert_eq!(s.state(), State::Active, "duplicate must not disconnect");
    }

    #[test]
    fn heartbeat_in_sequence_surfaces() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        let mut rec = Rec::new();
        let ctrl = s.on_heartbeat(2, false, None, now, &mut rec).unwrap();
        assert_eq!(ctrl, Control::Heartbeat);
        assert_eq!(rec.len(), 0);
    }

    #[test]
    fn test_request_out_of_sequence_suppressed_no_echo() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        let mut rec = Rec::new();
        let ctrl = s
            .on_test_request(5, false, b"PROBE", now, &mut rec)
            .unwrap();
        assert_eq!(ctrl, Control::None, "gap TestRequest must be suppressed");
        // A gap emits a ResendRequest and NOT the Heartbeat echo (which is
        // Proceed-only work).
        assert_eq!(rec.len(), 1);
        assert_eq!(
            rec.mt(0),
            b"2",
            "gap must emit ResendRequest, not a Heartbeat echo"
        );
        assert_eq!(rec.num(0, 7), Some(2));
    }

    #[test]
    fn test_request_duplicate_suppressed_no_echo() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        consume_seq_2(&mut s, now); // next_inbound = 3
        let mut rec = Rec::new();
        let ctrl = s.on_test_request(2, true, b"PROBE", now, &mut rec).unwrap();
        assert_eq!(
            ctrl,
            Control::None,
            "duplicate TestRequest must be suppressed"
        );
        assert_eq!(
            rec.len(),
            0,
            "duplicate must not emit a Heartbeat echo or ResendRequest"
        );
        assert_eq!(s.state(), State::Active);
    }

    #[test]
    fn reject_out_of_sequence_suppressed_and_resends() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        let mut rec = Rec::new();
        let ctrl = s.on_reject(5, false, now, &mut rec).unwrap();
        assert_eq!(ctrl, Control::None, "gap Reject must be suppressed");
        assert_eq!(rec.len(), 1);
        assert_eq!(rec.mt(0), b"2", "gap must emit ResendRequest");
        assert_eq!(rec.num(0, 7), Some(2));
        assert_eq!(s.state(), State::Resending);
    }

    #[test]
    fn reject_duplicate_suppressed_no_resend() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        consume_seq_2(&mut s, now); // next_inbound = 3
        let mut rec = Rec::new();
        let ctrl = s.on_reject(2, true, now, &mut rec).unwrap();
        assert_eq!(ctrl, Control::None, "duplicate Reject must be suppressed");
        assert_eq!(rec.len(), 0);
        assert_eq!(s.state(), State::Active);
    }

    #[test]
    fn sequence_reset_gap_fill_out_of_sequence_suppressed_and_resends() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now); // next_inbound = 2
        let mut rec = Rec::new();
        // GapFill (gap_fill = true) at seq 5 > 2: out of sequence.
        let ctrl = s.on_sequence_reset(5, 9, true, now, &mut rec).unwrap();
        assert_eq!(
            ctrl,
            Control::None,
            "out-of-sequence GapFill must be suppressed"
        );
        assert_eq!(rec.len(), 1);
        assert_eq!(rec.mt(0), b"2", "gap must emit ResendRequest");
        assert_eq!(rec.num(0, 7), Some(2));
        // Proceed-only work (advance to new_seq) must NOT run on a gap.
        assert_eq!(
            s.next_inbound_seq(),
            2,
            "next_inbound must not advance to new_seq on a gap"
        );
    }

    #[test]
    fn sequence_reset_gap_fill_duplicate_suppressed_no_advance() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        consume_seq_2(&mut s, now); // next_inbound = 3
        let mut rec = Rec::new();
        // Note: on_sequence_reset validates GapFill with poss_dup = false
        // internally, so a below-expected GapFill is a too-low-without-PossDup
        // case → Disconnected, NOT a silent duplicate. Assert that path here so
        // the GapFill duplicate semantics are pinned. seq 2 < 3.
        let ctrl = s.on_sequence_reset(2, 9, true, now, &mut rec).unwrap();
        assert_eq!(
            ctrl,
            Control::Disconnected {
                reason: DisconnectReason::SeqNumTooLow
            },
            "a below-expected GapFill (validated with PossDup=false) disconnects"
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
        let now = Instant::now();
        establish(&mut s, now); // next_inbound = 2
        let mut rec = Rec::new();
        // In-sequence GapFill at seq 2 advancing to new_seq 7.
        let ctrl = s.on_sequence_reset(2, 7, true, now, &mut rec).unwrap();
        assert_eq!(ctrl, Control::SequenceReset);
        assert_eq!(s.next_inbound_seq(), 7, "in-sequence GapFill advances");
        assert_eq!(rec.len(), 0);
    }

    #[test]
    fn logout_out_of_sequence_suppressed_and_resends() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now); // Active, next_inbound = 2
        let mut rec = Rec::new();
        // seq 5 > 2: gap. A gap Logout must be suppressed (ResendRequest), NOT
        // treated as a logout exchange.
        let ctrl = s.on_logout(5, false, now, &mut rec).unwrap();
        assert_eq!(ctrl, Control::None, "gap Logout must be suppressed");
        assert_eq!(rec.len(), 1);
        assert_eq!(rec.mt(0), b"2", "gap must emit ResendRequest, not a Logout");
        assert_eq!(rec.num(0, 7), Some(2));
        assert_eq!(
            s.state(),
            State::Resending,
            "gap Logout must not disconnect the session"
        );
    }

    #[test]
    fn logout_duplicate_suppressed_no_disconnect() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        establish(&mut s, now);
        consume_seq_2(&mut s, now); // next_inbound = 3
        let mut rec = Rec::new();
        // seq 2 < 3 with PossDup: duplicate Logout — ignored, session survives.
        let ctrl = s.on_logout(2, true, now, &mut rec).unwrap();
        assert_eq!(ctrl, Control::None, "duplicate Logout must be suppressed");
        assert_eq!(rec.len(), 0);
        assert_eq!(
            s.state(),
            State::Active,
            "duplicate Logout must not disconnect the session"
        );
    }
}
