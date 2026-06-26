mod event;

use std::time::{Duration, Instant};

pub use event::{DisconnectReason, Event, State};

use crate::framework::SessionError;

const SEQ_MAX: u32 = i32::MAX as u32;

const TEST_REQ_ID_CAP: usize = 64;

/// An outbound admin message that the framework must sequence and encode.
///
/// `seq` is the pre-allocated `MsgSeqNum(34)`. For [`AdminMsg::SequenceReset`]
/// `seq` is the first gap-filled sequence number (encode with `PossDupFlag=Y`);
/// for all others it is the next consumed outbound sequence number.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdminMsg {
    Logon {
        seq: u32,
        heart_bt_int_s: u32,
    },
    Logout {
        seq: u32,
    },
    Heartbeat {
        seq: u32,
        echo: Option<([u8; TEST_REQ_ID_CAP], u8)>,
    },
    TestRequest {
        seq: u32,
        id: u64,
    },
    ResendRequest {
        seq: u32,
        begin: u32,
    },
    /// GapFill-mode SequenceReset. Encode with `GapFillFlag(123)=Y` and
    /// `PossDupFlag(43)=Y`. `seq` is the start of the gap-filled range;
    /// `new_seq` is `NewSeqNo(36)`.
    SequenceReset {
        seq: u32,
        new_seq: u32,
    },
}

/// Output of a [`SessionState`] handler call.
///
/// Carries at most two outbound admin messages and one session event.
/// Drain these immediately after each handler invocation — they are not
/// buffered anywhere inside the session.
#[derive(Clone, Copy, Debug)]
pub struct Out {
    admin: [Option<AdminMsg>; 2],
    event: Option<Event>,
    admin_len: u8,
}

impl Out {
    const EMPTY: Self = Self {
        admin: [None, None],
        event: None,
        admin_len: 0,
    };

    fn push_admin(&mut self, msg: AdminMsg) {
        debug_assert!((self.admin_len as usize) < 2, "Out admin overflow");
        if (self.admin_len as usize) < 2 {
            self.admin[self.admin_len as usize] = Some(msg);
            self.admin_len += 1;
        }
    }

    fn push_event(&mut self, ev: Event) {
        self.event = Some(ev);
    }

    /// Outbound admin messages to encode and send, in order.
    pub fn admin_messages(&self) -> impl Iterator<Item = AdminMsg> + '_ {
        self.admin[..self.admin_len as usize]
            .iter()
            .filter_map(|a| *a)
    }

    /// Session event to deliver to the application layer, if any.
    pub fn event(&self) -> Option<Event> {
        self.event
    }
}

/// Pure FIX session state machine.
///
/// Owns sequence numbers, timers, and state transitions. The framework above
/// owns the transport, clock, and wire encoding. Each typed handler receives
/// pre-decoded admin fields and returns an [`Out`] containing any outbound
/// admin messages and a session event. Never allocates.
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

    /// Allocates the next outbound sequence number for an application message
    /// and updates the outbound activity timestamp used by the heartbeat timer.
    ///
    /// Returns `Err(SeqNumExhausted)` when `next_outbound` has reached `i32::MAX`.
    /// The caller must initiate a sequence reset or logout before sending further messages.
    pub fn allocate_seq(&mut self, now: Instant) -> Result<u32, SessionError> {
        if self.next_outbound > SEQ_MAX {
            return Err(SessionError::SeqNumExhausted);
        }
        let s = self.next_outbound;
        self.next_outbound += 1;
        self.last_sent = Some(now);
        Ok(s)
    }

    fn bump_outbound(&mut self, now: Instant, out: &mut Out) -> Option<u32> {
        if self.next_outbound > SEQ_MAX {
            self.disconnect(DisconnectReason::SeqNumExhausted, out);
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
            State::LogonSent | State::LogoutPending => self.state_entered.map(|t| t + self.hb),
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
    pub fn connect(&mut self, now: Instant) -> Out {
        if self.state != State::Disconnected {
            return Out::EMPTY;
        }
        let mut out = Out::EMPTY;
        let Some(seq) = self.bump_outbound(now, &mut out) else {
            return out;
        };
        out.push_admin(AdminMsg::Logon {
            seq,
            heart_bt_int_s: self.hb.as_secs() as u32,
        });
        self.state = State::LogonSent;
        self.state_entered = Some(now);
        self.last_received = Some(now);
        out
    }

    /// Initiates a clean logout. No-op unless in an active state.
    pub fn logout(&mut self, now: Instant) -> Out {
        if !matches!(self.state, State::Active | State::Resending) {
            return Out::EMPTY;
        }
        let mut out = Out::EMPTY;
        let Some(seq) = self.bump_outbound(now, &mut out) else {
            return out;
        };
        out.push_admin(AdminMsg::Logout { seq });
        self.state = State::LogoutPending;
        self.state_entered = Some(now);
        out
    }

    /// Fires due timers: logon/logout timeouts, heartbeat emission, and
    /// TestRequest probing. Call at or after [`next_timeout`](Self::next_timeout).
    pub fn on_timeout(&mut self, now: Instant) -> Out {
        let mut out = Out::EMPTY;
        match self.state {
            State::Disconnected => {}
            State::LogonSent => {
                if let Some(t) = self.state_entered
                    && now.duration_since(t) >= self.hb
                {
                    self.disconnect(DisconnectReason::LogonTimeout, &mut out);
                }
            }
            State::LogoutPending => {
                if let Some(t) = self.state_entered
                    && now.duration_since(t) >= self.hb
                {
                    self.disconnect(DisconnectReason::LogoutTimeout, &mut out);
                }
            }
            State::Active | State::Resending => {
                if let Some(t) = self.test_request_sent {
                    if now.duration_since(t) >= self.hb {
                        let Some(seq) = self.bump_outbound(now, &mut out) else {
                            return out;
                        };
                        out.push_admin(AdminMsg::Logout { seq });
                        self.disconnect(DisconnectReason::TestRequestTimeout, &mut out);
                        return out;
                    }
                } else if let Some(t) = self.last_received
                    && now.duration_since(t) >= self.inbound_grace()
                {
                    self.test_req_counter += 1;
                    let Some(seq) = self.bump_outbound(now, &mut out) else {
                        return out;
                    };
                    out.push_admin(AdminMsg::TestRequest {
                        seq,
                        id: self.test_req_counter,
                    });
                    self.test_request_sent = Some(now);
                }
                if let Some(t) = self.last_sent
                    && now.duration_since(t) >= self.hb
                {
                    let Some(seq) = self.bump_outbound(now, &mut out) else {
                        return out;
                    };
                    out.push_admin(AdminMsg::Heartbeat { seq, echo: None });
                }
            }
        }
        out
    }

    /// Handles a received Logon.
    ///
    /// Set `send_reply = true` when acting as acceptor; the session includes a
    /// Logon in the output. Pass `false` for the initiator's incoming reply.
    pub fn on_logon(
        &mut self,
        seq: u32,
        heart_bt_int_s: u32,
        reset_seq_num: bool,
        send_reply: bool,
        now: Instant,
    ) -> Out {
        let valid = if send_reply {
            self.state == State::Disconnected
        } else {
            self.state == State::LogonSent
        };
        if !valid {
            return Out::EMPTY;
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        if reset_seq_num {
            self.next_inbound = 1;
            if send_reply {
                self.next_outbound = 1;
            }
        }
        self.hb = Duration::from_secs(u64::from(heart_bt_int_s));

        let mut out = Out::EMPTY;
        if send_reply {
            let Some(reply_seq) = self.bump_outbound(now, &mut out) else {
                return out;
            };
            out.push_admin(AdminMsg::Logon {
                seq: reply_seq,
                heart_bt_int_s,
            });
        }

        if seq < self.next_inbound {
            let Some(logout_seq) = self.bump_outbound(now, &mut out) else {
                return out;
            };
            out.push_admin(AdminMsg::Logout { seq: logout_seq });
            self.disconnect(DisconnectReason::SeqNumTooLow, &mut out);
            return out;
        }

        out.push_event(Event::Established { heart_bt_int_s });

        if seq > self.next_inbound {
            self.gap_high = seq;
            let Some(rr_seq) = self.bump_outbound(now, &mut out) else {
                return out;
            };
            out.push_admin(AdminMsg::ResendRequest {
                seq: rr_seq,
                begin: self.next_inbound,
            });
            self.state = State::Resending;
        } else {
            self.next_inbound += 1;
            self.state = State::Active;
        }
        out
    }

    /// Handles a received Logout.
    pub fn on_logout(&mut self, seq: u32, poss_dup: bool, now: Instant) -> Out {
        self.last_received = Some(now);
        self.test_request_sent = None;
        let mut out = Out::EMPTY;
        if self.state == State::LogonSent {
            self.disconnect(DisconnectReason::Logout, &mut out);
        } else if matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) && self.validate_seq(seq, poss_dup, now, &mut out)
        {
            if self.state != State::LogoutPending {
                let Some(logout_seq) = self.bump_outbound(now, &mut out) else {
                    return out;
                };
                out.push_admin(AdminMsg::Logout { seq: logout_seq });
            }
            self.disconnect(DisconnectReason::Logout, &mut out);
        }
        out
    }

    /// Handles a received Heartbeat.
    pub fn on_heartbeat(&mut self, seq: u32, poss_dup: bool, now: Instant) -> Out {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Out::EMPTY;
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        let mut out = Out::EMPTY;
        if self.validate_seq(seq, poss_dup, now, &mut out) {
            self.check_resend_done();
        }
        out
    }

    /// Handles a received TestRequest. Replies with a Heartbeat echoing the TestReqID.
    pub fn on_test_request(
        &mut self,
        seq: u32,
        poss_dup: bool,
        test_req_id: &[u8],
        now: Instant,
    ) -> Out {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Out::EMPTY;
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        let mut out = Out::EMPTY;
        if self.validate_seq(seq, poss_dup, now, &mut out) {
            let mut echo = [0u8; TEST_REQ_ID_CAP];
            let id_len = test_req_id.len().min(TEST_REQ_ID_CAP);
            echo[..id_len].copy_from_slice(&test_req_id[..id_len]);
            let Some(hb_seq) = self.bump_outbound(now, &mut out) else {
                return out;
            };
            out.push_admin(AdminMsg::Heartbeat {
                seq: hb_seq,
                echo: Some((echo, id_len as u8)),
            });
            self.check_resend_done();
        }
        out
    }

    /// Handles a received ResendRequest. Surfaces `Event::ResendRange` so the
    /// persistence layer can drive the replay walk via [`FixJournal::resend_range`].
    pub fn on_resend_request(
        &mut self,
        seq: u32,
        poss_dup: bool,
        begin: u32,
        end: u32,
        now: Instant,
    ) -> Out {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Out::EMPTY;
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        let mut out = Out::EMPTY;
        if self.validate_seq(seq, poss_dup, now, &mut out) {
            out.push_event(Event::ResendRange { begin, end });
            self.check_resend_done();
        }
        out
    }

    /// Handles a received SequenceReset or GapFill.
    ///
    /// `gap_fill = false` is Reset mode: ignores `MsgSeqNum`, sets
    /// `next_inbound` to `new_seq`. `gap_fill = true` is GapFill mode:
    /// validates sequence, advances `next_inbound` to `new_seq`.
    pub fn on_sequence_reset(
        &mut self,
        seq: u32,
        new_seq: u32,
        gap_fill: bool,
        now: Instant,
    ) -> Out {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Out::EMPTY;
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        let mut out = Out::EMPTY;
        if !gap_fill {
            if new_seq == 0 || new_seq < self.next_inbound {
                return out;
            }
            self.next_inbound = new_seq;
            out.push_event(Event::SequenceReset { new_seq });
            self.check_resend_done();
        } else if self.validate_seq(seq, false, now, &mut out) {
            if new_seq > self.next_inbound {
                self.next_inbound = new_seq;
            }
            out.push_event(Event::SequenceReset { new_seq });
            self.check_resend_done();
        }
        out
    }

    /// Handles a received Reject.
    pub fn on_reject(&mut self, seq: u32, poss_dup: bool, ref_seq_num: u32, now: Instant) -> Out {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Out::EMPTY;
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        let mut out = Out::EMPTY;
        if self.validate_seq(seq, poss_dup, now, &mut out) {
            out.push_event(Event::RejectReceived { ref_seq_num });
            self.check_resend_done();
        }
        out
    }

    /// Handles an in-sequence application message.
    pub fn on_app(&mut self, seq: u32, poss_dup: bool, now: Instant) -> Out {
        if !matches!(
            self.state,
            State::Active | State::Resending | State::LogoutPending
        ) {
            return Out::EMPTY;
        }
        self.last_received = Some(now);
        self.test_request_sent = None;
        let mut out = Out::EMPTY;
        if self.validate_seq(seq, poss_dup, now, &mut out) {
            out.push_event(Event::App {
                seq_num: seq,
                poss_dup,
            });
            self.check_resend_done();
        }
        out
    }

    /// Handles a CompID mismatch detected by the framework. Sends Logout and disconnects.
    pub fn on_comp_id_mismatch(&mut self, now: Instant) -> Out {
        if self.state == State::Disconnected {
            return Out::EMPTY;
        }
        let mut out = Out::EMPTY;
        let Some(seq) = self.bump_outbound(now, &mut out) else {
            return out;
        };
        out.push_admin(AdminMsg::Logout { seq });
        self.disconnect(DisconnectReason::CompIdMismatch, &mut out);
        out
    }

    fn validate_seq(&mut self, seq: u32, poss_dup: bool, now: Instant, out: &mut Out) -> bool {
        if seq > self.next_inbound {
            if self.gap_high < seq {
                self.gap_high = seq;
            }
            if self.state != State::Resending {
                let Some(rr_seq) = self.bump_outbound(now, out) else {
                    return false;
                };
                out.push_admin(AdminMsg::ResendRequest {
                    seq: rr_seq,
                    begin: self.next_inbound,
                });
                if self.state == State::Active {
                    self.state = State::Resending;
                }
            }
            return false;
        }
        if seq < self.next_inbound {
            if poss_dup {
                return false;
            }
            let Some(logout_seq) = self.bump_outbound(now, out) else {
                return false;
            };
            out.push_admin(AdminMsg::Logout { seq: logout_seq });
            self.disconnect(DisconnectReason::SeqNumTooLow, out);
            return false;
        }
        self.next_inbound += 1;
        true
    }

    fn disconnect(&mut self, reason: DisconnectReason, out: &mut Out) {
        self.state = State::Disconnected;
        self.test_request_sent = None;
        self.state_entered = None;
        out.push_event(Event::Disconnected { reason });
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
    use super::*;

    #[test]
    fn allocate_seq_errors_at_i32_max() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        s.connect(now);
        s.on_logon(1, 30, false, false, now);
        s.next_outbound = SEQ_MAX + 1;
        assert_eq!(s.allocate_seq(now), Err(SessionError::SeqNumExhausted));
    }

    #[test]
    fn bump_outbound_disconnects_at_i32_max() {
        let mut s = SessionState::new(Duration::from_secs(30));
        let now = Instant::now();
        s.connect(now);
        s.on_logon(1, 30, false, false, now);
        s.next_outbound = SEQ_MAX + 1;
        let out = s.logout(now);
        assert_eq!(
            out.event(),
            Some(Event::Disconnected {
                reason: DisconnectReason::SeqNumExhausted
            })
        );
    }
}
