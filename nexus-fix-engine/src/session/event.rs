/// Session lifecycle state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum State {
    /// No active FIX session.
    Disconnected,
    /// Logon sent, awaiting the counterparty's Logon reply.
    LogonSent,
    /// Session established, sequence numbers in sync.
    Active,
    /// Inbound gap detected, ResendRequest sent, awaiting replay.
    Resending,
    /// Logout sent, awaiting the counterparty's Logout confirm.
    LogoutPending,
    /// In-session reset initiated: TestRequest sent, awaiting Heartbeat to confirm drain.
    AwaitingResetDrain,
    /// Drain confirmed: Logon(141=Y) sent, awaiting counterparty's Logon(141=Y) ack.
    AwaitingResetAck,
}

/// Why the session was dropped **abnormally**.
///
/// A clean, negotiated logout is not here — it surfaces as
/// [`Message::LoggedOut`](crate::Message::LoggedOut) on the `Ok` side. Every
/// reason in this enum is a fault, carried by
/// [`TransportError::UnexpectedDisconnect`](crate::TransportError).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisconnectReason {
    /// No Logon reply within the logon timeout. No longer produced by the engine
    /// (it holds no timers); pass it to `logout()` when your own timer fires (phase 3).
    LogonTimeout,
    /// No Logout confirm within the logout timeout. No longer produced by the engine
    /// (it holds no timers); pass it to `logout()` when your own timer fires (phase 3).
    LogoutTimeout,
    /// Counterparty did not answer a TestRequest in time. No longer produced by the
    /// engine (it holds no timers); pass it to `logout()` when your own timer fires (phase 3).
    TestRequestTimeout,
    /// Inbound CompIDs do not match the session configuration.
    CompIdMismatch,
    /// Inbound MsgSeqNum lower than expected without PossDupFlag.
    SeqNumTooLow,
    /// Counterparty violated the session protocol.
    ProtocolViolation,
    /// Outbound sequence number reached i32::MAX; caller must force a sequence reset.
    SeqNumExhausted,
    /// Counterparty did not complete the reset handshake within the timeout. No longer
    /// produced by the engine (it holds no timers); pass it to `logout()` when your own
    /// timer fires (phase 3).
    ResetTimeout,
    /// The peer closed the transport (socket EOF) without a FIX Logout. Distinct
    /// from a connection reset, which surfaces as
    /// [`TransportError::Io`](crate::TransportError).
    PeerClosed,
}

/// The owned verdict a [`SessionState`](super::SessionState) handler returns.
///
/// The driver stores it across the `poll`/`message` borrow and reconstructs the
/// borrowed [`Message`](crate::Message) from it. It is `D`-free and owns no
/// borrow of the frame, so it can outlive the handler call that produced it —
/// unlike `Message`, which borrows the frame buffer.
///
/// Each inbound handler returns the kind of message it processed (or
/// [`Control::None`] when there is nothing to surface, e.g. an outbound-initiated
/// action or a suppressed gap/dup). The two exhaustion/precondition cases
/// ([`Control::Disconnected`] and the transient [`Control::Proceed`]) are covered
/// below.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Control {
    /// Nothing to surface to the application: an outbound-initiated action, or
    /// an inbound gap/duplicate the handler already answered (a ResendRequest was
    /// emitted, or a `PossDup`-too-low frame was ignored). Doubles as the initial
    /// `pending` value in the driver.
    None,
    /// Transient: [`validate_seq`](super::SessionState) matched the sequence and
    /// advanced it, so the caller should keep processing and return its own kind.
    /// Never a final verdict — a handler consumes it and returns its own
    /// `Control`; it is `unreachable!` in the driver's `message()`/`dispose()`.
    Proceed,
    /// A Logon (35=A) acknowledging our own outbound Logon (initiator role). The
    /// session is live; nothing to answer. Surfaces as
    /// [`Message::LogonAcknowledged`](crate::Message::LogonAcknowledged).
    ///
    /// `acknowledged` is retained for the internal reply-completion return of
    /// [`accept_logon`](super::SessionState::accept_logon); only the `true`
    /// (initiator-ack) case is ever surfaced through [`Control`].
    Logon {
        /// Whether this Logon acknowledged our own (vs. a reply we just sent).
        acknowledged: bool,
    },
    /// A counterparty-initiated Logon (35=A, acceptor role) that the user must
    /// answer. Surfaces as [`Message::LogonRequest`](crate::Message::LogonRequest)
    /// carrying a `LogonDecision`; the reply is user-driven
    /// (`decision.accept`/`decision.reject`), not engine-emitted. `seq` is the
    /// peer's `MsgSeqNum(34)`, `heart_bt_int_s` its `HeartBtInt(108)`.
    LogonRequest {
        /// The peer Logon's `MsgSeqNum(34)`.
        seq: u32,
        /// The peer Logon's `HeartBtInt(108)`, in seconds.
        heart_bt_int_s: u32,
    },
    /// A counterparty-initiated reset Logon (35=A, `ResetSeqNumFlag(141)=Y`) that
    /// the user must answer — either the acceptor's opening reset Logon or a
    /// peer-initiated in-session reset while active. Surfaces as
    /// [`Message::LogonResetRequest`](crate::Message::LogonResetRequest); the reply
    /// (a `LogonReset`) is user-driven via the `LogonDecision`.
    LogonResetRequest {
        /// The peer Logon's `MsgSeqNum(34)`.
        seq: u32,
        /// The peer Logon's `HeartBtInt(108)`, in seconds.
        heart_bt_int_s: u32,
    },
    /// An inbound gap was detected: a message arrived above the expected
    /// `MsgSeqNum`. Surfaces as [`Message::GapDetected`](crate::Message::GapDetected)
    /// with `begin` = the first missing inbound seqnum; the user answers with
    /// `resend_request(begin)`. The engine has already entered `Resending` so a
    /// further gap in the same recovery window is suppressed
    /// ([`Control::None`]), not re-surfaced.
    GapDetected {
        /// First missing inbound seqnum — the `BeginSeqNo(7)` for the reply.
        begin: u32,
    },
    /// A peer-initiated Logout (35=5) the user must answer. Surfaces as
    /// [`Message::LogoutRequest`](crate::Message::LogoutRequest); the user replies
    /// with `logout(..)`. This is an in-sequence Logout while `Active`/`Resending`
    /// (the reply is user-driven, not engine-emitted) or an out-of-state Logout
    /// (e.g. mid-reset). An in-sequence Logout while `LogoutPending` confirms our
    /// own initiated logout and surfaces as [`Control::LoggedOut`] instead.
    Logout,
    /// A Heartbeat (35=0) was processed.
    Heartbeat,
    /// A TestRequest (35=1) was processed. Surfaces as
    /// [`Message::TestRequest`](crate::Message::TestRequest) carrying the
    /// `TestReqID(112)`; the user answers with `heartbeat(Some(id))`. The engine no
    /// longer auto-emits the Heartbeat echo.
    TestRequest,
    /// A ResendRequest (35=2) was validated and is in-sequence — the state
    /// machine's signal that the driver should act on it. Carries no fields: the
    /// driver parses `BeginSeqNo`/`EndSeqNo` locally and *refines* this into a
    /// [`ResendCursor`](Self::ResendCursor) (providable) or a
    /// [`ResendOutOfRange`](Self::ResendOutOfRange) (not), so this variant is never
    /// stored as the driver's `pending` and never reaches `message()`.
    ResendRequest,
    /// A providable ResendRequest: the requested range lies fully within the
    /// journal's retained replay window. The driver's refinement of
    /// [`ResendRequest`](Self::ResendRequest); surfaces as
    /// [`Message::ResendRequest`](crate::Message::ResendRequest) carrying a
    /// `ResendCursor` the user pumps. `begin` is the requested `BeginSeqNo(7)`;
    /// `end` is the resolved `EndSeqNo(16)` (an open-ended `0` is clamped to the
    /// journal high-water).
    ResendCursor {
        /// Requested first outbound seqnum to replay (`BeginSeqNo(7)`).
        begin: u32,
        /// Resolved last outbound seqnum to replay (`EndSeqNo(16)`, `0` clamped to
        /// high-water).
        end: u32,
    },
    /// A ResendRequest the journal can no longer fulfill: `begin` has rotated off
    /// the retained window (`begin < low_water`) and/or the resolved `end` exceeds
    /// what was ever sent (`end > high_water`). Surfaces as
    /// [`Message::ResendOutOfRange`](crate::Message::ResendOutOfRange) with no
    /// cursor — the user decides (a `sequence_reset`, or logout).
    ResendOutOfRange {
        /// Requested first outbound seqnum (`BeginSeqNo(7)`).
        begin: u32,
        /// Resolved last outbound seqnum (`EndSeqNo(16)`, `0` clamped to high-water).
        end: u32,
        /// Oldest outbound seqnum still replayable from the retained window.
        low_water: u32,
        /// Highest outbound seqnum ever sent (last stored).
        high_water: u32,
    },
    /// A SequenceReset (35=4) was processed.
    SequenceReset,
    /// A Reject (35=3) was processed.
    Reject,
    /// An in-sequence application message was processed.
    Application,
    /// A clean, negotiated logout completed and the session ended. Surfaces as
    /// [`Message::LoggedOut`](crate::Message::LoggedOut) — the graceful terminal
    /// event on the `Ok` side, distinct from an abnormal [`Disconnected`](Self::Disconnected).
    LoggedOut,
    /// The session was dropped abnormally. Surfaces as
    /// [`TransportError::UnexpectedDisconnect`](crate::TransportError), never a `Message`.
    Disconnected {
        /// Why the session ended.
        reason: DisconnectReason,
    },
}
