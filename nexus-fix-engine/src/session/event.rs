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

/// Why the session disconnected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisconnectReason {
    /// Clean logout exchange completed.
    Logout,
    /// No Logon reply within the logon timeout.
    LogonTimeout,
    /// No Logout confirm within the logout timeout.
    LogoutTimeout,
    /// Counterparty did not answer a TestRequest in time.
    TestRequestTimeout,
    /// Inbound CompIDs do not match the session configuration.
    CompIdMismatch,
    /// Inbound MsgSeqNum lower than expected without PossDupFlag.
    SeqNumTooLow,
    /// Counterparty violated the session protocol.
    ProtocolViolation,
    /// Outbound sequence number reached i32::MAX; caller must force a sequence reset.
    SeqNumExhausted,
    /// Counterparty did not complete the reset handshake within the timeout.
    ResetTimeout,
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
    /// A Logon (35=A) was processed. `acknowledged` is `true` when it acked our
    /// outbound Logon (initiator role), `false` when it initiates one we must
    /// answer (acceptor role).
    Logon {
        /// Whether this Logon acknowledged our own (vs. requesting one).
        acknowledged: bool,
    },
    /// A Logout (35=5) was processed. `acknowledged` is `true` when it confirmed
    /// our pending Logout, `false` when the counterparty initiated it.
    Logout {
        /// Whether this Logout acknowledged our own (vs. initiating one).
        acknowledged: bool,
    },
    /// A Heartbeat (35=0) was processed.
    Heartbeat,
    /// A TestRequest (35=1) was processed.
    TestRequest,
    /// A ResendRequest (35=2) was processed. The driver drives the replay walk
    /// from its locally parsed `begin`/`end`, so this carries no fields.
    ResendRequest,
    /// A SequenceReset (35=4) was processed.
    SequenceReset,
    /// A Reject (35=3) was processed.
    Reject,
    /// An in-sequence application message was processed.
    Application,
    /// The session left the connected states.
    Disconnected {
        /// Why the session ended.
        reason: DisconnectReason,
    },
}
