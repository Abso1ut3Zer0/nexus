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
}

/// Session event returned in [`Out::event`](super::Out::event).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// Logon exchange completed; the session is live.
    Established {
        /// Negotiated heartbeat interval in seconds.
        heart_bt_int_s: u32,
    },
    /// An in-sequence application message; decode it from the buffer
    /// passed to `handle_message`.
    App {
        /// Inbound MsgSeqNum of the message.
        seq_num: u32,
        /// `PossDupFlag(43)=Y` was set (replayed message).
        poss_dup: bool,
    },
    /// Counterparty requested retransmission of our messages. The session
    /// gap-fills the range automatically; store-backed replay lands with
    /// the persistence layer.
    ResendRange {
        /// First requested sequence number.
        begin: u32,
        /// Last requested sequence number, `0` for all subsequent.
        end: u32,
    },
    /// Counterparty reset the inbound sequence via SequenceReset.
    SequenceReset {
        /// Next inbound sequence number after the reset.
        new_seq: u32,
    },
    /// Counterparty rejected one of our messages at the session level.
    RejectReceived {
        /// RefSeqNum(45) of the rejected message, `0` if absent.
        ref_seq_num: u32,
    },
    /// The session left the connected states.
    Disconnected {
        /// Why the session ended.
        reason: DisconnectReason,
    },
}
