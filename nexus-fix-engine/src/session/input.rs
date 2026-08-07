//! Decoded inputs to the [`SessionState`](super::SessionState) inbound
//! handlers — the D-free counterpart of the codec's outbound `AdminEncode`
//! message structs.
//!
//! Each handler takes exactly one of these, so the call site names every value
//! (`SequenceResetIn { seq, new_seq, .. }`) instead of a positional
//! `(u32, bool, u32, bool)` that is trivial to transpose. Within each struct,
//! fields are ordered by descending alignment (like types adjacent) so the
//! layout stays hole-free if these are ever `#[repr(C)]`.

/// Input to [`SessionState::on_logon`](super::SessionState::on_logon).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LogonIn {
    /// `MsgSeqNum(34)` of the received Logon.
    pub seq: u32,
    /// `HeartBtInt(108)` — negotiated heartbeat interval, in seconds.
    pub heart_bt_int_s: u32,
    /// `ResetSeqNumFlag(141)=Y` — peer asks both sides to reset to seqnum 1.
    pub is_reset_seq_num: bool,
}

/// Input to [`SessionState::on_logout`](super::SessionState::on_logout).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LogoutIn {
    /// `MsgSeqNum(34)` of the received Logout.
    pub seq: u32,
    /// `PossDupFlag(43)=Y` — a below-expected seqnum is discarded, not rejected.
    pub is_poss_dup: bool,
}

/// Input to [`SessionState::on_heartbeat`](super::SessionState::on_heartbeat).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct HeartbeatIn {
    /// `TestReqID(112)` this heartbeat echoes, if it is a reply to our test
    /// request; `None` for an unsolicited heartbeat.
    pub echo_id: Option<u64>,
    /// `MsgSeqNum(34)` of the received Heartbeat.
    pub seq: u32,
    /// `PossDupFlag(43)=Y` — a below-expected seqnum is discarded, not rejected.
    pub is_poss_dup: bool,
}

/// Input to [`SessionState::on_test_request`](super::SessionState::on_test_request).
///
/// The `TestReqID(112)` is *not* carried here: the session no longer echoes it
/// (the user answers a surfaced [`Message::TestRequest`](crate::Message::TestRequest)
/// with `heartbeat(Some(id))`), so the handler only needs the sequence fields to
/// validate ordering.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct TestRequestIn {
    /// `MsgSeqNum(34)` of the received TestRequest.
    pub seq: u32,
    /// `PossDupFlag(43)=Y` — a below-expected seqnum is discarded, not rejected.
    pub is_poss_dup: bool,
}

/// Input to [`SessionState::on_resend_request`](super::SessionState::on_resend_request).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ResendRequestIn {
    /// `MsgSeqNum(34)` of the received ResendRequest.
    pub seq: u32,
    /// `PossDupFlag(43)=Y` — a below-expected seqnum is discarded, not rejected.
    pub is_poss_dup: bool,
}

/// Input to [`SessionState::on_sequence_reset`](super::SessionState::on_sequence_reset).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SequenceResetIn {
    /// `MsgSeqNum(34)` of the received SequenceReset.
    pub seq: u32,
    /// `NewSeqNo(36)` — the sequence number the peer is advancing to.
    pub new_seq: u32,
    /// `PossDupFlag(43)=Y` — a below-expected seqnum is discarded, not rejected.
    pub is_poss_dup: bool,
    /// `GapFillFlag(123)=Y` — gap-fill mode (validated against the expected
    /// seqnum); absent/`N` is a hard reset that is honored unconditionally.
    pub is_gap_fill: bool,
}

/// Input to [`SessionState::on_reject`](super::SessionState::on_reject).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct RejectIn {
    /// `MsgSeqNum(34)` of the received Reject.
    pub seq: u32,
    /// `PossDupFlag(43)=Y` — a below-expected seqnum is discarded, not rejected.
    pub is_poss_dup: bool,
}

/// Input to [`SessionState::on_app`](super::SessionState::on_app) — any
/// application (non-admin) message.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AppIn {
    /// `MsgSeqNum(34)` of the received message.
    pub seq: u32,
    /// `PossDupFlag(43)=Y` — a below-expected seqnum is discarded, not rejected.
    pub is_poss_dup: bool,
}

/// Input to [`SessionState::on_reject_inbound`](super::SessionState::on_reject_inbound)
/// — the engine is rejecting a received message (e.g. a session-level violation).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct RejectInboundIn {
    /// `MsgSeqNum(34)` of the message being rejected.
    pub seq: u32,
    /// `RefTagID(371)` — the tag that triggered the reject, if known.
    pub ref_tag_id: Option<u32>,
    /// `SessionRejectReason(373)` to cite in the outbound Reject.
    pub session_reject_reason: u8,
    /// `PossDupFlag(43)=Y` on the rejected message.
    pub is_poss_dup: bool,
}
