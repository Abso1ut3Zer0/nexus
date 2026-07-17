//! Typed outbound admin (session-level) messages.
//!
//! Each session-level message the engine emits — Logon, Heartbeat, ResendRequest,
//! … — is a distinct struct implementing [`AdminEncode`]. The trait is a pure
//! *naming bridge*: it ties a message to the [`FixDictionary`] encoder that writes
//! its body, the [`SessionCustomizer`] hook that may append to it, its owned-tag
//! list, and its `MsgType(35)`. The field-writes and the owned-lists themselves
//! stay on the dictionary (adjacent to the encoder, guarded by the drift test);
//! `AdminEncode` only defers to them.
//!
//! The engine's emit seam is generic over [`AdminEncode`], so the concrete admin
//! type is never erased into a sum and matched back apart. A handler that says
//! `sink.emit(ResendRequest { .. })` keeps a `ResendRequest` through encode,
//! customize, and journal — cross-message mis-wiring is unrepresentable.

use crate::customizer::{AdminMsgOut, SessionCustomizer};
use crate::dict::{AdminHeader, FixDictionary};
use crate::writer::FrameFormatter;

/// Capacity of the `TestReqID(112)` echo a [`Heartbeat`] carries when replying to
/// a TestRequest. Crate-private: callers construct the echo through
/// [`TestReqId::new`], which caps the input, so nothing outside the crate needs
/// to know the size.
const TEST_REQ_ID_CAP: usize = 64;

/// A `TestReqID(112)` echo, at most `TEST_REQ_ID_CAP` bytes.
///
/// The fields are private and the only constructor caps the input, so the stored
/// length can never exceed the buffer — an over-length echo is unrepresentable,
/// and [`as_bytes`](Self::as_bytes) never panics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TestReqId {
    buf: [u8; TEST_REQ_ID_CAP],
    len: u8,
}

impl TestReqId {
    /// Copy up to `TEST_REQ_ID_CAP` bytes of `id`; anything beyond is dropped.
    pub fn new(id: &[u8]) -> Self {
        let len = id.len().min(TEST_REQ_ID_CAP);
        let mut buf = [0u8; TEST_REQ_ID_CAP];
        buf[..len].copy_from_slice(&id[..len]);
        Self {
            buf,
            len: len as u8,
        }
    }

    /// The echoed bytes (`len <= TEST_REQ_ID_CAP` by construction, never panics).
    pub fn as_bytes(&self) -> &[u8] {
        &self.buf[..self.len as usize]
    }
}

/// Ties an outbound admin message to its wiring: the dictionary encoder that
/// writes its standard body, the per-venue customizer hook, its owned-tag list,
/// and its `MsgType(35)`.
///
/// Implemented by each admin struct in this module. Every method is a one-liner
/// forwarding to the right `FixDictionary::encode_*` / `SessionCustomizer::customize_*`
/// / `FixDictionary::*_OWNED`, so adding a field to an encoder never needs a
/// change here.
pub trait AdminEncode {
    /// The `MsgType(35)` byte string for this message (e.g. `b"A"` for Logon).
    const MSG_TYPE: &'static [u8];

    /// The pre-allocated `MsgSeqNum(34)` this message carries.
    fn seq(&self) -> u32;

    /// The body tags this message's encoder writes, for the given dictionary
    /// (the `FixDictionary::*_OWNED` const). The customizer tripwire treats these
    /// as engine-owned.
    fn owned<D: FixDictionary>() -> &'static [u32];

    /// Write this message's standard body fields into an already-started frame
    /// (session header stamped), deferring to `D::encode_*`.
    fn encode<D: FixDictionary>(&self, fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>);

    /// Run this message's per-venue customizer hook, deferring to
    /// `SessionCustomizer::customize_*`.
    fn customize<C: SessionCustomizer>(&self, customizer: &mut C, out: &mut AdminMsgOut<'_, '_>);
}

/// Logon (35=A).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Logon {
    pub seq: u32,
    pub heart_bt_int_s: u32,
}

impl AdminEncode for Logon {
    const MSG_TYPE: &'static [u8] = b"A";
    fn seq(&self) -> u32 {
        self.seq
    }
    fn owned<D: FixDictionary>() -> &'static [u32] {
        D::LOGON_OWNED
    }
    fn encode<D: FixDictionary>(&self, fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>) {
        D::encode_logon(fmt, hdr, self.heart_bt_int_s);
    }
    fn customize<C: SessionCustomizer>(&self, customizer: &mut C, out: &mut AdminMsgOut<'_, '_>) {
        customizer.customize_logon(out);
    }
}

/// Logon with `ResetSeqNumFlag(141)=Y` — both sides reset to seqnum 1 (35=A).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LogonReset {
    pub seq: u32,
    pub heart_bt_int_s: u32,
}

impl AdminEncode for LogonReset {
    const MSG_TYPE: &'static [u8] = b"A";
    fn seq(&self) -> u32 {
        self.seq
    }
    fn owned<D: FixDictionary>() -> &'static [u32] {
        D::LOGON_RESET_OWNED
    }
    fn encode<D: FixDictionary>(&self, fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>) {
        D::encode_logon_reset(fmt, hdr, self.heart_bt_int_s);
    }
    fn customize<C: SessionCustomizer>(&self, customizer: &mut C, out: &mut AdminMsgOut<'_, '_>) {
        customizer.customize_logon_reset(out);
    }
}

/// Logout (35=5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Logout {
    pub seq: u32,
}

impl AdminEncode for Logout {
    const MSG_TYPE: &'static [u8] = b"5";
    fn seq(&self) -> u32 {
        self.seq
    }
    fn owned<D: FixDictionary>() -> &'static [u32] {
        D::LOGOUT_OWNED
    }
    fn encode<D: FixDictionary>(&self, fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>) {
        D::encode_logout(fmt, hdr);
    }
    fn customize<C: SessionCustomizer>(&self, customizer: &mut C, out: &mut AdminMsgOut<'_, '_>) {
        customizer.customize_logout(out);
    }
}

/// Heartbeat (35=0), optionally echoing a `TestReqID(112)`.
///
/// `echo` is a [`TestReqId`] — build it with [`TestReqId::new`], which caps the
/// input at `TEST_REQ_ID_CAP` bytes so the echo can never over-run its buffer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Heartbeat {
    pub seq: u32,
    pub echo: Option<TestReqId>,
}

impl AdminEncode for Heartbeat {
    const MSG_TYPE: &'static [u8] = b"0";
    fn seq(&self) -> u32 {
        self.seq
    }
    fn owned<D: FixDictionary>() -> &'static [u32] {
        D::HEARTBEAT_OWNED
    }
    fn encode<D: FixDictionary>(&self, fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>) {
        let echo_bytes = self.echo.as_ref().map(TestReqId::as_bytes);
        D::encode_heartbeat(fmt, hdr, echo_bytes);
    }
    fn customize<C: SessionCustomizer>(&self, customizer: &mut C, out: &mut AdminMsgOut<'_, '_>) {
        customizer.customize_heartbeat(out);
    }
}

/// TestRequest (35=1) carrying `TestReqID(112)` derived from `id`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TestRequest {
    pub seq: u32,
    pub id: u64,
}

impl AdminEncode for TestRequest {
    const MSG_TYPE: &'static [u8] = b"1";
    fn seq(&self) -> u32 {
        self.seq
    }
    fn owned<D: FixDictionary>() -> &'static [u32] {
        D::TEST_REQUEST_OWNED
    }
    fn encode<D: FixDictionary>(&self, fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>) {
        D::encode_test_request(fmt, hdr, self.id);
    }
    fn customize<C: SessionCustomizer>(&self, customizer: &mut C, out: &mut AdminMsgOut<'_, '_>) {
        customizer.customize_test_request(out);
    }
}

/// ResendRequest (35=2) covering `[begin, ∞)` (encoded as `EndSeqNo(16)=0`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResendRequest {
    pub seq: u32,
    pub begin: u32,
}

impl AdminEncode for ResendRequest {
    const MSG_TYPE: &'static [u8] = b"2";
    fn seq(&self) -> u32 {
        self.seq
    }
    fn owned<D: FixDictionary>() -> &'static [u32] {
        D::RESEND_REQUEST_OWNED
    }
    fn encode<D: FixDictionary>(&self, fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>) {
        D::encode_resend_request(fmt, hdr, self.begin);
    }
    fn customize<C: SessionCustomizer>(&self, customizer: &mut C, out: &mut AdminMsgOut<'_, '_>) {
        customizer.customize_resend_request(out);
    }
}

/// GapFill-mode SequenceReset (35=4). Encoded with `GapFillFlag(123)=Y` and
/// `PossDupFlag(43)=Y`; `new_seq` is `NewSeqNo(36)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SequenceReset {
    pub seq: u32,
    pub new_seq: u32,
}

impl AdminEncode for SequenceReset {
    const MSG_TYPE: &'static [u8] = b"4";
    fn seq(&self) -> u32 {
        self.seq
    }
    fn owned<D: FixDictionary>() -> &'static [u32] {
        D::SEQUENCE_RESET_OWNED
    }
    fn encode<D: FixDictionary>(&self, fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>) {
        D::encode_sequence_reset(fmt, hdr, self.new_seq);
    }
    fn customize<C: SessionCustomizer>(&self, customizer: &mut C, out: &mut AdminMsgOut<'_, '_>) {
        customizer.customize_sequence_reset(out);
    }
}

/// Session-level Reject (35=3), sent for a malformed or semantically invalid
/// inbound message. Keeps the session alive.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reject {
    pub seq: u32,
    pub ref_seq_num: u32,
    pub ref_tag_id: Option<u32>,
    pub session_reject_reason: u8,
}

impl AdminEncode for Reject {
    const MSG_TYPE: &'static [u8] = b"3";
    fn seq(&self) -> u32 {
        self.seq
    }
    fn owned<D: FixDictionary>() -> &'static [u32] {
        D::REJECT_OWNED
    }
    fn encode<D: FixDictionary>(&self, fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>) {
        D::encode_reject(
            fmt,
            hdr,
            self.ref_seq_num,
            self.ref_tag_id,
            self.session_reject_reason,
        );
    }
    fn customize<C: SessionCustomizer>(&self, customizer: &mut C, out: &mut AdminMsgOut<'_, '_>) {
        customizer.customize_reject(out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_req_id_new_caps_over_length_input() {
        // The case that used to panic: an over-length id. `new` caps it at the
        // buffer size instead of storing a `len` that later slices out of bounds.
        let id = TestReqId::new(&[b'x'; 100]);
        assert_eq!(
            id.as_bytes().len(),
            TEST_REQ_ID_CAP,
            "an over-length echo must be capped to the buffer, not stored verbatim"
        );
        assert!(id.as_bytes().iter().all(|&b| b == b'x'));
    }

    #[test]
    fn test_req_id_new_preserves_short_input() {
        let id = TestReqId::new(b"TR-1");
        assert_eq!(id.as_bytes(), b"TR-1");
    }

    #[test]
    fn test_req_id_new_empty_is_empty() {
        assert_eq!(TestReqId::new(b"").as_bytes(), b"");
    }
}
