//! Per-venue customization of outbound session (admin) messages.
//!
//! Venues layer authentication onto the FIX Logon that the base protocol does
//! not describe: Coinbase wants an HMAC-SHA256 in `RawData(96)`, Binance an
//! Ed25519 signature, Deribit a nonce/digest pair. All three are computed
//! *over* the header the engine assigns — `SendingTime(52)`, `MsgSeqNum(34)`,
//! `SenderCompID(49)`, `TargetCompID(56)` — so they cannot be expressed as
//! static configuration or generated from a FIX XML dictionary. They are code.
//!
//! [`SessionCustomizer`] is the seam for that code. The engine stamps the
//! session header, runs the hook, and only then frames `BodyLength(9)` and
//! `CheckSum(10)` — so fields the hook appends are covered by the length and
//! the checksum with no work from the venue author.
//!
//! ```
//! use nexus_fix_codec::{AdminMsgOut, SessionCustomizer};
//!
//! struct StaticAuth {
//!     username: &'static [u8],
//!     password: &'static [u8],
//! }
//!
//! impl SessionCustomizer for StaticAuth {
//!     fn configure_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
//!         m.field(553, self.username);
//!         m.field(554, self.password);
//!     }
//! }
//! ```
//!
//! Every method defaults to a no-op, so a venue implements only the message
//! types it actually customizes. A customizer that implements `configure_logon`
//! alone cannot leak credentials into a Heartbeat.

use crate::dict::AdminHeader;
use crate::writer::FrameFormatter;

/// Tags the session layer owns. The engine stamps these; a customizer that
/// writes one would emit a duplicate and get the message rejected on the wire.
#[inline]
const fn is_engine_owned(tag: u32) -> bool {
    matches!(tag, 8 | 9 | 10 | 34 | 35 | 49 | 52 | 56)
}

/// An outbound admin message, header stamped, body open for appending.
///
/// Handed to [`SessionCustomizer`] after the engine has written
/// `BeginString(8)`, `MsgType(35)`, `MsgSeqNum(34)`, `SenderCompID(49)`,
/// `TargetCompID(56)`, and `SendingTime(52)`, and before `BodyLength(9)` and
/// `CheckSum(10)` are computed. The accessors read back the stamped values —
/// venue signatures are computed over exactly those — and [`field`](Self::field)
/// appends to the body.
pub struct AdminMsgOut<'f, 'h> {
    fmt: &'f mut FrameFormatter<'h>,
    hdr: &'f AdminHeader<'h>,
    msg_type: &'static [u8],
}

impl<'f, 'h> AdminMsgOut<'f, 'h> {
    /// Wrap an in-progress frame whose session header has already been stamped.
    ///
    /// Called by the engine between the dictionary's standard-field encode and
    /// [`FrameFormatter::finish`].
    #[inline]
    pub fn new(
        fmt: &'f mut FrameFormatter<'h>,
        hdr: &'f AdminHeader<'h>,
        msg_type: &'static [u8],
    ) -> Self {
        Self { fmt, hdr, msg_type }
    }

    /// `MsgSeqNum` (tag 34) as stamped by the session.
    #[inline]
    pub fn seq_num(&self) -> u32 {
        self.hdr.seq
    }

    /// `SendingTime` (tag 52) as stamped by the session.
    #[inline]
    pub fn sending_time(&self) -> &[u8] {
        self.hdr.ts
    }

    /// `SenderCompID` (tag 49) as stamped by the session.
    #[inline]
    pub fn sender(&self) -> &[u8] {
        self.hdr.sender
    }

    /// `TargetCompID` (tag 56) as stamped by the session.
    #[inline]
    pub fn target(&self) -> &[u8] {
        self.hdr.target
    }

    /// `MsgType` (tag 35) of the message being built.
    #[inline]
    pub fn msg_type(&self) -> &[u8] {
        self.msg_type
    }

    /// Append a `tag=value` body field.
    ///
    /// The field is written inside the frame, so `BodyLength(9)` and
    /// `CheckSum(10)` cover it automatically.
    ///
    /// # Panics
    ///
    /// Debug builds panic if `tag` is one the session layer owns (8, 9, 10, 34,
    /// 35, 49, 52, 56) — writing one duplicates a header field and the venue
    /// rejects the message. This is a programming error in the customizer, not a
    /// runtime condition, so it is a debug tripwire rather than a release-time
    /// check or a `Result` the caller would have nothing useful to do with.
    #[inline]
    pub fn field(&mut self, tag: u32, value: &[u8]) {
        debug_assert!(
            !is_engine_owned(tag),
            "tag {tag} is engine-owned; the session stamps it"
        );
        self.fmt.field(tag, value);
    }
}

/// Per-venue hook for customizing outbound session messages.
///
/// Each method fires after the engine stamps the session header and before the
/// frame's `BodyLength(9)`/`CheckSum(10)` are computed, so appended fields are
/// framed correctly and signatures can be taken over the stamped header. See
/// the [module docs](self) for the rationale and an example.
///
/// Methods are per message type and default to no-ops: a venue implements only
/// what it customizes, and cannot accidentally inject Logon credentials into
/// every Heartbeat.
pub trait SessionCustomizer {
    /// Customize a Logon (35=A). The venue-auth hook.
    fn configure_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a Logon (35=A) carrying `ResetSeqNumFlag(141)=Y`.
    fn configure_logon_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a Logout (35=5).
    fn configure_logout(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a Heartbeat (35=0).
    fn configure_heartbeat(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a TestRequest (35=1).
    fn configure_test_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a ResendRequest (35=2).
    fn configure_resend_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a SequenceReset (35=4).
    fn configure_sequence_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a Reject (35=3).
    fn configure_reject(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }
}

/// The null customizer: every hook is a no-op.
///
/// The default customizer type parameter for the engine's `FixSession` and
/// `FixConnection`, so plain-FIX callers never name it. A ZST with empty method
/// bodies — it monomorphizes to nothing.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoCustomizer;

impl SessionCustomizer for NoCustomizer {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn engine_owned_tags_are_exactly_the_session_header() {
        for tag in [8, 9, 10, 34, 35, 49, 52, 56] {
            assert!(is_engine_owned(tag), "tag {tag} must be engine-owned");
        }
        // A representative spread of body tags the venue may write.
        for tag in [1, 96, 108, 112, 141, 553, 554, 5000] {
            assert!(!is_engine_owned(tag), "tag {tag} must not be engine-owned");
        }
    }

    #[test]
    fn accessors_read_the_stamped_header() {
        let mut buf = [0u8; 256];
        let hdr = AdminHeader {
            seq: 42,
            sender: b"ME",
            target: b"YOU",
            ts: b"20260716-12:00:00.000",
        };
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
        let m = AdminMsgOut::new(&mut fmt, &hdr, b"A");

        assert_eq!(m.seq_num(), 42);
        assert_eq!(m.sender(), b"ME");
        assert_eq!(m.target(), b"YOU");
        assert_eq!(m.sending_time(), b"20260716-12:00:00.000");
        assert_eq!(m.msg_type(), b"A");
    }

    #[test]
    fn field_appends_into_the_frame() {
        let mut buf = [0u8; 256];
        let hdr = AdminHeader {
            seq: 1,
            sender: b"ME",
            target: b"YOU",
            ts: b"20260716-12:00:00.000",
        };
        let (start, len) = {
            let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
            let mut m = AdminMsgOut::new(&mut fmt, &hdr, b"A");
            m.field(553, b"user");
            fmt.finish().unwrap()
        };
        let msg = &buf[start..start + len];
        assert!(msg.windows(9).any(|w| w == b"553=user\x01"));
        assert!(crate::validate_checksum(msg).is_ok());
    }

    #[test]
    #[should_panic(expected = "engine-owned")]
    fn field_rejects_engine_owned_tag_in_debug() {
        let mut buf = [0u8; 256];
        let hdr = AdminHeader {
            seq: 1,
            sender: b"ME",
            target: b"YOU",
            ts: b"20260716-12:00:00.000",
        };
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
        let mut m = AdminMsgOut::new(&mut fmt, &hdr, b"A");
        m.field(34, b"99");
    }
}
