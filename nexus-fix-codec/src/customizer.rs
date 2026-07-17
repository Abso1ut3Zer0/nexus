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
//!     fn customize_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
//!         m.field(553, self.username);
//!         m.field(554, self.password);
//!     }
//! }
//! ```
//!
//! Every method defaults to a no-op, so a venue implements only the message
//! types it actually customizes. A customizer that implements `customize_logon`
//! alone cannot leak credentials into a Heartbeat.

use crate::dict::AdminHeader;
use crate::writer::FrameFormatter;

/// The session framing and header the engine stamps on *every* admin message:
/// `BeginString(8)`, `BodyLength(9)`, `CheckSum(10)`, `MsgSeqNum(34)`,
/// `MsgType(35)`, `SenderCompID(49)`, `SendingTime(52)`, `TargetCompID(56)`. A
/// customizer that writes one of these duplicates a field the session owns, so
/// the [`AdminMsgOut::field`] tripwire rejects it regardless of message type.
///
/// This set is protocol-fixed and never changes; per-message body tags come
/// from the dictionary (`FixDictionary::*_OWNED`) instead.
#[inline]
const fn is_framing_tag(tag: u32) -> bool {
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
///
/// `msg_type` and `owned` are plain data the engine passes in: `msg_type` is the
/// same `MsgType(35)` byte string written into the frame (so [`msg_type`] and
/// the wire agree by construction), and `owned` is the body tags this message's
/// own encoder wrote (`FixDictionary::*_OWNED`), which the [`field`] tripwire
/// rejects as duplicates.
///
/// [`msg_type`]: Self::msg_type
/// [`field`]: Self::field
pub struct AdminMsgOut<'f, 'h> {
    fmt: &'f mut FrameFormatter<'h>,
    hdr: &'f AdminHeader<'h>,
    msg_type: &'static [u8],
    owned: &'static [u32],
}

impl<'f, 'h> AdminMsgOut<'f, 'h> {
    /// Wrap an in-progress frame whose session header has already been stamped.
    ///
    /// Called by the engine between the dictionary's standard-field encode and
    /// [`FrameFormatter::finish`]. `msg_type` must be the exact `MsgType(35)`
    /// byte string the frame was started with — it is what
    /// [`msg_type`](Self::msg_type) reports, so a venue signs over the wire's own
    /// value. `owned` is this message's `FixDictionary::*_OWNED` body-tag list,
    /// which the [`field`](Self::field) tripwire treats as engine-owned.
    #[inline]
    pub fn new(
        fmt: &'f mut FrameFormatter<'h>,
        hdr: &'f AdminHeader<'h>,
        msg_type: &'static [u8],
        owned: &'static [u32],
    ) -> Self {
        Self {
            fmt,
            hdr,
            msg_type,
            owned,
        }
    }

    // The accessors below read the `AdminHeader` the engine stamped *from*, not
    // the bytes in the frame. They agree because `write_admin_header` writes
    // these very values verbatim. An encoder that reformatted a value on the way
    // in (padding, normalizing) would break that coupling and make these lie to
    // a venue signing over them — such an encoder must reformat here too.

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

    /// `MsgType` (tag 35) of the message being built — the same byte string
    /// written into the frame, since the engine passes one value to both
    /// [`FrameFormatter::new`] and [`new`](Self::new).
    #[inline]
    pub fn msg_type(&self) -> &'static [u8] {
        self.msg_type
    }

    /// Append a `tag=value` body field.
    ///
    /// The field is written inside the frame, so `BodyLength(9)` and
    /// `CheckSum(10)` cover it automatically.
    ///
    /// # Panics
    ///
    /// Debug builds panic if `tag` is one the engine already wrote for this
    /// message — writing it again duplicates the field and the venue rejects the
    /// message. That is the framing and session header stamped on every admin
    /// message (8, 9, 10, 34, 35, 49, 52, 56) plus the body tags this message's
    /// own encoder writes (the `owned` list, for example `108` on a Logon, `141`
    /// on a Logon carrying `ResetSeqNumFlag`, `7`/`16` on a ResendRequest). The
    /// set is per message: `108` is engine-owned on a Logon and writable on a
    /// Heartbeat.
    ///
    /// This is a programming error in the customizer, not a runtime condition,
    /// so it is a debug tripwire rather than a release-time check or a `Result`
    /// the caller would have nothing useful to do with.
    #[inline]
    pub fn field(&mut self, tag: u32, value: &[u8]) {
        debug_assert!(
            !(is_framing_tag(tag) || self.owned.contains(&tag)),
            "tag {tag} is engine-owned for MsgType({}); the session stamps it",
            self.msg_type.escape_ascii()
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
    fn customize_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a Logon (35=A) carrying `ResetSeqNumFlag(141)=Y`.
    fn customize_logon_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a Logout (35=5).
    fn customize_logout(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a Heartbeat (35=0).
    fn customize_heartbeat(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a TestRequest (35=1).
    fn customize_test_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a ResendRequest (35=2).
    fn customize_resend_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a SequenceReset (35=4).
    fn customize_sequence_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        let _ = m;
    }

    /// Customize a Reject (35=3).
    fn customize_reject(&self, m: &mut AdminMsgOut<'_, '_>) {
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

    fn hdr() -> AdminHeader<'static> {
        AdminHeader {
            seq: 42,
            sender: b"ME",
            target: b"YOU",
            ts: b"20260716-12:00:00.000",
        }
    }

    #[test]
    fn accessors_read_the_stamped_header() {
        let mut buf = [0u8; 256];
        let h = hdr();
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
        let m = AdminMsgOut::new(&mut fmt, &h, b"A", &[108]);

        assert_eq!(m.seq_num(), 42);
        assert_eq!(m.sender(), b"ME");
        assert_eq!(m.target(), b"YOU");
        assert_eq!(m.sending_time(), b"20260716-12:00:00.000");
        assert_eq!(m.msg_type(), b"A");
    }

    #[test]
    fn field_appends_into_the_frame() {
        let mut buf = [0u8; 256];
        let h = hdr();
        let (start, len) = {
            let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
            let mut m = AdminMsgOut::new(&mut fmt, &h, b"A", &[108]);
            m.field(553, b"user");
            fmt.finish().unwrap()
        };
        let msg = &buf[start..start + len];
        assert!(msg.windows(9).any(|w| w == b"553=user\x01"));
        assert!(crate::validate_checksum(msg).is_ok());
    }

    /// The tripwire is a `debug_assert!`, so it only exists in debug builds —
    /// without the gate this test fails under `cargo test --release`, where no
    /// panic fires.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "engine-owned")]
    fn field_rejects_framing_tag_in_debug() {
        let mut buf = [0u8; 256];
        let h = hdr();
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
        let mut m = AdminMsgOut::new(&mut fmt, &h, b"A", &[108]);
        m.field(34, b"99"); // 34 is framing — owned on every message
    }

    /// A tag in this message's `owned` list trips the tripwire.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "engine-owned")]
    fn field_rejects_this_messages_own_owned_tag_in_debug() {
        let mut buf = [0u8; 256];
        let h = hdr();
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
        let mut m = AdminMsgOut::new(&mut fmt, &h, b"A", &[108]);
        m.field(108, b"30"); // 108 is in the Logon owned list
    }

    /// The asymmetry the data-carried `owned` list buys: 108 is owned on a Logon
    /// but not on a Heartbeat, so the same call succeeds here. Same tag, same
    /// call, opposite outcomes — decided purely by the `owned` slice.
    #[test]
    fn field_accepts_a_tag_owned_by_another_message() {
        let mut buf = [0u8; 256];
        let h = hdr();
        let (start, len) = {
            let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"0");
            // Heartbeat's owned list is `&[112]`; 108 is not in it.
            let mut m = AdminMsgOut::new(&mut fmt, &h, b"0", &[112]);
            m.field(108, b"30");
            fmt.finish().unwrap()
        };
        assert!(
            buf[start..start + len]
                .windows(7)
                .any(|w| w == b"108=30\x01")
        );
    }

    /// The tags real venue auth writes are never framing tags, so a Logon hook
    /// can always write them regardless of its `owned` list.
    #[test]
    fn venue_body_tags_are_not_framing() {
        for tag in [96, 553, 554, 5000] {
            assert!(!is_framing_tag(tag), "tag {tag} must be writable by a hook");
        }
    }
}
