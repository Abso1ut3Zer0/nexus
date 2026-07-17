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

/// Which admin message is being built.
///
/// Single source of truth for a message's identity: it names the `MsgType(35)`
/// written into the frame *and* the one the customizer's accessor reads back
/// ([`AdminMsgOut::msg_type`]), so the wire value and the value a venue signs
/// over cannot diverge. It also selects the per-message engine params the
/// [`field`](AdminMsgOut::field) tripwire rejects.
///
/// `Logon` and `LogonReset` share `MsgType(35)=A` but are distinct kinds: the
/// reset variant's encoder writes `ResetSeqNumFlag(141)` and the plain one does
/// not, and the tripwire is exact about that.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdminKind {
    /// Logon (35=A).
    Logon,
    /// Logon carrying `ResetSeqNumFlag(141)=Y` (35=A).
    LogonReset,
    /// Logout (35=5).
    Logout,
    /// Heartbeat (35=0).
    Heartbeat,
    /// TestRequest (35=1).
    TestRequest,
    /// ResendRequest (35=2).
    ResendRequest,
    /// SequenceReset (35=4).
    SequenceReset,
    /// Reject (35=3).
    Reject,
}

impl AdminKind {
    /// The `MsgType(35)` value for this kind.
    #[inline]
    pub const fn msg_type(self) -> &'static [u8] {
        match self {
            Self::Logon | Self::LogonReset => b"A",
            Self::Logout => b"5",
            Self::Heartbeat => b"0",
            Self::TestRequest => b"1",
            Self::ResendRequest => b"2",
            Self::SequenceReset => b"4",
            Self::Reject => b"3",
        }
    }

    /// The body tags this kind's `FixDictionary::encode_*` writes, in the order
    /// it writes them.
    ///
    /// Mirrors the encoder bodies in [`dict`](crate::dict) exactly — the
    /// definition is "tags this message's own encoder already wrote", so a
    /// customizer writing one would emit a duplicate. Tags an encoder writes
    /// *conditionally* (`112` only when a Heartbeat echoes a TestReqID, `371`
    /// only when a Reject cites a tag) are listed unconditionally: the tripwire
    /// is deliberately conservative, since a customizer has no business writing
    /// a tag its message's encoder may already own.
    // One arm per encoder body, even where two encoders agree today (Heartbeat
    // and TestRequest both write 112). Collapsing them would couple two
    // independent encoders, and the next field added to one would silently
    // widen the other's tripwire.
    #[allow(clippy::match_same_arms)]
    #[inline]
    const fn engine_params(self) -> &'static [u32] {
        match self {
            // encode_logon: 108
            Self::Logon => &[108],
            // encode_logon_reset: 108, 141
            Self::LogonReset => &[108, 141],
            // encode_logout: header only
            Self::Logout => &[],
            // encode_heartbeat: 112 (when echoing)
            Self::Heartbeat => &[112],
            // encode_test_request: 112
            Self::TestRequest => &[112],
            // encode_resend_request: 7, 16
            Self::ResendRequest => &[7, 16],
            // encode_sequence_reset: 43, 123, 36
            Self::SequenceReset => &[43, 123, 36],
            // encode_reject: 45, 371 (when present), 373
            Self::Reject => &[45, 371, 373],
        }
    }
}

/// Whether `tag` is one the engine writes for `kind` — the session framing and
/// header it stamps on every admin message, plus the params this message's own
/// encoder already wrote. A customizer writing one emits a duplicate and the
/// venue rejects the message.
#[inline]
const fn is_engine_owned(tag: u32, kind: AdminKind) -> bool {
    // Framing (8/9/10) and the session header (34/35/49/52/56): every message.
    if matches!(tag, 8 | 9 | 10 | 34 | 35 | 49 | 52 | 56) {
        return true;
    }
    let params = kind.engine_params();
    let mut i = 0;
    while i < params.len() {
        if params[i] == tag {
            return true;
        }
        i += 1;
    }
    false
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
    kind: AdminKind,
}

impl<'f, 'h> AdminMsgOut<'f, 'h> {
    /// Wrap an in-progress frame whose session header has already been stamped.
    ///
    /// Called by the engine between the dictionary's standard-field encode and
    /// [`FrameFormatter::finish`]. `kind` must be the message the frame was
    /// started for — it is what [`msg_type`](Self::msg_type) reports and what
    /// the [`field`](Self::field) tripwire matches against.
    #[inline]
    pub fn new(fmt: &'f mut FrameFormatter<'h>, hdr: &'f AdminHeader<'h>, kind: AdminKind) -> Self {
        Self { fmt, hdr, kind }
    }

    /// Which admin message this is.
    #[inline]
    pub fn kind(&self) -> AdminKind {
        self.kind
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

    /// `MsgType` (tag 35) of the message being built — the same value written
    /// into the frame, since both come from [`kind`](Self::kind).
    #[inline]
    pub fn msg_type(&self) -> &'static [u8] {
        self.kind.msg_type()
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
    /// message (8, 9, 10, 34, 35, 49, 52, 56) plus the params this message's own
    /// encoder writes (for example `108` on a Logon, `141` on a Logon carrying
    /// `ResetSeqNumFlag`, `7`/`16` on a ResendRequest). The set is per message:
    /// `108` is engine-owned on a Logon and writable on a Heartbeat.
    ///
    /// This is a programming error in the customizer, not a runtime condition,
    /// so it is a debug tripwire rather than a release-time check or a `Result`
    /// the caller would have nothing useful to do with.
    #[inline]
    pub fn field(&mut self, tag: u32, value: &[u8]) {
        debug_assert!(
            !is_engine_owned(tag, self.kind),
            "tag {tag} is engine-owned for {:?}; the session stamps it",
            self.kind
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

    const ALL_KINDS: [AdminKind; 8] = [
        AdminKind::Logon,
        AdminKind::LogonReset,
        AdminKind::Logout,
        AdminKind::Heartbeat,
        AdminKind::TestRequest,
        AdminKind::ResendRequest,
        AdminKind::SequenceReset,
        AdminKind::Reject,
    ];

    #[test]
    fn session_framing_is_engine_owned_on_every_kind() {
        for kind in ALL_KINDS {
            for tag in [8, 9, 10, 34, 35, 49, 52, 56] {
                assert!(
                    is_engine_owned(tag, kind),
                    "tag {tag} must be engine-owned on {kind:?}"
                );
            }
        }
    }

    /// Pins the per-message table against the `encode_*` bodies in `dict.rs`.
    /// If an encoder gains a field, this list must gain it too — otherwise the
    /// tripwire goes quiet on a tag the engine now duplicates.
    #[test]
    fn engine_params_match_the_encoder_bodies() {
        let table: &[(AdminKind, &[u32])] = &[
            (AdminKind::Logon, &[108]),
            (AdminKind::LogonReset, &[108, 141]),
            (AdminKind::Logout, &[]),
            (AdminKind::Heartbeat, &[112]),
            (AdminKind::TestRequest, &[112]),
            (AdminKind::ResendRequest, &[7, 16]),
            (AdminKind::SequenceReset, &[43, 123, 36]),
            (AdminKind::Reject, &[45, 371, 373]),
        ];
        for (kind, params) in table {
            assert_eq!(kind.engine_params(), *params, "engine params for {kind:?}");
            for tag in *params {
                assert!(
                    is_engine_owned(*tag, *kind),
                    "tag {tag} must be engine-owned on {kind:?}"
                );
            }
        }
    }

    /// The point of making the check per-message: a tag the engine owns on one
    /// message is the venue's to write on another.
    #[test]
    fn engine_params_are_scoped_to_their_own_message() {
        // 108 (HeartBtInt): the Logon pair's encoders write it; nothing else does.
        assert!(is_engine_owned(108, AdminKind::Logon));
        assert!(is_engine_owned(108, AdminKind::LogonReset));
        for kind in [
            AdminKind::Logout,
            AdminKind::Heartbeat,
            AdminKind::TestRequest,
            AdminKind::ResendRequest,
            AdminKind::SequenceReset,
            AdminKind::Reject,
        ] {
            assert!(
                !is_engine_owned(108, kind),
                "108 is not written by {kind:?}'s encoder, so the venue may write it"
            );
        }

        // 141 (ResetSeqNumFlag): only the reset variant — same MsgType as Logon,
        // different kind, and the tripwire distinguishes them.
        assert!(is_engine_owned(141, AdminKind::LogonReset));
        assert!(!is_engine_owned(141, AdminKind::Logon));

        // 112 (TestReqID): Heartbeat echo and TestRequest, not the Logon pair.
        assert!(is_engine_owned(112, AdminKind::Heartbeat));
        assert!(is_engine_owned(112, AdminKind::TestRequest));
        assert!(!is_engine_owned(112, AdminKind::Logon));
    }

    #[test]
    fn venue_body_tags_are_never_engine_owned() {
        // The tags real venue auth writes, on the message that writes them.
        for tag in [96, 553, 554, 5000] {
            assert!(
                !is_engine_owned(tag, AdminKind::Logon),
                "tag {tag} must be writable by a Logon customizer"
            );
        }
    }

    #[test]
    fn msg_type_is_the_wire_value_for_every_kind() {
        let expected: &[(AdminKind, &[u8])] = &[
            (AdminKind::Logon, b"A"),
            (AdminKind::LogonReset, b"A"),
            (AdminKind::Logout, b"5"),
            (AdminKind::Heartbeat, b"0"),
            (AdminKind::TestRequest, b"1"),
            (AdminKind::ResendRequest, b"2"),
            (AdminKind::SequenceReset, b"4"),
            (AdminKind::Reject, b"3"),
        ];
        for (kind, mt) in expected {
            assert_eq!(kind.msg_type(), *mt, "MsgType for {kind:?}");
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
        let m = AdminMsgOut::new(&mut fmt, &hdr, AdminKind::Logon);

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
            let mut m = AdminMsgOut::new(&mut fmt, &hdr, AdminKind::Logon);
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
    fn field_rejects_engine_owned_tag_in_debug() {
        let mut buf = [0u8; 256];
        let hdr = AdminHeader {
            seq: 1,
            sender: b"ME",
            target: b"YOU",
            ts: b"20260716-12:00:00.000",
        };
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
        let mut m = AdminMsgOut::new(&mut fmt, &hdr, AdminKind::Logon);
        m.field(34, b"99");
    }

    /// 108 is the Logon encoder's own param — and writable on a Heartbeat, whose
    /// encoder never writes it. Same tag, same call, opposite outcomes.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "engine-owned")]
    fn field_rejects_this_messages_own_engine_param_in_debug() {
        let mut buf = [0u8; 256];
        let hdr = AdminHeader {
            seq: 1,
            sender: b"ME",
            target: b"YOU",
            ts: b"20260716-12:00:00.000",
        };
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"A");
        let mut m = AdminMsgOut::new(&mut fmt, &hdr, AdminKind::Logon);
        m.field(108, b"30");
    }

    #[test]
    fn field_accepts_a_tag_another_message_owns() {
        let mut buf = [0u8; 256];
        let hdr = AdminHeader {
            seq: 1,
            sender: b"ME",
            target: b"YOU",
            ts: b"20260716-12:00:00.000",
        };
        let (start, len) = {
            let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"0");
            let mut m = AdminMsgOut::new(&mut fmt, &hdr, AdminKind::Heartbeat);
            m.field(108, b"30"); // engine-owned on Logon, not on Heartbeat
            fmt.finish().unwrap()
        };
        assert!(
            buf[start..start + len]
                .windows(7)
                .any(|w| w == b"108=30\x01")
        );
    }
}
