use crate::field::FieldView;
use crate::types::FixTimestamp;
use crate::writer::FrameFormatter;
use nexus_ascii::AsciiTextStr;

/// Zero-copy decoder for a session-level admin message.
///
/// Implemented by every generated admin message type in `admin::*`.
/// The session framework calls `decode` to construct the decoder and hands it
/// to the caller via the engine's `Message` type; the caller then uses the
/// typed accessor methods to read fields.
pub trait FixAdminMsg<'buf>: Sized {
    /// Construct the decoder from a raw FIX message buffer.
    fn decode(buf: &'buf [u8]) -> Result<Self, crate::DecodeError>;
}

pub struct AdminHeader<'a> {
    pub seq: u32,
    pub sender: &'a [u8],
    pub target: &'a [u8],
    pub ts: &'a [u8],
}

fn write_admin_header(fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>) {
    use crate::types::encode_fix_uint;
    let mut buf = [0u8; 10];
    let n = encode_fix_uint(hdr.seq, &mut buf);
    fmt.field(34, &buf[..n]);
    fmt.field(49, hdr.sender);
    fmt.field(56, hdr.target);
    fmt.field(52, hdr.ts);
}

/// Dictionary-level knowledge for a specific FIX version.
///
/// Generated per dictionary (FIX 4.2, FIX 4.4, etc.) by `nexus-fix-codegen`.
/// The implementing type is a zero-sized struct — all information is
/// compile-time. The `Session` is generic over this trait, so
/// FIX-version dispatch monomorphizes away with no vtable or runtime branching.
pub trait FixDictionary {
    /// The dictionary's message-type enum (generated, closed set).
    type MsgType: Copy + Eq + core::fmt::Debug;

    /// The dictionary's generated header decoder type.
    type Header<'buf>: FixHeader<'buf>;

    /// Decoder for Logon (35=A).
    type Logon<'buf>: FixAdminMsg<'buf>;
    /// Decoder for Logout (35=5).
    type Logout<'buf>: FixAdminMsg<'buf>;
    /// Decoder for Heartbeat (35=0).
    type Heartbeat<'buf>: FixAdminMsg<'buf>;
    /// Decoder for TestRequest (35=1).
    type TestRequest<'buf>: FixAdminMsg<'buf>;
    /// Decoder for ResendRequest (35=2).
    type ResendRequest<'buf>: FixAdminMsg<'buf>;
    /// Decoder for SequenceReset (35=4).
    type SequenceReset<'buf>: FixAdminMsg<'buf>;
    /// Decoder for Reject (35=3).
    type Reject<'buf>: FixAdminMsg<'buf>;

    /// The `BeginString` value for this FIX version (e.g. `b"FIX.4.4"`).
    const BEGIN_STRING: &'static [u8];

    /// Whether the given message type is an admin (session-level) message.
    fn is_admin(msg_type: Self::MsgType) -> bool;

    /// Body tags [`encode_logon`](Self::encode_logon) writes.
    ///
    /// The `SessionCustomizer` tripwire in
    /// [`AdminMsgOut::field`](crate::AdminMsgOut::field) rejects a venue hook
    /// that writes one of these — it would duplicate a field the engine already
    /// wrote. Each `*_OWNED` const lives next to its encoder so a reader adding a
    /// field to the encoder sees the list to keep in sync; the engine's
    /// `encode_admin` passes it to `AdminMsgOut::new`.
    const LOGON_OWNED: &'static [u32] = &[108];

    /// Write Logon's (35=A) standard fields into an already-started frame.
    ///
    /// The caller owns the frame lifecycle — [`FrameFormatter::new`] (which
    /// writes `8`/`35`) and [`FrameFormatter::finish`] (which computes `9`/`10`)
    /// — so it can run a
    /// [`SessionCustomizer`](crate::SessionCustomizer) hook between this call
    /// and `finish`, and have the hook's fields covered by BodyLength and the
    /// checksum. Same contract for every `encode_*` below.
    fn encode_logon(fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>, heart_bt_int_s: u32) {
        use crate::types::encode_fix_uint;
        write_admin_header(fmt, hdr);
        let mut tmp = [0u8; 10];
        let n = encode_fix_uint(heart_bt_int_s, &mut tmp);
        fmt.field(108, &tmp[..n]);
    }

    /// Body tags [`encode_logon_reset`](Self::encode_logon_reset) writes.
    /// See [`LOGON_OWNED`](Self::LOGON_OWNED).
    const LOGON_RESET_OWNED: &'static [u32] = &[108, 141];

    /// Write Logon-with-`ResetSeqNumFlag` (35=A, 141=Y) standard fields.
    fn encode_logon_reset(
        fmt: &mut FrameFormatter<'_>,
        hdr: &AdminHeader<'_>,
        heart_bt_int_s: u32,
    ) {
        use crate::types::encode_fix_uint;
        write_admin_header(fmt, hdr);
        let mut tmp = [0u8; 10];
        let n = encode_fix_uint(heart_bt_int_s, &mut tmp);
        fmt.field(108, &tmp[..n]);
        fmt.field(141, b"Y");
    }

    /// Body tags [`encode_logout`](Self::encode_logout) writes. `58` is written
    /// only when a reason string is supplied, but the tripwire is unconditional.
    /// See [`LOGON_OWNED`](Self::LOGON_OWNED).
    const LOGOUT_OWNED: &'static [u32] = &[58];

    /// Write Logout's (35=5) standard fields, appending `Text(58)` if a reason is
    /// given.
    ///
    /// `reason` is a printable-ASCII [`AsciiTextStr`] — SOH-safe by construction —
    /// so appending it can never break framing; encoding is infallible w.r.t. the
    /// reason.
    fn encode_logout(
        fmt: &mut FrameFormatter<'_>,
        hdr: &AdminHeader<'_>,
        reason: Option<&AsciiTextStr>,
    ) {
        write_admin_header(fmt, hdr);
        if let Some(text) = reason {
            fmt.field(58, text.as_bytes());
        }
    }

    /// Body tags [`encode_heartbeat`](Self::encode_heartbeat) writes. `112` is
    /// written only when echoing a `TestReqID`, but the tripwire is
    /// unconditional: a hook has no business writing a tag the encoder may own.
    /// See [`LOGON_OWNED`](Self::LOGON_OWNED).
    const HEARTBEAT_OWNED: &'static [u32] = &[112];

    /// Write Heartbeat's (35=0) standard fields, echoing `TestReqID` if given.
    fn encode_heartbeat(fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>, echo: Option<&[u8]>) {
        write_admin_header(fmt, hdr);
        if let Some(id) = echo {
            fmt.field(112, id);
        }
    }

    /// Body tags [`encode_test_request`](Self::encode_test_request) writes.
    /// See [`LOGON_OWNED`](Self::LOGON_OWNED).
    const TEST_REQUEST_OWNED: &'static [u32] = &[112];

    /// Write TestRequest's (35=1) standard fields.
    fn encode_test_request(fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>, id: u64) {
        use crate::types::encode_fix_seqnum;
        write_admin_header(fmt, hdr);
        let mut tmp = [0u8; 20];
        let n = encode_fix_seqnum(id, &mut tmp);
        fmt.field(112, &tmp[..n]);
    }

    /// Body tags [`encode_resend_request`](Self::encode_resend_request) writes.
    /// See [`LOGON_OWNED`](Self::LOGON_OWNED).
    const RESEND_REQUEST_OWNED: &'static [u32] = &[7, 16];

    /// Write ResendRequest's (35=2) standard fields.
    fn encode_resend_request(fmt: &mut FrameFormatter<'_>, hdr: &AdminHeader<'_>, begin_seq: u32) {
        use crate::types::encode_fix_uint;
        write_admin_header(fmt, hdr);
        let mut tmp = [0u8; 10];
        let n = encode_fix_uint(begin_seq, &mut tmp);
        fmt.field(7, &tmp[..n]);
        fmt.field(16, b"0");
    }

    /// Body tags [`encode_sequence_reset`](Self::encode_sequence_reset) writes.
    /// See [`LOGON_OWNED`](Self::LOGON_OWNED).
    const SEQUENCE_RESET_OWNED: &'static [u32] = &[43, 123, 36];

    /// Write SequenceReset's (35=4) standard fields.
    ///
    /// `gap_fill = true` is GapFill mode: `PossDupFlag(43)=Y` +
    /// `GapFillFlag(123)=Y`, used to replace admin holes during a resend, so the
    /// receiver validates the sequence and advances to `NewSeqNo`. `gap_fill =
    /// false` is Reset mode: `GapFillFlag(123)=N`, no `PossDupFlag` — an
    /// administrative reset the receiver honors unconditionally, forcing its
    /// expected inbound seqnum to `NewSeqNo` regardless of `MsgSeqNum`.
    fn encode_sequence_reset(
        fmt: &mut FrameFormatter<'_>,
        hdr: &AdminHeader<'_>,
        new_seq: u32,
        gap_fill: bool,
    ) {
        use crate::types::encode_fix_uint;
        write_admin_header(fmt, hdr);
        if gap_fill {
            fmt.field(43, b"Y");
            fmt.field(123, b"Y");
        } else {
            fmt.field(123, b"N");
        }
        let mut tmp = [0u8; 10];
        let n = encode_fix_uint(new_seq, &mut tmp);
        fmt.field(36, &tmp[..n]);
    }

    /// Body tags [`encode_reject`](Self::encode_reject) writes. `371` is written
    /// only when a `RefTagID` is cited and `58` only when a reason string is
    /// supplied, but the tripwire is unconditional.
    /// See [`LOGON_OWNED`](Self::LOGON_OWNED).
    const REJECT_OWNED: &'static [u32] = &[45, 371, 373, 58];

    /// Write Reject's (35=3) standard fields, appending `Text(58)` if a reason is
    /// given.
    ///
    /// `reason` is a printable-ASCII [`AsciiTextStr`] — SOH-safe by construction —
    /// so appending it can never break framing.
    fn encode_reject(
        fmt: &mut FrameFormatter<'_>,
        hdr: &AdminHeader<'_>,
        ref_seq_num: u32,
        ref_tag_id: Option<u32>,
        session_reject_reason: u8,
        reason: Option<&AsciiTextStr>,
    ) {
        use crate::types::encode_fix_uint;
        write_admin_header(fmt, hdr);
        let mut tmp = [0u8; 10];
        let n = encode_fix_uint(ref_seq_num, &mut tmp);
        fmt.field(45, &tmp[..n]);
        if let Some(tag) = ref_tag_id {
            let n = encode_fix_uint(tag, &mut tmp);
            fmt.field(371, &tmp[..n]);
        }
        let n = encode_fix_uint(session_reject_reason as u32, &mut tmp);
        fmt.field(373, &tmp[..n]);
        if let Some(text) = reason {
            fmt.field(58, text.as_bytes());
        }
    }
}

/// Session-level header field access.
///
/// Implemented by every generated `HeaderDecoder`. Provides the protocol-
/// mandatory fields that session-layer code needs for sequencing, routing,
/// and heartbeat logic — without knowing which dictionary is in use.
pub trait FixHeader<'buf>: Sized {
    /// Decode the header from a raw FIX message buffer.
    fn decode(buf: &'buf [u8]) -> Self;

    /// Raw `MsgType` bytes (tag 35) for session-layer admin detection.
    fn raw_msg_type(&self) -> Option<FieldView<'buf, &'buf [u8]>>;

    /// `MsgSeqNum` (tag 34).
    fn msg_seq_num(&self) -> Option<FieldView<'buf, u64>>;

    /// `SenderCompID` (tag 49).
    fn sender_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>>;

    /// `TargetCompID` (tag 56).
    fn target_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>>;

    /// `PossDupFlag` (tag 43).
    fn poss_dup_flag(&self) -> Option<FieldView<'buf, bool>>;

    /// `SendingTime` (tag 52).
    fn sending_time(&self) -> Option<FieldView<'buf, FixTimestamp>>;
}
