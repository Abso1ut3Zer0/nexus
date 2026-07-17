//! Venue auth seam: the `SessionCustomizer` hook fires after the engine stamps
//! the session header and before framing computes BodyLength/CheckSum.
//!
//! The load-bearing property is that the hook writes *inside* the frame: 9 and
//! 10 must be correct over whatever it injected, and the accessors must return
//! the values actually stamped on the wire so a venue can sign over them.

#![cfg(unix)]

use nexus_fix_codec::{
    AdminMsgOut, DecodeError, FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp,
    NoCustomizer, SessionCustomizer, find_tag, validate_checksum,
};
use nexus_fix_engine::{AdminMsg, CompId, MessageWriter, SessionConfig};

// ── minimal mock dictionary ──────────────────────────────────────────────────

struct MockDict;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum MockMsgType {}

struct AdminDecoder<'buf> {
    _buf: &'buf [u8],
}

impl<'buf> FixAdminMsg<'buf> for AdminDecoder<'buf> {
    fn decode(buf: &'buf [u8]) -> Result<Self, DecodeError> {
        Ok(Self { _buf: buf })
    }
}

struct MockHeader<'buf> {
    buf: &'buf [u8],
}

impl<'buf> FixHeader<'buf> for MockHeader<'buf> {
    fn decode(buf: &'buf [u8]) -> Self {
        Self { buf }
    }
    fn raw_msg_type(&self) -> Option<FieldView<'buf, &'buf [u8]>> {
        find_tag(self.buf, 0, 35).and_then(|s| FieldView::new(s, self.buf))
    }
    fn msg_seq_num(&self) -> Option<FieldView<'buf, u64>> {
        find_tag(self.buf, 0, 34).and_then(|s| FieldView::new(s, self.buf))
    }
    fn sender_comp_id(&self) -> Option<FieldView<'buf, &'buf nexus_fix_codec::AsciiTextStr>> {
        find_tag(self.buf, 0, 49).and_then(|s| FieldView::new(s, self.buf))
    }
    fn target_comp_id(&self) -> Option<FieldView<'buf, &'buf nexus_fix_codec::AsciiTextStr>> {
        find_tag(self.buf, 0, 56).and_then(|s| FieldView::new(s, self.buf))
    }
    fn poss_dup_flag(&self) -> Option<FieldView<'buf, bool>> {
        find_tag(self.buf, 0, 43).and_then(|s| FieldView::new(s, self.buf))
    }
    fn sending_time(&self) -> Option<FieldView<'buf, FixTimestamp>> {
        None
    }
}

impl FixDictionary for MockDict {
    type MsgType = MockMsgType;
    type Header<'buf> = MockHeader<'buf>;
    type Logon<'buf> = AdminDecoder<'buf>;
    type Logout<'buf> = AdminDecoder<'buf>;
    type Heartbeat<'buf> = AdminDecoder<'buf>;
    type TestRequest<'buf> = AdminDecoder<'buf>;
    type ResendRequest<'buf> = AdminDecoder<'buf>;
    type SequenceReset<'buf> = AdminDecoder<'buf>;
    type Reject<'buf> = AdminDecoder<'buf>;
    const BEGIN_STRING: &'static [u8] = b"FIX.4.4";
    fn is_admin(_: MockMsgType) -> bool {
        false
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────

fn config() -> SessionConfig {
    SessionConfig {
        sender: CompId::new(b"SENDER").unwrap(),
        target: CompId::new(b"TARGET").unwrap(),
    }
}

fn tag(frame: &[u8], t: u32) -> Option<&[u8]> {
    find_tag(frame, 0, t).map(|s| s.slice(frame))
}

fn has_field(frame: &[u8], field: &[u8]) -> bool {
    frame.windows(field.len()).any(|w| w == field)
}

/// A stand-in for a venue's HMAC. The point of the signing tests is that the
/// hook sees the *stamped* header, not which digest is used, so this avoids
/// pulling a crypto dependency into the engine's dev-deps.
fn fnv1a(data: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in data {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

fn soh_join(parts: &[&[u8]]) -> Vec<u8> {
    let mut out = Vec::new();
    for (i, p) in parts.iter().enumerate() {
        if i > 0 {
            out.push(0x01);
        }
        out.extend_from_slice(p);
    }
    out
}

// ── customizers under test ───────────────────────────────────────────────────

/// Injects static credentials into Logon only.
struct TestAuth;

impl SessionCustomizer for TestAuth {
    fn configure_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(553, b"trader-1");
        m.field(554, b"s3cret");
    }
}

/// Coinbase's shape: signs the SOH-joined stamped header into RawData(96).
struct SigningAuth;

impl SessionCustomizer for SigningAuth {
    fn configure_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
        let seq = m.seq_num().to_string();
        let presign = soh_join(&[
            m.sending_time(),
            m.msg_type(),
            seq.as_bytes(),
            m.sender(),
            m.target(),
        ]);
        m.field(96, fnv1a(&presign).to_string().as_bytes());
    }
}

// ── NoCustomizer: byte-identical frames ──────────────────────────────────────

/// Pins the exact wire bytes of the `NoCustomizer` path against an oracle that
/// hand-builds the frame the way the pre-hook one-shot encoder did: same field
/// order, same BodyLength, same checksum. `SendingTime` is lifted out of the
/// produced frame so the two are comparable.
///
/// If the seam split had perturbed field order, framing, or the checksum, this
/// fails on the full byte string.
fn assert_matches_oracle(admin: AdminMsg, msg_type: &[u8], body: &[(u32, Vec<u8>)]) {
    use nexus_fix_codec::FrameFormatter;

    let mut w: MessageWriter<MockDict> = MessageWriter::new();
    w.encode_admin(admin, &config());
    let produced = w.data().to_vec();

    let ts = tag(&produced, 52).expect("52 stamped").to_vec();
    let seq = tag(&produced, 34).expect("34 stamped").to_vec();

    let mut buf = [0u8; 512];
    let mut f = FrameFormatter::new(&mut buf, b"FIX.4.4", msg_type);
    f.field(34, &seq);
    f.field(49, b"SENDER");
    f.field(56, b"TARGET");
    f.field(52, &ts);
    for (t, v) in body {
        f.field(*t, v);
    }
    let (start, len) = f.finish().unwrap();
    let oracle = &buf[start..start + len];

    assert_eq!(
        produced.as_slice(),
        oracle,
        "NoCustomizer frame must be byte-identical to the pre-hook encoding\n produced: {:?}\n oracle:   {:?}",
        String::from_utf8_lossy(&produced),
        String::from_utf8_lossy(oracle),
    );
}

#[test]
fn no_customizer_logon_is_byte_identical() {
    assert_matches_oracle(
        AdminMsg::Logon {
            seq: 1,
            heart_bt_int_s: 30,
        },
        b"A",
        &[(108, b"30".to_vec())],
    );
}

#[test]
fn no_customizer_logon_reset_is_byte_identical() {
    assert_matches_oracle(
        AdminMsg::LogonReset {
            seq: 1,
            heart_bt_int_s: 30,
        },
        b"A",
        &[(108, b"30".to_vec()), (141, b"Y".to_vec())],
    );
}

#[test]
fn no_customizer_logout_is_byte_identical() {
    assert_matches_oracle(AdminMsg::Logout { seq: 2 }, b"5", &[]);
}

#[test]
fn no_customizer_heartbeat_is_byte_identical() {
    assert_matches_oracle(AdminMsg::Heartbeat { seq: 3, echo: None }, b"0", &[]);
}

#[test]
fn no_customizer_heartbeat_with_echo_is_byte_identical() {
    // 64 = the engine's internal TestReqID capacity (private; the public
    // `AdminMsg::Heartbeat` variant names the array size structurally).
    let mut id = [0u8; 64];
    id[..4].copy_from_slice(b"TR-1");
    assert_matches_oracle(
        AdminMsg::Heartbeat {
            seq: 3,
            echo: Some((id, 4)),
        },
        b"0",
        &[(112, b"TR-1".to_vec())],
    );
}

#[test]
fn no_customizer_test_request_is_byte_identical() {
    assert_matches_oracle(
        AdminMsg::TestRequest { seq: 4, id: 77 },
        b"1",
        &[(112, b"77".to_vec())],
    );
}

#[test]
fn no_customizer_resend_request_is_byte_identical() {
    assert_matches_oracle(
        AdminMsg::ResendRequest { seq: 5, begin: 2 },
        b"2",
        &[(7, b"2".to_vec()), (16, b"0".to_vec())],
    );
}

#[test]
fn no_customizer_sequence_reset_is_byte_identical() {
    assert_matches_oracle(
        AdminMsg::SequenceReset {
            seq: 6,
            new_seq: 10,
        },
        b"4",
        &[
            (43, b"Y".to_vec()),
            (123, b"Y".to_vec()),
            (36, b"10".to_vec()),
        ],
    );
}

#[test]
fn no_customizer_reject_is_byte_identical() {
    assert_matches_oracle(
        AdminMsg::Reject {
            seq: 7,
            ref_seq_num: 3,
            ref_tag_id: Some(35),
            session_reject_reason: 1,
        },
        b"3",
        &[
            (45, b"3".to_vec()),
            (371, b"35".to_vec()),
            (373, b"1".to_vec()),
        ],
    );
}

// ── the seam's guarantee: 9 and 10 cover the injected fields ─────────────────

#[test]
fn injected_fields_are_on_the_wire() {
    let mut w: MessageWriter<MockDict, TestAuth> = MessageWriter::with_customizer(TestAuth);
    w.encode_admin(
        AdminMsg::Logon {
            seq: 1,
            heart_bt_int_s: 30,
        },
        &config(),
    );
    let data = w.data();

    assert!(
        has_field(data, b"553=trader-1\x01"),
        "553 must be on the wire"
    );
    assert!(
        has_field(data, b"554=s3cret\x01"),
        "554 must be on the wire"
    );
    // The standard fields still land, and the hook's fields follow them.
    assert!(has_field(data, b"108=30\x01"));
}

/// The seam's entire reason to exist: the hook runs *inside* the frame, so
/// BodyLength and CheckSum are computed over what it injected.
///
/// `validate_checksum` recomputes 10 over the frame; BodyLength is checked
/// against the actual byte count between the 9 field and the 10 field. Both are
/// independent of the encoder's own arithmetic.
#[test]
fn body_length_and_checksum_cover_injected_fields() {
    let mut w: MessageWriter<MockDict, TestAuth> = MessageWriter::with_customizer(TestAuth);
    w.encode_admin(
        AdminMsg::Logon {
            seq: 1,
            heart_bt_int_s: 30,
        },
        &config(),
    );
    let data = w.data();

    assert!(
        validate_checksum(data).is_ok(),
        "CheckSum(10) must be valid over the injected fields"
    );

    // BodyLength counts from the byte after 9=…SOH to the byte before 10=.
    let declared: usize = std::str::from_utf8(tag(data, 9).expect("9 present"))
        .unwrap()
        .parse()
        .unwrap();
    let nine = find_tag(data, 0, 9).unwrap();
    // The span covers 9's *value*; the body starts past it and its SOH.
    let body_start = (nine.offset + nine.len) as usize + 1;
    let ten_start = data.len() - 7; // "10=DDD\x01"
    assert_eq!(
        declared,
        ten_start - body_start,
        "BodyLength(9) must count the injected fields"
    );

    // And the injected fields are genuinely inside the counted region.
    let body = &data[body_start..ten_start];
    assert!(has_field(body, b"553=trader-1\x01"));
    assert!(has_field(body, b"554=s3cret\x01"));
}

// ── read accessors expose the stamped header ─────────────────────────────────

/// The hook signs over the header the engine stamped. The test re-derives the
/// expected digest from the *wire frame's own* 52/35/34/49/56 — never from the
/// customizer — so it fails if any accessor returns something other than what
/// was actually stamped.
#[test]
fn accessors_return_the_stamped_header_inside_the_hook() {
    let mut w: MessageWriter<MockDict, SigningAuth> = MessageWriter::with_customizer(SigningAuth);
    w.encode_admin(
        AdminMsg::Logon {
            seq: 7,
            heart_bt_int_s: 30,
        },
        &config(),
    );
    let data = w.data();

    let expected = fnv1a(&soh_join(&[
        tag(data, 52).expect("52 on the wire"),
        tag(data, 35).expect("35 on the wire"),
        tag(data, 34).expect("34 on the wire"),
        tag(data, 49).expect("49 on the wire"),
        tag(data, 56).expect("56 on the wire"),
    ]))
    .to_string();

    let signature = tag(data, 96).expect("96 injected by the hook");
    assert_eq!(
        signature,
        expected.as_bytes(),
        "the hook must sign over the header as stamped on the wire"
    );

    // Sanity: the stamped seq is the one we asked for, so the digest above is
    // not trivially matching on empty/garbage input.
    assert_eq!(tag(data, 34).unwrap(), b"7");
    assert!(validate_checksum(data).is_ok());
}

// ── per-message dispatch ─────────────────────────────────────────────────────

/// The QuickFIX miswiring we designed out: a single undifferentiated hook fires
/// for every admin type, so apps leak Logon credentials into Heartbeats. With
/// per-message defaulted no-ops, a `configure_logon`-only customizer cannot.
#[test]
fn logon_only_customizer_leaves_other_admin_messages_untouched() {
    let others: Vec<AdminMsg> = vec![
        AdminMsg::Logout { seq: 2 },
        AdminMsg::Heartbeat { seq: 3, echo: None },
        AdminMsg::TestRequest { seq: 4, id: 1 },
        AdminMsg::ResendRequest { seq: 5, begin: 1 },
        AdminMsg::SequenceReset {
            seq: 6,
            new_seq: 10,
        },
        AdminMsg::Reject {
            seq: 7,
            ref_seq_num: 1,
            ref_tag_id: None,
            session_reject_reason: 1,
        },
    ];

    for admin in others {
        let mut w: MessageWriter<MockDict, TestAuth> = MessageWriter::with_customizer(TestAuth);
        w.encode_admin(admin, &config());
        let data = w.data();
        assert!(
            !has_field(data, b"553="),
            "credentials must not leak into non-Logon admin: {}",
            String::from_utf8_lossy(data)
        );
        assert!(
            !has_field(data, b"554="),
            "credentials must not leak into non-Logon admin: {}",
            String::from_utf8_lossy(data)
        );
    }
}

/// A `configure_logon`-only customizer must produce byte-identical Heartbeats to
/// the `NoCustomizer` path — the defaulted no-op adds nothing at all.
#[test]
fn logon_only_customizer_heartbeat_matches_no_customizer() {
    let mut plain: MessageWriter<MockDict, NoCustomizer> =
        MessageWriter::with_customizer(NoCustomizer);
    plain.encode_admin(AdminMsg::Heartbeat { seq: 3, echo: None }, &config());
    let plain_body = tag(plain.data(), 9).map(|_| plain.data().len());

    let mut authed: MessageWriter<MockDict, TestAuth> = MessageWriter::with_customizer(TestAuth);
    authed.encode_admin(AdminMsg::Heartbeat { seq: 3, echo: None }, &config());

    // Same length and same BodyLength: the hook contributed nothing. (Full byte
    // equality would compare two different SendingTimes.)
    assert_eq!(plain_body, Some(authed.data().len()));
    assert_eq!(tag(plain.data(), 9), tag(authed.data(), 9));
}

// ── the Logon hook still applies on the reset variant ────────────────────────

#[test]
fn logon_reset_has_its_own_hook() {
    struct ResetOnly;
    impl SessionCustomizer for ResetOnly {
        fn configure_logon_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(553, b"reset-user");
        }
    }

    let mut w: MessageWriter<MockDict, ResetOnly> = MessageWriter::with_customizer(ResetOnly);
    w.encode_admin(
        AdminMsg::LogonReset {
            seq: 1,
            heart_bt_int_s: 30,
        },
        &config(),
    );
    assert!(has_field(w.data(), b"553=reset-user\x01"));
    assert!(validate_checksum(w.data()).is_ok());

    // ...and does not fire for a plain Logon.
    let mut w2: MessageWriter<MockDict, ResetOnly> = MessageWriter::with_customizer(ResetOnly);
    w2.encode_admin(
        AdminMsg::Logon {
            seq: 1,
            heart_bt_int_s: 30,
        },
        &config(),
    );
    assert!(!has_field(w2.data(), b"553="));
}

// ── every arm is wired to its own hook ───────────────────────────────────────

/// `encode_admin` dispatches eight near-identical arms; the copy-paste risks are
/// an arm that forgets to call its hook and an arm wired to the *wrong* hook.
/// This customizer stamps a distinct marker from every hook, so each admin type
/// must come back carrying exactly its own — pinning the whole dispatch table.
struct MarkAll;

impl SessionCustomizer for MarkAll {
    fn configure_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"logon");
    }
    fn configure_logon_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"logon_reset");
    }
    fn configure_logout(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"logout");
    }
    fn configure_heartbeat(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"heartbeat");
    }
    fn configure_test_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"test_request");
    }
    fn configure_resend_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"resend_request");
    }
    fn configure_sequence_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"sequence_reset");
    }
    fn configure_reject(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"reject");
    }
}

#[test]
fn every_admin_type_runs_its_own_hook() {
    let cases: Vec<(AdminMsg, &[u8])> = vec![
        (
            AdminMsg::Logon {
                seq: 1,
                heart_bt_int_s: 30,
            },
            b"logon",
        ),
        (
            AdminMsg::LogonReset {
                seq: 1,
                heart_bt_int_s: 30,
            },
            b"logon_reset",
        ),
        (AdminMsg::Logout { seq: 2 }, b"logout"),
        (AdminMsg::Heartbeat { seq: 3, echo: None }, b"heartbeat"),
        (AdminMsg::TestRequest { seq: 4, id: 1 }, b"test_request"),
        (
            AdminMsg::ResendRequest { seq: 5, begin: 1 },
            b"resend_request",
        ),
        (
            AdminMsg::SequenceReset {
                seq: 6,
                new_seq: 10,
            },
            b"sequence_reset",
        ),
        (
            AdminMsg::Reject {
                seq: 7,
                ref_seq_num: 1,
                ref_tag_id: None,
                session_reject_reason: 1,
            },
            b"reject",
        ),
    ];

    for (admin, expected) in cases {
        let mut w: MessageWriter<MockDict, MarkAll> = MessageWriter::with_customizer(MarkAll);
        w.encode_admin(admin, &config());
        let data = w.data();
        let marker = tag(data, 9001).unwrap_or_else(|| {
            panic!(
                "no hook ran for this admin type: {}",
                String::from_utf8_lossy(data)
            )
        });
        assert_eq!(
            marker,
            expected,
            "admin arm ran the wrong hook: got {}, want {}",
            String::from_utf8_lossy(marker),
            String::from_utf8_lossy(expected),
        );
        assert!(validate_checksum(data).is_ok());
    }
}

// ── engine-owned tags are a programming error ────────────────────────────────

#[test]
#[should_panic(expected = "engine-owned")]
fn writing_seq_num_from_the_hook_trips_the_debug_assert() {
    struct BadAuth;
    impl SessionCustomizer for BadAuth {
        fn configure_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(34, b"99"); // the session owns 34
        }
    }

    let mut w: MessageWriter<MockDict, BadAuth> = MessageWriter::with_customizer(BadAuth);
    w.encode_admin(
        AdminMsg::Logon {
            seq: 1,
            heart_bt_int_s: 30,
        },
        &config(),
    );
}
