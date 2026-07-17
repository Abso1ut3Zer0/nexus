//! Venue auth seam: the `SessionCustomizer` hook fires after the engine stamps
//! the session header and before framing computes BodyLength/CheckSum.
//!
//! The load-bearing property is that the hook writes *inside* the frame: 9 and
//! 10 must be correct over whatever it injected, and the accessors must return
//! the values actually stamped on the wire so a venue can sign over them.
//!
//! Admin frames are produced through the typed emit path: [`Emitter`] over a
//! [`MessageWriter`], one struct per admin type implementing `AdminEncode`.

#![cfg(unix)]

use nexus_fix_codec::{
    AdminEncode, AdminMsgOut, DecodeError, FieldView, FixAdminMsg, FixDictionary, FixHeader,
    FixTimestamp, Heartbeat, Logon, LogonReset, Logout, NoCustomizer, Reject, ResendRequest,
    SequenceReset, SessionCustomizer, TEST_REQ_ID_CAP, TestRequest, find_tag, validate_checksum,
};
use nexus_fix_engine::{
    AdminSink, CompId, Emitter, FrameWriter, MessageWriter, SessionConfig, TransportError,
};

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

/// Encode one admin message into `w` through the production [`Emitter`] with a
/// no-op `after` (no journaling), then inspect `w.data()`.
fn emit_admin<M: AdminEncode, C: SessionCustomizer>(
    w: &mut MessageWriter<MockDict, C>,
    config: &SessionConfig,
    msg: M,
) -> Result<(), TransportError> {
    Emitter::new(w, config, |_seq, _frame| Ok(())).emit(msg)
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
    fn customize_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(553, b"trader-1");
        m.field(554, b"s3cret");
    }
}

/// Coinbase's shape: signs the SOH-joined stamped header into RawData(96).
struct SigningAuth;

impl SessionCustomizer for SigningAuth {
    fn customize_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
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
fn assert_matches_oracle<M: AdminEncode>(admin: M, msg_type: &[u8], body: &[(u32, Vec<u8>)]) {
    use nexus_fix_codec::FrameFormatter;

    let mut w: MessageWriter<MockDict> = MessageWriter::new();
    emit_admin(&mut w, &config(), admin).expect("oracle frame fits");
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
        Logon {
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
        LogonReset {
            seq: 1,
            heart_bt_int_s: 30,
        },
        b"A",
        &[(108, b"30".to_vec()), (141, b"Y".to_vec())],
    );
}

#[test]
fn no_customizer_logout_is_byte_identical() {
    assert_matches_oracle(Logout { seq: 2 }, b"5", &[]);
}

#[test]
fn no_customizer_heartbeat_is_byte_identical() {
    assert_matches_oracle(Heartbeat { seq: 3, echo: None }, b"0", &[]);
}

#[test]
fn no_customizer_heartbeat_with_echo_is_byte_identical() {
    // `TEST_REQ_ID_CAP` is the engine's TestReqID echo capacity; the public
    // `Heartbeat` struct names the array size structurally.
    let mut id = [0u8; TEST_REQ_ID_CAP];
    id[..4].copy_from_slice(b"TR-1");
    assert_matches_oracle(
        Heartbeat {
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
        TestRequest { seq: 4, id: 77 },
        b"1",
        &[(112, b"77".to_vec())],
    );
}

#[test]
fn no_customizer_resend_request_is_byte_identical() {
    assert_matches_oracle(
        ResendRequest { seq: 5, begin: 2 },
        b"2",
        &[(7, b"2".to_vec()), (16, b"0".to_vec())],
    );
}

#[test]
fn no_customizer_sequence_reset_is_byte_identical() {
    assert_matches_oracle(
        SequenceReset {
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
        Reject {
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

// ── the dictionary owned-lists track the encoders (the drift fix) ────────────

/// All tags in `frame`, in wire order, that are not part of the global session
/// framing set (`8`/`9`/`10`/`34`/`35`/`49`/`52`/`56`) — i.e. the body tags the
/// message's own encoder wrote.
fn scan_body_tags(frame: &[u8]) -> Vec<u32> {
    const FRAMING: &[u32] = &[8, 9, 10, 34, 35, 49, 52, 56];
    frame
        .split(|&b| b == 0x01)
        .filter(|f| !f.is_empty())
        .filter_map(|f| {
            let eq = f.iter().position(|&b| b == b'=')?;
            std::str::from_utf8(&f[..eq]).ok()?.parse::<u32>().ok()
        })
        .filter(|t| !FRAMING.contains(t))
        .collect()
}

/// The load-bearing test for the drift fix: each `FixDictionary::*_OWNED` const
/// must equal the body tags its `encode_*` actually writes. The const lives next
/// to the encoder, but nothing forces them to agree — so encode every admin type
/// with `NoCustomizer` and compare the scanned body against the const. Add a
/// field to an encoder and forget its const (or vice versa) and this reddens.
///
/// Each admin is built in the form that writes *all* its owned tags — a Heartbeat
/// with an echo so `112` lands, a Reject citing a tag so `371` lands — because
/// the tripwire is deliberately unconditional over those conditional fields.
#[test]
fn dictionary_owned_consts_match_the_encoder_bodies() {
    let mut echo = [0u8; TEST_REQ_ID_CAP];
    echo[..4].copy_from_slice(b"TR-1");

    // Each admin struct is a distinct type, so drive one assertion per type
    // rather than a heterogeneous collection.
    macro_rules! check {
        ($msg:expr, $owned:expr) => {{
            let mut w: MessageWriter<MockDict> = MessageWriter::new();
            emit_admin(&mut w, &config(), $msg).expect("admin fits");
            let scanned = scan_body_tags(w.data());
            assert_eq!(
                scanned,
                $owned,
                "body tags {} wrote disagree with its *_OWNED const: an encoder field \
                 was added or removed without updating the const (or vice versa)",
                stringify!($msg),
            );
        }};
    }

    check!(
        Logon {
            seq: 1,
            heart_bt_int_s: 30
        },
        MockDict::LOGON_OWNED
    );
    check!(
        LogonReset {
            seq: 1,
            heart_bt_int_s: 30
        },
        MockDict::LOGON_RESET_OWNED
    );
    check!(Logout { seq: 2 }, MockDict::LOGOUT_OWNED);
    check!(
        Heartbeat {
            seq: 3,
            echo: Some((echo, 4))
        },
        MockDict::HEARTBEAT_OWNED
    );
    check!(TestRequest { seq: 4, id: 1 }, MockDict::TEST_REQUEST_OWNED);
    check!(
        ResendRequest { seq: 5, begin: 2 },
        MockDict::RESEND_REQUEST_OWNED
    );
    check!(
        SequenceReset {
            seq: 6,
            new_seq: 10
        },
        MockDict::SEQUENCE_RESET_OWNED
    );
    check!(
        Reject {
            seq: 7,
            ref_seq_num: 3,
            ref_tag_id: Some(35),
            session_reject_reason: 1
        },
        MockDict::REJECT_OWNED
    );
}

// ── the seam's guarantee: 9 and 10 cover the injected fields ─────────────────

#[test]
fn injected_fields_are_on_the_wire() {
    let mut w: MessageWriter<MockDict, TestAuth> = MessageWriter::with_customizer(TestAuth);
    emit_admin(
        &mut w,
        &config(),
        Logon {
            seq: 1,
            heart_bt_int_s: 30,
        },
    )
    .expect("logon fits");
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
    emit_admin(
        &mut w,
        &config(),
        Logon {
            seq: 1,
            heart_bt_int_s: 30,
        },
    )
    .expect("logon fits");
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
    emit_admin(
        &mut w,
        &config(),
        Logon {
            seq: 7,
            heart_bt_int_s: 30,
        },
    )
    .expect("logon fits");
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
/// per-message defaulted no-ops, a `customize_logon`-only customizer cannot.
#[test]
fn logon_only_customizer_leaves_other_admin_messages_untouched() {
    macro_rules! check_untouched {
        ($msg:expr) => {{
            let mut w: MessageWriter<MockDict, TestAuth> = MessageWriter::with_customizer(TestAuth);
            emit_admin(&mut w, &config(), $msg).expect("admin fits");
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
        }};
    }

    check_untouched!(Logout { seq: 2 });
    check_untouched!(Heartbeat { seq: 3, echo: None });
    check_untouched!(TestRequest { seq: 4, id: 1 });
    check_untouched!(ResendRequest { seq: 5, begin: 1 });
    check_untouched!(SequenceReset {
        seq: 6,
        new_seq: 10
    });
    check_untouched!(Reject {
        seq: 7,
        ref_seq_num: 1,
        ref_tag_id: None,
        session_reject_reason: 1
    });
}

/// A `customize_logon`-only customizer must produce byte-identical Heartbeats to
/// the `NoCustomizer` path — the defaulted no-op adds nothing at all.
#[test]
fn logon_only_customizer_heartbeat_matches_no_customizer() {
    let mut plain: MessageWriter<MockDict, NoCustomizer> =
        MessageWriter::with_customizer(NoCustomizer);
    emit_admin(&mut plain, &config(), Heartbeat { seq: 3, echo: None }).expect("heartbeat fits");
    let plain_body = tag(plain.data(), 9).map(|_| plain.data().len());

    let mut authed: MessageWriter<MockDict, TestAuth> = MessageWriter::with_customizer(TestAuth);
    emit_admin(&mut authed, &config(), Heartbeat { seq: 3, echo: None }).expect("heartbeat fits");

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
        fn customize_logon_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(553, b"reset-user");
        }
    }

    let mut w: MessageWriter<MockDict, ResetOnly> = MessageWriter::with_customizer(ResetOnly);
    emit_admin(
        &mut w,
        &config(),
        LogonReset {
            seq: 1,
            heart_bt_int_s: 30,
        },
    )
    .expect("logon reset fits");
    assert!(has_field(w.data(), b"553=reset-user\x01"));
    assert!(validate_checksum(w.data()).is_ok());

    // ...and does not fire for a plain Logon.
    let mut w2: MessageWriter<MockDict, ResetOnly> = MessageWriter::with_customizer(ResetOnly);
    emit_admin(
        &mut w2,
        &config(),
        Logon {
            seq: 1,
            heart_bt_int_s: 30,
        },
    )
    .expect("logon fits");
    assert!(!has_field(w2.data(), b"553="));
}

// ── every arm is wired to its own hook ───────────────────────────────────────

/// The typed emit path forwards each admin struct to *its* `customize_*` hook;
/// the copy-paste risks are a struct that forgets to call its hook and one wired
/// to the *wrong* hook. This customizer stamps a distinct marker from every
/// hook, so each admin type must come back carrying exactly its own — pinning
/// the whole dispatch table.
struct MarkAll;

impl SessionCustomizer for MarkAll {
    fn customize_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"logon");
    }
    fn customize_logon_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"logon_reset");
    }
    fn customize_logout(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"logout");
    }
    fn customize_heartbeat(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"heartbeat");
    }
    fn customize_test_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"test_request");
    }
    fn customize_resend_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"resend_request");
    }
    fn customize_sequence_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"sequence_reset");
    }
    fn customize_reject(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(9001, b"reject");
    }
}

#[test]
fn every_admin_type_runs_its_own_hook() {
    macro_rules! check_hook {
        ($msg:expr, $expected:expr) => {{
            let mut w: MessageWriter<MockDict, MarkAll> = MessageWriter::with_customizer(MarkAll);
            emit_admin(&mut w, &config(), $msg).expect("admin fits");
            let data = w.data();
            let marker = tag(data, 9001).unwrap_or_else(|| {
                panic!(
                    "no hook ran for this admin type: {}",
                    String::from_utf8_lossy(data)
                )
            });
            assert_eq!(
                marker,
                $expected,
                "admin arm ran the wrong hook: got {}, want {}",
                String::from_utf8_lossy(marker),
                String::from_utf8_lossy($expected),
            );
            assert!(validate_checksum(data).is_ok());
        }};
    }

    check_hook!(
        Logon {
            seq: 1,
            heart_bt_int_s: 30
        },
        b"logon"
    );
    check_hook!(
        LogonReset {
            seq: 1,
            heart_bt_int_s: 30
        },
        b"logon_reset"
    );
    check_hook!(Logout { seq: 2 }, b"logout");
    check_hook!(Heartbeat { seq: 3, echo: None }, b"heartbeat");
    check_hook!(TestRequest { seq: 4, id: 1 }, b"test_request");
    check_hook!(ResendRequest { seq: 5, begin: 1 }, b"resend_request");
    check_hook!(
        SequenceReset {
            seq: 6,
            new_seq: 10
        },
        b"sequence_reset"
    );
    check_hook!(
        Reject {
            seq: 7,
            ref_seq_num: 1,
            ref_tag_id: None,
            session_reject_reason: 1
        },
        b"reject"
    );
}

// ── the accessor's MsgType is the wire's MsgType ─────────────────────────────

/// Echoes `msg_type()` — what a venue signs over — into a body tag, so the test
/// can compare it against the frame's own `35`.
struct EchoMsgType;

impl SessionCustomizer for EchoMsgType {
    fn customize_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
        let mt = m.msg_type().to_vec();
        m.field(9002, &mt);
    }
    fn customize_logon_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        let mt = m.msg_type().to_vec();
        m.field(9002, &mt);
    }
    fn customize_logout(&self, m: &mut AdminMsgOut<'_, '_>) {
        let mt = m.msg_type().to_vec();
        m.field(9002, &mt);
    }
    fn customize_heartbeat(&self, m: &mut AdminMsgOut<'_, '_>) {
        let mt = m.msg_type().to_vec();
        m.field(9002, &mt);
    }
    fn customize_test_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        let mt = m.msg_type().to_vec();
        m.field(9002, &mt);
    }
    fn customize_resend_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        let mt = m.msg_type().to_vec();
        m.field(9002, &mt);
    }
    fn customize_sequence_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        let mt = m.msg_type().to_vec();
        m.field(9002, &mt);
    }
    fn customize_reject(&self, m: &mut AdminMsgOut<'_, '_>) {
        let mt = m.msg_type().to_vec();
        m.field(9002, &mt);
    }
}

/// A venue signs over `msg_type()`. If it disagreed with the frame's `35`, the
/// bytes on the wire would look perfect and the venue would reject the signature
/// with an opaque auth error — so pin the correspondence on every arm.
#[test]
fn accessor_msg_type_matches_the_frames_own_tag_35() {
    macro_rules! check_mt {
        ($msg:expr, $expected:expr) => {{
            let mut w: MessageWriter<MockDict, EchoMsgType> =
                MessageWriter::with_customizer(EchoMsgType);
            emit_admin(&mut w, &config(), $msg).expect("admin fits");
            let data = w.data();

            let wire = tag(data, 35).expect("35 on the wire");
            let seen = tag(data, 9002).expect("hook echoed msg_type()");

            // Pinned against a literal too: if both drifted together the wire tag
            // would still be wrong, and this catches that.
            assert_eq!(wire, $expected, "wrong MsgType on the wire");
            assert_eq!(
                seen,
                wire,
                "msg_type() ({}) disagrees with the frame's 35 ({}) — a venue would sign the wrong MsgType",
                String::from_utf8_lossy(seen),
                String::from_utf8_lossy(wire),
            );
        }};
    }

    check_mt!(
        Logon {
            seq: 1,
            heart_bt_int_s: 30
        },
        b"A"
    );
    check_mt!(
        LogonReset {
            seq: 1,
            heart_bt_int_s: 30
        },
        b"A"
    );
    check_mt!(Logout { seq: 2 }, b"5");
    check_mt!(Heartbeat { seq: 3, echo: None }, b"0");
    check_mt!(TestRequest { seq: 4, id: 1 }, b"1");
    check_mt!(ResendRequest { seq: 5, begin: 1 }, b"2");
    check_mt!(
        SequenceReset {
            seq: 6,
            new_seq: 10
        },
        b"4"
    );
    check_mt!(
        Reject {
            seq: 7,
            ref_seq_num: 1,
            ref_tag_id: None,
            session_reject_reason: 1
        },
        b"3"
    );
}

// ── engine-owned tags are a programming error ────────────────────────────────

/// The tripwire is a `debug_assert!`: it exists only in debug builds, so these
/// `#[should_panic]` tests must not run under `cargo test --release` — no panic
/// fires there and the test would fail for a reason unrelated to the code.
#[cfg(debug_assertions)]
mod engine_owned_tripwire {
    use std::panic::UnwindSafe;

    use super::*;

    /// Writes `tag` from every hook, so any admin type drives the same probe.
    struct WritesTag(u32);
    impl SessionCustomizer for WritesTag {
        fn customize_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(self.0, b"x");
        }
        fn customize_logon_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(self.0, b"x");
        }
        fn customize_logout(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(self.0, b"x");
        }
        fn customize_heartbeat(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(self.0, b"x");
        }
        fn customize_test_request(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(self.0, b"x");
        }
        fn customize_resend_request(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(self.0, b"x");
        }
        fn customize_sequence_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(self.0, b"x");
        }
        fn customize_reject(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(self.0, b"x");
        }
    }

    fn encode_writing<M: AdminEncode>(admin: M, tag: u32) {
        let inner = FrameWriter::builder().build();
        let mut w: MessageWriter<MockDict, WritesTag> =
            MessageWriter::with_frame_writer_and_customizer(inner, WritesTag(tag));
        emit_admin(&mut w, &config(), admin).expect("admin fits");
    }

    fn encode_logon_writing(tag: u32) {
        encode_writing(
            Logon {
                seq: 1,
                heart_bt_int_s: 30,
            },
            tag,
        );
    }

    /// Runs the hook for `admin` writing `tag`, returning the panic message if
    /// the tripwire fired. The panic hook is muted for the duration so an
    /// expected trip does not spray a backtrace across passing test output.
    fn catch_hook_panic<M: AdminEncode + UnwindSafe>(admin: M, tag: u32) -> Option<String> {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let result = std::panic::catch_unwind(move || encode_writing(admin, tag));
        std::panic::set_hook(prev);

        result.err().map(|e| {
            e.downcast_ref::<&str>()
                .map(|s| (*s).to_string())
                .or_else(|| e.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| String::from("<non-string panic payload>"))
        })
    }

    #[test]
    #[should_panic(expected = "engine-owned")]
    fn writing_seq_num_from_the_hook_trips_the_debug_assert() {
        encode_logon_writing(34); // the session owns 34 on every message
    }

    #[test]
    #[should_panic(expected = "engine-owned")]
    fn writing_the_logons_own_heart_bt_int_trips_the_debug_assert() {
        encode_logon_writing(108); // encode_logon already wrote 108
    }

    /// Each admin type's own engine params trip the tripwire *through the emit
    /// path*, exactly as a real customizer would hit them. One test per case
    /// would be many near-identical `#[should_panic]` fns; instead each case runs
    /// in a child thread and we assert the panic message.
    #[test]
    fn every_admin_types_own_engine_params_are_rejected() {
        macro_rules! reject {
            ($msg:expr, $tag:expr) => {{
                let panic = catch_hook_panic($msg, $tag);
                let msg = panic.unwrap_or_else(|| {
                    panic!(
                        "writing engine-owned tag {} on {} did not trip the tripwire",
                        $tag,
                        stringify!($msg)
                    )
                });
                assert!(
                    msg.contains("engine-owned"),
                    "unexpected panic for tag {} on {}: {}",
                    $tag,
                    stringify!($msg),
                    msg
                );
            }};
        }

        reject!(
            Logon {
                seq: 1,
                heart_bt_int_s: 30
            },
            108
        );
        reject!(
            LogonReset {
                seq: 1,
                heart_bt_int_s: 30
            },
            108
        );
        reject!(
            LogonReset {
                seq: 1,
                heart_bt_int_s: 30
            },
            141
        );
        reject!(Heartbeat { seq: 3, echo: None }, 112);
        reject!(TestRequest { seq: 4, id: 1 }, 112);
        reject!(ResendRequest { seq: 5, begin: 1 }, 7);
        reject!(ResendRequest { seq: 5, begin: 1 }, 16);
        reject!(
            SequenceReset {
                seq: 6,
                new_seq: 10
            },
            43
        );
        reject!(
            SequenceReset {
                seq: 6,
                new_seq: 10
            },
            123
        );
        reject!(
            SequenceReset {
                seq: 6,
                new_seq: 10
            },
            36
        );
        reject!(
            Reject {
                seq: 7,
                ref_seq_num: 1,
                ref_tag_id: Some(35),
                session_reject_reason: 1
            },
            45
        );
        reject!(
            Reject {
                seq: 7,
                ref_seq_num: 1,
                ref_tag_id: Some(35),
                session_reject_reason: 1
            },
            371
        );
        reject!(
            Reject {
                seq: 7,
                ref_seq_num: 1,
                ref_tag_id: Some(35),
                session_reject_reason: 1
            },
            373
        );
    }

    /// A tag that is engine-owned on a *different* message is the venue's to
    /// write here — the asymmetry that makes the check worth doing per message.
    #[test]
    fn tags_owned_by_another_message_are_allowed() {
        // 108 is engine-owned on Logon; encode_heartbeat never writes it.
        assert_eq!(
            catch_hook_panic(Heartbeat { seq: 3, echo: None }, 108),
            None,
            "108 must be writable on a Heartbeat"
        );
        // 141 is engine-owned on LogonReset; encode_logon never writes it.
        assert_eq!(
            catch_hook_panic(
                Logon {
                    seq: 1,
                    heart_bt_int_s: 30,
                },
                141,
            ),
            None,
            "141 must be writable on a plain Logon"
        );
        // Logout's encoder writes nothing beyond the header.
        assert_eq!(
            catch_hook_panic(Logout { seq: 2 }, 108),
            None,
            "108 must be writable on a Logout"
        );
    }
}

// ── overflow: a hook that doesn't fit errors, never silently drops ────────────
//
// The seam hands the outbound buffer to user code. A hook writing an oversized
// field (an over-long RawData/passphrase, or any caller with a small writer)
// poisons the frame; `finish` then returns `BufferFull`. The emit path surfaces
// that as `Err(MessageTooLarge)` with nothing committed — never a silent drop
// that would leave the outbound seqnum bumped and the session wedged.

/// Writes a `pad`-byte body field (tag 5000, never engine-owned) from *every*
/// admin hook, so any admin type can be driven up to and past a writer's
/// capacity.
struct Padding(usize);

impl Padding {
    fn pad(&self, m: &mut AdminMsgOut<'_, '_>) {
        m.field(5000, &vec![b'x'; self.0]);
    }
}

impl SessionCustomizer for Padding {
    fn customize_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
        self.pad(m);
    }
    fn customize_logon_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        self.pad(m);
    }
    fn customize_logout(&self, m: &mut AdminMsgOut<'_, '_>) {
        self.pad(m);
    }
    fn customize_heartbeat(&self, m: &mut AdminMsgOut<'_, '_>) {
        self.pad(m);
    }
    fn customize_test_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        self.pad(m);
    }
    fn customize_resend_request(&self, m: &mut AdminMsgOut<'_, '_>) {
        self.pad(m);
    }
    fn customize_sequence_reset(&self, m: &mut AdminMsgOut<'_, '_>) {
        self.pad(m);
    }
    fn customize_reject(&self, m: &mut AdminMsgOut<'_, '_>) {
        self.pad(m);
    }
}

/// Encode `admin` with a `cap`-byte writer and a hook padding `pad` bytes.
fn encode_padded<M: AdminEncode>(admin: M, cap: usize, pad: usize) -> Result<(), TransportError> {
    let inner = FrameWriter::builder().buffer_capacity(cap).build();
    let mut w: MessageWriter<MockDict, Padding> =
        MessageWriter::with_frame_writer_and_customizer(inner, Padding(pad));
    emit_admin(&mut w, &config(), admin)
}

#[test]
fn oversized_hook_field_errors_instead_of_silent_drop() {
    // Both admin types comfortably fit the 512-byte writer *without* the hook;
    // the 1000-byte padding is what overflows, so the failure is unambiguously
    // the hook's, not an undersized base frame.
    macro_rules! overflow_case {
        ($msg:expr, $name:expr) => {{
            let inner = FrameWriter::builder().buffer_capacity(512).build();
            let mut w: MessageWriter<MockDict, Padding> =
                MessageWriter::with_frame_writer_and_customizer(inner, Padding(1000));
            let r = emit_admin(&mut w, &config(), $msg);
            assert!(
                matches!(r, Err(TransportError::MessageTooLarge(_))),
                "{}: an oversized hook must return MessageTooLarge, got {:?}",
                $name,
                r
            );
            // Nothing was committed — a failed encode leaves no bytes to send.
            assert!(
                w.is_empty(),
                "{}: a failed encode must leave the outbound buffer empty",
                $name
            );
            assert!(
                w.data().is_empty(),
                "{}: a failed encode must not expose a partial frame",
                $name
            );
        }};
    }

    overflow_case!(
        Logon {
            seq: 1,
            heart_bt_int_s: 30
        },
        "logon"
    );
    overflow_case!(Logout { seq: 2 }, "logout");
}

#[test]
fn hook_field_overflow_boundary_is_exact() {
    // At a fixed capacity, find the largest padding that still fits, then prove
    // the transition is a true off-by-one: `fits` succeeds, `fits + 1` errors.
    const CAP: usize = 256;
    let admin = || Logon {
        seq: 1,
        heart_bt_int_s: 30,
    };

    // Padding past CAP cannot fit, so CAP bounds the scan — a hard cap so a
    // regression that stopped failing errors here instead of looping forever.
    let mut fits = 0usize;
    while fits < CAP && encode_padded(admin(), CAP, fits + 1).is_ok() {
        fits += 1;
    }

    assert!(
        fits > 0,
        "the base Logon should fit CAP with room for some padding"
    );
    assert!(
        fits < CAP,
        "padding must overflow within CAP bytes; the boundary scan never found a \
         failing size (did encode stop reporting overflow?)"
    );
    assert!(
        encode_padded(admin(), CAP, fits).is_ok(),
        "a body that exactly fits must succeed (pad={fits})"
    );
    assert!(
        matches!(
            encode_padded(admin(), CAP, fits + 1),
            Err(TransportError::MessageTooLarge(_))
        ),
        "one byte past the exact fit must error (pad={})",
        fits + 1
    );
}

/// A failed encode after a good one must leave the good frame byte-identical and
/// append nothing — the poisoned frame lives in the writer's spare region but is
/// never committed, so it can never reach the wire.
#[test]
fn failed_encode_leaves_prior_frame_intact_and_adds_nothing() {
    /// Pads only Logon; every other admin type is a no-op.
    struct PadLogonOnly(usize);
    impl SessionCustomizer for PadLogonOnly {
        fn customize_logon(&self, m: &mut AdminMsgOut<'_, '_>) {
            m.field(5000, &vec![b'x'; self.0]);
        }
    }

    let inner = FrameWriter::builder().buffer_capacity(256).build();
    let mut w: MessageWriter<MockDict, PadLogonOnly> =
        MessageWriter::with_frame_writer_and_customizer(inner, PadLogonOnly(1000));

    // A Heartbeat (no padding) fits and commits.
    emit_admin(&mut w, &config(), Heartbeat { seq: 3, echo: None }).expect("heartbeat fits");
    let after_good = w.data().to_vec();
    assert!(!after_good.is_empty());
    assert!(validate_checksum(&after_good).is_ok());

    // An oversized Logon into the same writer must fail...
    let r = emit_admin(
        &mut w,
        &config(),
        Logon {
            seq: 4,
            heart_bt_int_s: 30,
        },
    );
    assert!(
        matches!(r, Err(TransportError::MessageTooLarge(_))),
        "oversized Logon must error, got {r:?}"
    );

    // ...and leave the buffer byte-identical: no half-written Logon appended.
    assert_eq!(
        w.data(),
        after_good.as_slice(),
        "a failed encode must not append partial bytes to committed output"
    );
}
