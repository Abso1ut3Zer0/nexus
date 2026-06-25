use nexus_fix_codegen_tests::{venue_alpha, venue_beta};

#[test]
fn alpha_decodes_scalar_fields_and_enum() {
    let msg = b"11=ORD123\x0154=1\x0155=BTC-USD\x0138=10\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(m.cl_ord_id().unwrap().as_bytes(), &b"ORD123"[..]);
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"BTC-USD"[..]);
    assert_eq!(
        m.order_qty().unwrap().get(),
        nexus_fix_codec::FixDecimal::new(10, 0,).unwrap()
    );
    assert_eq!(m.side(), Some(venue_alpha::fields::Side::BUY));
}

#[test]
fn alpha_typed_text_accessor() {
    let msg = b"11=ORD123\x0155=BTC-USD\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    let text = m.cl_ord_id().unwrap().get();
    assert_eq!(text.as_bytes(), b"ORD123");
    let sym = m.symbol().unwrap().get();
    assert_eq!(sym.as_bytes(), b"BTC-USD");
}

#[test]
fn alpha_absent_field_is_none() {
    let msg = b"11=ORD123\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert!(m.symbol().is_none());
    assert!(m.side().is_none());
}

#[test]
fn alpha_unknown_enum_value_is_preserved() {
    let msg = b"11=A\x0154=9\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(m.side(), Some(venue_alpha::fields::Side::Unknown(b'9')));
}

#[test]
fn alpha_is_complete() {
    let full = b"11=A\x0154=1\x0155=X\x01";
    assert!(
        venue_alpha::messages::NewOrderSingle::decode(full)
            .unwrap()
            .is_complete()
    );
    let missing_symbol = b"11=A\x0154=1\x01";
    assert!(
        !venue_alpha::messages::NewOrderSingle::decode(missing_symbol)
            .unwrap()
            .is_complete()
    );
}

#[test]
fn alpha_decodes_data_field_with_embedded_soh() {
    let msg = b"11=A\x0195=3\x0196=a\x01b\x0155=X\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(m.raw_data_length().unwrap().get(), 3);
    assert_eq!(m.raw_data().unwrap().as_bytes(), &b"a\x01b"[..]);
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"X"[..]);
}

#[test]
fn alpha_truncated_data_errors() {
    let msg = b"11=A\x0195=100\x0196=ab\x01";
    assert!(matches!(
        venue_alpha::messages::NewOrderSingle::decode(msg),
        Err(nexus_fix_codec::DecodeError::Truncated)
    ));
}

#[test]
fn alpha_decodes_repeating_group() {
    let msg = b"11=A\x01453=2\x01448=PARTY1\x01452=1\x01448=PARTY2\x01452=2\x0155=X\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    let parties: Vec<_> = m.no_party_i_ds().collect();
    assert_eq!(parties.len(), 2);
    assert_eq!(parties[0].party_id().unwrap().as_bytes(), &b"PARTY1"[..]);
    assert_eq!(parties[1].party_id().unwrap().as_bytes(), &b"PARTY2"[..]);
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"X"[..]);
}

#[test]
fn alpha_decodes_nested_group() {
    let msg = b"11=A\x01453=1\x01448=P1\x01452=1\x01802=2\x01523=S1\x01803=1\x01523=S2\x01803=2\x0155=X\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    let parties: Vec<_> = m.no_party_i_ds().collect();
    assert_eq!(parties.len(), 1);
    assert_eq!(parties[0].party_id().unwrap().as_bytes(), &b"P1"[..]);
    let subs: Vec<_> = parties[0].no_party_sub_i_ds().collect();
    assert_eq!(subs.len(), 2);
    assert_eq!(subs[0].party_sub_id().unwrap().as_bytes(), &b"S1"[..]);
    assert_eq!(subs[1].party_sub_id().unwrap().as_bytes(), &b"S2"[..]);
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"X"[..]);
}

#[test]
fn alpha_decodes_execution_report() {
    let msg = b"37=ORD1\x0117=EX1\x01150=0\x0139=2\x0155=BTC-USD\x0154=1\x0132=5\x0131=100.50\x01";
    let m = venue_alpha::messages::ExecutionReport::decode(msg).unwrap();
    assert_eq!(m.order_id().unwrap().as_bytes(), &b"ORD1"[..]);
    assert_eq!(m.exec_id().unwrap().as_bytes(), &b"EX1"[..]);
    assert_eq!(m.exec_type(), Some(venue_alpha::fields::ExecType::NEW));
    assert_eq!(m.ord_status(), Some(venue_alpha::fields::OrdStatus::FILLED));
    assert_eq!(
        m.last_qty().unwrap().get(),
        nexus_fix_codec::FixDecimal::new(5, 0,).unwrap()
    );
    assert_eq!(
        m.last_px().unwrap().get(),
        nexus_fix_codec::FixDecimal::new(10050, 2,).unwrap()
    );
}

#[test]
fn alpha_msgtype_dispatch() {
    use venue_alpha::MsgType;
    assert_eq!(MsgType::from_bytes(b"D"), Some(MsgType::NewOrderSingle));
    assert_eq!(MsgType::from_bytes(b"8"), Some(MsgType::ExecutionReport));
    assert_eq!(MsgType::from_bytes(b"0"), Some(MsgType::Heartbeat));
    assert_eq!(MsgType::ExecutionReport.as_bytes(), b"8");
    assert_eq!(MsgType::from_bytes(b"ZZ"), None);
}

fn sending_time() -> nexus_fix_codec::FixTimestamp {
    nexus_fix_codec::FixTimestamp::parse(b"20260603-12:00:00").unwrap()
}

#[test]
fn alpha_encodes_round_trip() {
    let mut buf = [0u8; 256];
    let (start, len) = venue_alpha::encoders::NewOrderSingleEncoder::wrap(&mut buf)
        .header_encoder()
        .sender_comp_id(b"BUYSIDE")
        .target_comp_id(b"SELLSIDE")
        .msg_seq_num(7)
        .sending_time(sending_time()) // skips the optional PossDupFlag
        .finish()
        .cl_ord_id(b"ORD1")
        .side(venue_alpha::fields::Side::SELL)
        .symbol(b"ETH-USD")
        .finish()
        .unwrap();
    let msg = &buf[start..start + len];

    // A complete, valid FIX message — header, body, framing, checksum.
    assert!(msg.starts_with(b"8=FIX.4.4\x019="));
    assert!(nexus_fix_codec::validate_checksum(msg).is_ok());

    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(
        m.header().sender_comp_id().unwrap().get().as_bytes(),
        b"BUYSIDE"
    );
    assert_eq!(m.header().msg_seq_num().unwrap().get(), 7);
    assert!(m.header().poss_dup_flag().is_none());
    assert_eq!(m.cl_ord_id().unwrap().as_bytes(), &b"ORD1"[..]);
    assert_eq!(m.side(), Some(venue_alpha::fields::Side::SELL));
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"ETH-USD"[..]);
    assert!(m.is_complete());
}

#[test]
fn alpha_encodes_typed_decimal_and_optional_header() {
    let qty = nexus_fix_codec::FixDecimal::new(1050, 1).unwrap();
    let mut buf = [0u8; 256];
    let (start, len) = venue_alpha::encoders::NewOrderSingleEncoder::wrap(&mut buf)
        .header_encoder()
        .sender_comp_id(b"S")
        .target_comp_id(b"T")
        .msg_seq_num(99)
        .poss_dup_flag(true) // optional header field, set in order
        .sending_time(sending_time())
        .finish()
        .cl_ord_id(b"X")
        .side(venue_alpha::fields::Side::BUY)
        .symbol(b"BTC-USD")
        .order_qty(qty) // typed FixDecimal in, encoded for us
        .finish()
        .unwrap();
    let msg = &buf[start..start + len];

    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert!(m.header().poss_dup_flag().unwrap().get());
    assert_eq!(m.order_qty().unwrap().get(), qty);
}

#[test]
fn alpha_encodes_data_field() {
    let mut buf = [0u8; 128];
    let (start, len) = venue_alpha::encoders::NewOrderSingleEncoder::wrap(&mut buf)
        .header_encoder()
        .sender_comp_id(b"S")
        .target_comp_id(b"T")
        .msg_seq_num(1)
        .sending_time(sending_time())
        .finish()
        .cl_ord_id(b"A")
        .raw_data(b"x\x01y")
        .finish()
        .unwrap();
    let msg = &buf[start..start + len];
    assert!(nexus_fix_codec::validate_checksum(msg).is_ok());
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(m.raw_data_length().unwrap().get(), 3);
    assert_eq!(m.raw_data().unwrap().as_bytes(), &b"x\x01y"[..]);
}

#[test]
fn beta_decodes_market_data_group() {
    let msg = b"55=EUR/USD\x01268=2\x01269=0\x01270=1.1050\x01271=1000000\x01269=1\x01270=1.1052\x01271=2000000\x01";
    let m = venue_beta::messages::MarketDataSnapshotFullRefresh::decode(msg).unwrap();
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"EUR/USD"[..]);
    let entries: Vec<_> = m.no_md_entries().collect();
    assert_eq!(entries.len(), 2);
    assert_eq!(
        entries[0].md_entry_type(),
        Some(venue_beta::fields::MDEntryType::BID)
    );
    assert_eq!(
        entries[0].md_entry_px().unwrap().get(),
        nexus_fix_codec::FixDecimal::new(11050, 4,).unwrap()
    );
    assert_eq!(
        entries[1].md_entry_type(),
        Some(venue_beta::fields::MDEntryType::OFFER)
    );
    assert_eq!(
        entries[1].md_entry_size().unwrap().get(),
        nexus_fix_codec::FixDecimal::new(2_000_000, 0,).unwrap()
    );
}

#[test]
fn beta_msgtype_dispatch() {
    use venue_beta::MsgType;
    assert_eq!(
        MsgType::from_bytes(b"W"),
        Some(MsgType::MarketDataSnapshotFullRefresh)
    );
    assert_eq!(MsgType::from_bytes(b"A"), Some(MsgType::Logon));
    assert_eq!(MsgType::from_bytes(b"D"), None);
}

#[test]
fn alpha_header_decode_and_wrap() {
    let msg = b"8=FIX.4.4\x019=50\x0135=D\x0149=SENDER\x0156=TARGET\x0134=1\x0152=20260603-12:00:00\x0111=ORD1\x0154=1\x0155=BTC\x01";
    let header = venue_alpha::header::HeaderDecoder::decode(msg);
    assert_eq!(header.begin_string().unwrap().as_bytes(), &b"FIX.4.4"[..]);
    assert_eq!(header.msg_type().unwrap().as_bytes(), &b"D"[..]);
    assert_eq!(
        venue_alpha::MsgType::from_bytes(header.msg_type().unwrap().as_bytes()),
        Some(venue_alpha::MsgType::NewOrderSingle)
    );
    assert_eq!(header.msg_seq_num().unwrap().get(), 1);
    let m = venue_alpha::messages::NewOrderSingle::wrap(header).unwrap();
    assert_eq!(m.cl_ord_id().unwrap().as_bytes(), &b"ORD1"[..]);
    assert_eq!(m.side(), Some(venue_alpha::fields::Side::BUY));
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"BTC"[..]);
    assert_eq!(
        m.header().begin_string().unwrap().as_bytes(),
        &b"FIX.4.4"[..]
    );
}

#[test]
fn alpha_header_fields_absent() {
    let msg = b"11=ORD1\x0155=X\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert!(m.header().begin_string().is_none());
    assert!(m.header().msg_type().is_none());
    assert_eq!(m.cl_ord_id().unwrap().as_bytes(), &b"ORD1"[..]);
}

#[test]
fn alpha_header_all_typed_accessors() {
    let msg = b"8=FIX.4.4\x019=99\x0135=D\x0134=42\x0149=SENDER1\x0156=TARGET1\x0143=Y\x0152=20260603-14:30:00.123\x0111=X\x01";
    let header = venue_alpha::header::HeaderDecoder::decode(msg);
    assert_eq!(header.begin_string().unwrap().as_bytes(), &b"FIX.4.4"[..]);
    assert_eq!(header.body_length().unwrap().get(), 99);
    assert_eq!(header.body_length().unwrap().as_bytes(), &b"99"[..]);
    assert_eq!(header.msg_type().unwrap().as_bytes(), &b"D"[..]);
    assert_eq!(header.msg_seq_num().unwrap().get(), 42);
    assert_eq!(header.msg_seq_num().unwrap().as_bytes(), &b"42"[..]);
    let sender = header.sender_comp_id().unwrap().get();
    assert_eq!(sender.as_bytes(), b"SENDER1");
    assert_eq!(header.sender_comp_id().unwrap().as_bytes(), &b"SENDER1"[..]);
    let target = header.target_comp_id().unwrap().get();
    assert_eq!(target.as_bytes(), b"TARGET1");
    assert_eq!(header.target_comp_id().unwrap().as_bytes(), &b"TARGET1"[..]);
    assert!(header.poss_dup_flag().unwrap().get());
    assert_eq!(header.poss_dup_flag().unwrap().as_bytes(), &b"Y"[..]);
    assert!(header.sending_time().is_some_and(|f| f.is_valid()));
    assert_eq!(
        header.sending_time().unwrap().as_bytes(),
        &b"20260603-14:30:00.123"[..]
    );
}

#[test]
fn alpha_header_poss_dup_false() {
    let msg = b"8=FIX.4.4\x0135=D\x0143=N\x0111=X\x01";
    let header = venue_alpha::header::HeaderDecoder::decode(msg);
    assert!(!header.poss_dup_flag().unwrap().get());
}

#[test]
fn alpha_header_partial_fields() {
    let msg = b"8=FIX.4.4\x0135=D\x0111=X\x01";
    let header = venue_alpha::header::HeaderDecoder::decode(msg);
    assert_eq!(header.begin_string().unwrap().as_bytes(), &b"FIX.4.4"[..]);
    assert_eq!(header.msg_type().unwrap().as_bytes(), &b"D"[..]);
    assert!(header.body_length().is_none());
    assert!(header.msg_seq_num().is_none());
    assert!(header.sender_comp_id().is_none());
    assert!(header.target_comp_id().is_none());
    assert!(header.poss_dup_flag().is_none());
    assert!(header.sending_time().is_none());
}

#[test]
fn alpha_header_overflow_preserves_first_body_field() {
    let msg = b"8=FIX.4.4\x0135=D\x0111=FIRST\x0155=SYM\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(
        m.header().begin_string().unwrap().as_bytes(),
        &b"FIX.4.4"[..]
    );
    assert_eq!(m.cl_ord_id().unwrap().as_bytes(), &b"FIRST"[..]);
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"SYM"[..]);
}

#[test]
fn alpha_heartbeat_decode() {
    let msg = b"8=FIX.4.4\x0135=0\x01112=TEST123\x01";
    let m = venue_alpha::messages::Heartbeat::decode(msg).unwrap();
    assert_eq!(
        venue_alpha::MsgType::from_bytes(m.header().msg_type().unwrap().as_bytes()),
        Some(venue_alpha::MsgType::Heartbeat)
    );
    let req_id = m.test_req_id().unwrap().get();
    assert_eq!(req_id.as_bytes(), b"TEST123");
    assert_eq!(m.test_req_id().unwrap().as_bytes(), &b"TEST123"[..]);
    assert!(m.is_complete());
}

#[test]
fn alpha_heartbeat_no_test_req_id() {
    let msg = b"8=FIX.4.4\x0135=0\x01";
    let m = venue_alpha::messages::Heartbeat::decode(msg).unwrap();
    assert!(m.test_req_id().is_none());
    assert!(m.is_complete());
}

#[test]
fn alpha_raw_matches_typed_for_qty() {
    let msg = b"11=A\x0138=12345.67\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(m.order_qty().unwrap().as_bytes(), &b"12345.67"[..]);
    assert_eq!(
        m.order_qty().unwrap().get(),
        nexus_fix_codec::FixDecimal::new(1_234_567, 2,).unwrap()
    );
}

#[test]
fn alpha_group_entry_typed_accessor() {
    let msg = b"11=A\x01453=1\x01448=PARTY1\x01452=13\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    let parties: Vec<_> = m.no_party_i_ds().collect();
    assert_eq!(parties.len(), 1);
    let id = parties[0].party_id().unwrap().get();
    assert_eq!(id.as_bytes(), b"PARTY1");
    assert_eq!(parties[0].party_role().unwrap().get(), 13);
    assert_eq!(parties[0].party_role().unwrap().as_bytes(), &b"13"[..]);
}

#[test]
fn alpha_nested_group_typed_accessors() {
    let msg = b"11=A\x01453=1\x01448=P1\x01452=1\x01802=1\x01523=SUB1\x01803=7\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    let parties: Vec<_> = m.no_party_i_ds().collect();
    let subs: Vec<_> = parties[0].no_party_sub_i_ds().collect();
    assert_eq!(subs.len(), 1);
    let sub_id = subs[0].party_sub_id().unwrap().get();
    assert_eq!(sub_id.as_bytes(), b"SUB1");
    assert_eq!(subs[0].party_sub_id_type().unwrap().get(), 7);
    assert_eq!(subs[0].party_sub_id_type().unwrap().as_bytes(), &b"7"[..]);
}

#[test]
fn alpha_empty_buffer_does_not_panic() {
    let m = venue_alpha::messages::NewOrderSingle::decode(b"").unwrap();
    assert!(m.cl_ord_id().is_none());
    assert!(m.header().begin_string().is_none());
    assert!(!m.is_complete());
}

#[test]
fn alpha_header_only_no_body() {
    let msg = b"8=FIX.4.4\x0135=D\x0149=S\x0156=T\x0134=1\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(
        m.header().begin_string().unwrap().as_bytes(),
        &b"FIX.4.4"[..]
    );
    assert_eq!(m.header().msg_seq_num().unwrap().get(), 1);
    assert!(m.cl_ord_id().is_none());
    assert!(m.symbol().is_none());
    assert!(!m.is_complete());
}

#[test]
fn alpha_checksum_valid() {
    let body = b"8=FIX.4.4\x0135=0\x01112=HB\x01";
    let sum: u8 = body.iter().fold(0u8, |acc, &b| acc.wrapping_add(b));
    let tag10 = format!("10={:03}\x01", sum);
    let mut msg = body.to_vec();
    msg.extend_from_slice(tag10.as_bytes());
    let m = venue_alpha::messages::Heartbeat::decode(&msg).unwrap();
    assert_eq!(m.test_req_id().unwrap().as_bytes(), &b"HB"[..]);
}

#[test]
fn alpha_checksum_invalid() {
    let body = b"8=FIX.4.4\x0135=0\x01112=HB\x0110=000\x01";
    match venue_alpha::messages::Heartbeat::decode(body) {
        Err(nexus_fix_codec::DecodeError::Checksum(_)) => {}
        _ => panic!("expected Checksum error"),
    }
}

#[test]
fn alpha_checksum_absent_is_ok() {
    let msg = b"8=FIX.4.4\x0135=0\x01112=HB\x01";
    let m = venue_alpha::messages::Heartbeat::decode(msg).unwrap();
    assert_eq!(m.test_req_id().unwrap().as_bytes(), &b"HB"[..]);
}

#[test]
fn alpha_checksum_present_but_empty_is_rejected() {
    // A present-but-empty CheckSum (`10=\x01`) is malformed: `decode` must reject
    // it, not skip verification (which gating on a non-empty value would do). This
    // keeps `decode` consistent with `validate_checksum`, which also rejects it.
    let msg = b"8=FIX.4.4\x0135=0\x01112=HB\x0110=\x01";
    match venue_alpha::messages::Heartbeat::decode(msg) {
        Err(nexus_fix_codec::DecodeError::Checksum(_)) => {}
        _ => panic!("expected Checksum error"),
    }
    assert!(nexus_fix_codec::validate_checksum(msg).is_err());
}

#[test]
fn alpha_decode_unchecked_skips_checksum() {
    // Same bad-checksum message (10=000) `alpha_checksum_invalid` rejects:
    // `decode` errors, but `decode_unchecked` accepts it and parses the body —
    // the trusted-feed fast path.
    let body = b"8=FIX.4.4\x0135=0\x01112=HB\x0110=000\x01";
    assert!(matches!(
        venue_alpha::messages::Heartbeat::decode(body),
        Err(nexus_fix_codec::DecodeError::Checksum(_))
    ));
    let m = venue_alpha::messages::Heartbeat::decode_unchecked(body).unwrap();
    assert_eq!(m.test_req_id().unwrap().as_bytes(), &b"HB"[..]);
}

#[test]
fn alpha_decode_stops_at_checksum_ignoring_trailing() {
    // The body scan stops at the CheckSum terminator (tag 10): a field appended
    // *after* tag 10 must not be parsed. Here a second 112 with a different value
    // follows a valid CheckSum; the decoded test_req_id must be the pre-checksum
    // one, and the (unchanged) checksum still validates.
    let body = b"8=FIX.4.4\x0135=0\x01112=HB\x01";
    let sum: u8 = body.iter().fold(0u8, |acc, &b| acc.wrapping_add(b));
    let mut msg = body.to_vec();
    msg.extend_from_slice(format!("10={sum:03}\x01").as_bytes());
    msg.extend_from_slice(b"112=EVIL\x01"); // trailing field after the terminator
    let m = venue_alpha::messages::Heartbeat::decode(&msg).unwrap();
    assert_eq!(m.test_req_id().unwrap().as_bytes(), &b"HB"[..]);
}

#[test]
fn alpha_encode_buffer_full_errors() {
    // A buffer too small for the framed message → finish() returns BufferFull,
    // never panics.
    let mut buf = [0u8; 24];
    let result = venue_alpha::encoders::NewOrderSingleEncoder::wrap(&mut buf)
        .header_encoder()
        .sender_comp_id(b"SENDER")
        .target_comp_id(b"TARGET")
        .msg_seq_num(1)
        .sending_time(sending_time())
        .finish()
        .cl_ord_id(b"ORD-12345")
        .symbol(b"BTC-USD")
        .finish();
    assert_eq!(result, Err(nexus_fix_codec::EncodeError::BufferFull));
}

#[test]
fn alpha_encode_undersized_reservation_shifts_and_stays_valid() {
    // wrap_reserved with a prefix reservation too small for the BodyLength digits
    // forces finish() to shift the content right; the message must stay valid.
    let mut buf = [0u8; 256];
    let (start, len) = venue_alpha::encoders::NewOrderSingleEncoder::wrap_reserved(&mut buf, 14)
        .header_encoder()
        .sender_comp_id(b"SENDER")
        .target_comp_id(b"TARGET")
        .msg_seq_num(1)
        .sending_time(sending_time())
        .finish()
        .cl_ord_id(b"ORD-12345")
        .side(venue_alpha::fields::Side::BUY)
        .symbol(b"BTC-USD")
        .finish()
        .unwrap();
    let msg = &buf[start..start + len];
    assert!(msg.starts_with(b"8=FIX.4.4\x01"));
    assert!(nexus_fix_codec::validate_checksum(msg).is_ok());
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"BTC-USD"[..]);
}

#[test]
fn alpha_exec_report_typed_and_raw_consistency() {
    let msg = b"37=ORD1\x0117=EX1\x01150=0\x0139=0\x0155=ETH\x0154=2\x0132=100\x0131=50.25\x01";
    let m = venue_alpha::messages::ExecutionReport::decode(msg).unwrap();
    assert_eq!(m.order_id().unwrap().as_bytes(), &b"ORD1"[..]);
    let oid = m.order_id().unwrap().get();
    assert_eq!(oid.as_bytes(), b"ORD1");
    assert_eq!(m.exec_id().unwrap().as_bytes(), &b"EX1"[..]);
    let eid = m.exec_id().unwrap().get();
    assert_eq!(eid.as_bytes(), b"EX1");
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"ETH"[..]);
    let sym = m.symbol().unwrap().get();
    assert_eq!(sym.as_bytes(), b"ETH");
    assert_eq!(m.last_qty().unwrap().as_bytes(), &b"100"[..]);
    assert_eq!(m.last_px().unwrap().as_bytes(), &b"50.25"[..]);
    assert_eq!(
        m.last_px().unwrap().get(),
        nexus_fix_codec::FixDecimal::new(5025, 2,).unwrap()
    );
    assert_eq!(m.side(), Some(venue_alpha::fields::Side::SELL));
    assert_eq!(m.exec_type(), Some(venue_alpha::fields::ExecType::NEW));
    assert_eq!(m.ord_status(), Some(venue_alpha::fields::OrdStatus::NEW));
    assert!(m.is_complete());
}

#[test]
fn alpha_exec_report_incomplete() {
    let msg = b"37=ORD1\x01";
    let m = venue_alpha::messages::ExecutionReport::decode(msg).unwrap();
    assert!(!m.is_complete());
    assert!(m.exec_id().is_none());
    assert!(m.exec_type().is_none());
}

#[test]
fn beta_header_and_wrap() {
    let msg = b"8=FIX.4.2\x0135=A\x0149=CLIENT\x0156=SERVER\x0134=1\x0198=0\x01108=30\x01";
    let header = venue_beta::header::HeaderDecoder::decode(msg);
    assert_eq!(header.begin_string().unwrap().as_bytes(), &b"FIX.4.2"[..]);
    assert_eq!(
        venue_beta::MsgType::from_bytes(header.msg_type().unwrap().as_bytes()),
        Some(venue_beta::MsgType::Logon)
    );
    let sender = header.sender_comp_id().unwrap().get();
    assert_eq!(sender.as_bytes(), b"CLIENT");
    let m = venue_beta::messages::Logon::wrap(header).unwrap();
    assert_eq!(m.encrypt_method().unwrap().get(), 0);
    assert_eq!(m.heart_bt_int().unwrap().get(), 30);
    assert!(m.is_complete());
}

#[test]
fn beta_logon_incomplete() {
    let msg = b"8=FIX.4.2\x0135=A\x0198=0\x01";
    let m = venue_beta::messages::Logon::decode(msg).unwrap();
    assert!(!m.is_complete());
    assert_eq!(m.encrypt_method().unwrap().get(), 0);
    assert!(m.heart_bt_int().is_none());
}

#[test]
fn beta_group_entry_typed_accessors() {
    let msg = b"55=BTC\x01268=1\x01269=0\x01270=42000.50\x01271=3\x01";
    let m = venue_beta::messages::MarketDataSnapshotFullRefresh::decode(msg).unwrap();
    let entries: Vec<_> = m.no_md_entries().collect();
    assert_eq!(entries.len(), 1);
    assert_eq!(
        entries[0].md_entry_px().unwrap().as_bytes(),
        &b"42000.50"[..]
    );
    assert_eq!(
        entries[0].md_entry_px().unwrap().get(),
        nexus_fix_codec::FixDecimal::new(4_200_050, 2,).unwrap()
    );
    assert_eq!(entries[0].md_entry_size().unwrap().as_bytes(), &b"3"[..]);
    assert_eq!(
        entries[0].md_entry_size().unwrap().get(),
        nexus_fix_codec::FixDecimal::new(3, 0,).unwrap()
    );
}

#[test]
fn alpha_data_field_after_header() {
    let msg = b"8=FIX.4.4\x0135=D\x0111=A\x0195=5\x0196=he\x01lo\x0155=X\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(
        m.header().begin_string().unwrap().as_bytes(),
        &b"FIX.4.4"[..]
    );
    assert_eq!(m.raw_data_length().unwrap().get(), 5);
    assert_eq!(m.raw_data().unwrap().as_bytes(), &b"he\x01lo"[..]);
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"X"[..]);
}

#[test]
fn alpha_group_after_header() {
    let msg =
        b"8=FIX.4.4\x0135=D\x0134=7\x0111=A\x01453=2\x01448=P1\x01452=1\x01448=P2\x01452=2\x0155=X\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    assert_eq!(m.header().msg_seq_num().unwrap().get(), 7);
    let parties: Vec<_> = m.no_party_i_ds().collect();
    assert_eq!(parties.len(), 2);
    assert_eq!(parties[0].party_id().unwrap().as_bytes(), &b"P1"[..]);
    assert_eq!(parties[1].party_id().unwrap().as_bytes(), &b"P2"[..]);
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"X"[..]);
}

#[test]
fn modules_are_independent() {
    assert_eq!(venue_alpha::BEGIN_STRING, b"FIX.4.4");
    assert_eq!(venue_beta::BEGIN_STRING, b"FIX.4.2");
}

#[test]
fn alpha_dict_trait() {
    use nexus_fix_codec::FixDictionary;
    assert_eq!(venue_alpha::Dict::BEGIN_STRING, b"FIX.4.4");
    assert_eq!(
        venue_alpha::MsgType::from_bytes(b"D"),
        Some(venue_alpha::MsgType::NewOrderSingle)
    );
    assert_eq!(
        venue_alpha::MsgType::from_bytes(b"0"),
        Some(venue_alpha::MsgType::Heartbeat)
    );
    assert!(venue_alpha::Dict::is_admin(venue_alpha::MsgType::Heartbeat));
    assert!(!venue_alpha::Dict::is_admin(
        venue_alpha::MsgType::NewOrderSingle
    ));
    assert!(!venue_alpha::Dict::is_admin(
        venue_alpha::MsgType::ExecutionReport
    ));
}

#[test]
fn beta_dict_trait() {
    use nexus_fix_codec::FixDictionary;
    assert_eq!(venue_beta::Dict::BEGIN_STRING, b"FIX.4.2");
    assert!(venue_beta::Dict::is_admin(venue_beta::MsgType::Logon));
    assert!(!venue_beta::Dict::is_admin(
        venue_beta::MsgType::MarketDataSnapshotFullRefresh
    ));
}

#[test]
fn header_decode_and_msg_type_conversion() {
    use nexus_fix_codec::FixDictionary;
    let msg = b"8=FIX.4.4\x0135=0\x0134=1\x0149=S\x0156=T\x01112=HB\x01";
    let h = venue_alpha::header::HeaderDecoder::decode(msg);
    let mt = h.msg_type().unwrap();
    assert_eq!(mt, venue_alpha::MsgType::Heartbeat);
    assert!(venue_alpha::Dict::is_admin(mt));
    assert_eq!(h.msg_seq_num().unwrap().get(), 1);
}

#[test]
fn alpha_group_view_len_and_empty() {
    let msg = b"11=A\x01453=2\x01448=P1\x01452=1\x01448=P2\x01452=2\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    let view = m.no_party_i_ds();
    assert_eq!(view.len(), 2);
    assert!(!view.is_empty());
    assert_eq!(view.count(), 2);
}

#[test]
fn alpha_group_view_absent() {
    let msg = b"11=A\x01";
    let m = venue_alpha::messages::NewOrderSingle::decode(msg).unwrap();
    let view = m.no_party_i_ds();
    assert_eq!(view.len(), 0);
    assert!(view.is_empty());
    assert_eq!(view.count(), 0);
}

#[test]
fn alpha_group_encode_round_trip() {
    let mut buf = [0u8; 512];
    let (start, len) = venue_alpha::encoders::NewOrderSingleEncoder::wrap(&mut buf)
        .header_encoder()
        .sender_comp_id(b"S")
        .target_comp_id(b"T")
        .msg_seq_num(1)
        .sending_time(sending_time())
        .finish()
        .cl_ord_id(b"ORD1")
        .side(venue_alpha::fields::Side::BUY)
        .no_party_i_ds(2)
        .entry()
        .party_id(b"P1")
        .party_role(1)
        .done()
        .entry()
        .party_id(b"P2")
        .party_role(2)
        .done()
        .finish_group()
        .unwrap()
        .symbol(b"BTC")
        .finish()
        .unwrap();
    let full = &buf[start..start + len];

    assert!(nexus_fix_codec::validate_checksum(full).is_ok());

    let m = venue_alpha::messages::NewOrderSingle::decode(full).unwrap();
    assert_eq!(m.cl_ord_id().unwrap().as_bytes(), &b"ORD1"[..]);
    assert_eq!(m.side(), Some(venue_alpha::fields::Side::BUY));
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"BTC"[..]);
    let parties: Vec<_> = m.no_party_i_ds().collect();
    assert_eq!(parties.len(), 2);
    assert_eq!(parties[0].party_id().unwrap().as_bytes(), &b"P1"[..]);
    assert_eq!(parties[0].party_role().unwrap().get(), 1);
    assert_eq!(parties[1].party_id().unwrap().as_bytes(), &b"P2"[..]);
    assert_eq!(parties[1].party_role().unwrap().get(), 2);
}

#[test]
fn alpha_nested_group_encode_round_trip() {
    let mut buf = [0u8; 512];
    let (start, len) = venue_alpha::encoders::NewOrderSingleEncoder::wrap(&mut buf)
        .header_encoder()
        .sender_comp_id(b"S")
        .target_comp_id(b"T")
        .msg_seq_num(1)
        .sending_time(sending_time())
        .finish()
        .cl_ord_id(b"ORD1")
        .side(venue_alpha::fields::Side::BUY)
        .no_party_i_ds(1)
        .entry()
        .party_id(b"P1")
        .party_role(1)
        .no_party_sub_i_ds(2)
        .entry()
        .party_sub_id(b"S1")
        .party_sub_id_type(7)
        .done()
        .entry()
        .party_sub_id(b"S2")
        .party_sub_id_type(8)
        .done()
        .finish_group()
        .unwrap()
        .done()
        .finish_group()
        .unwrap()
        .symbol(b"BTC")
        .finish()
        .unwrap();
    let full = &buf[start..start + len];

    assert!(nexus_fix_codec::validate_checksum(full).is_ok());

    let m = venue_alpha::messages::NewOrderSingle::decode(full).unwrap();
    let parties: Vec<_> = m.no_party_i_ds().collect();
    assert_eq!(parties.len(), 1);
    assert_eq!(parties[0].party_id().unwrap().as_bytes(), &b"P1"[..]);
    assert_eq!(parties[0].party_role().unwrap().get(), 1);
    let subs: Vec<_> = parties[0].no_party_sub_i_ds().collect();
    assert_eq!(subs.len(), 2);
    assert_eq!(subs[0].party_sub_id().unwrap().as_bytes(), &b"S1"[..]);
    assert_eq!(subs[0].party_sub_id_type().unwrap().get(), 7);
    assert_eq!(subs[1].party_sub_id().unwrap().as_bytes(), &b"S2"[..]);
    assert_eq!(subs[1].party_sub_id_type().unwrap().get(), 8);
}

#[test]
fn beta_group_encode_round_trip() {
    let px_bid = nexus_fix_codec::FixDecimal::new(11050, 4).unwrap();
    let px_offer = nexus_fix_codec::FixDecimal::new(11052, 4).unwrap();
    let sz = nexus_fix_codec::FixDecimal::new(1_000_000, 0).unwrap();

    let mut buf = [0u8; 512];
    let (start, len) = venue_beta::encoders::MarketDataSnapshotFullRefreshEncoder::wrap(&mut buf)
        .header_encoder()
        .finish()
        .symbol(b"EUR/USD")
        .no_md_entries(2)
        .entry()
        .md_entry_type(venue_beta::fields::MDEntryType::BID)
        .md_entry_px(px_bid)
        .md_entry_size(sz)
        .done()
        .entry()
        .md_entry_type(venue_beta::fields::MDEntryType::OFFER)
        .md_entry_px(px_offer)
        .md_entry_size(sz)
        .done()
        .finish_group()
        .unwrap()
        .finish()
        .unwrap();
    let full = &buf[start..start + len];

    assert!(nexus_fix_codec::validate_checksum(full).is_ok());

    let m = venue_beta::messages::MarketDataSnapshotFullRefresh::decode(full).unwrap();
    assert_eq!(m.symbol().unwrap().as_bytes(), &b"EUR/USD"[..]);
    let entries: Vec<_> = m.no_md_entries().collect();
    assert_eq!(entries.len(), 2);
    assert_eq!(
        entries[0].md_entry_type(),
        Some(venue_beta::fields::MDEntryType::BID)
    );
    assert_eq!(entries[0].md_entry_px().unwrap().get(), px_bid);
    assert_eq!(entries[0].md_entry_size().unwrap().get(), sz);
    assert_eq!(
        entries[1].md_entry_type(),
        Some(venue_beta::fields::MDEntryType::OFFER)
    );
    assert_eq!(entries[1].md_entry_px().unwrap().get(), px_offer);
}

#[test]
fn alpha_group_count_mismatch_errors() {
    // Declares 2 party entries but writes 1 → finish_group() returns
    // EncodeError::GroupCountMismatch rather than panicking, so the caller
    // chooses the failure policy.
    let mut buf = [0u8; 512];
    let result = venue_alpha::encoders::NewOrderSingleEncoder::wrap(&mut buf)
        .header_encoder()
        .sender_comp_id(b"S")
        .target_comp_id(b"T")
        .msg_seq_num(1)
        .sending_time(sending_time())
        .finish()
        .cl_ord_id(b"ORD1")
        .no_party_i_ds(2)
        .entry()
        .party_id(b"P1")
        .done()
        .finish_group();
    assert!(matches!(
        result,
        Err(nexus_fix_codec::EncodeError::GroupCountMismatch {
            declared: 2,
            written: 1
        })
    ));
}
