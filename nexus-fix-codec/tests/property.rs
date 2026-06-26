//! Property-based tests for the FIX value-type layer.
//!
//! Two invariants a robust FIX engine depends on:
//! 1. **No parser panics on arbitrary wire bytes** — hostile/garbled input
//!    must yield `Err`, never a crash (no out-of-bounds, no overflow panic).
//! 2. **Every valid value round-trips** — `construct -> encode -> parse`
//!    reproduces the original value.

use core::num::NonZeroU32;
use nexus_fix_codec::{
    FixDate, FixDecimal, FixMonthYear, FixTenor, FixTime, FixTimestamp, FixTzTime, FixTzTimestamp,
    FixValueError, TenorUnit, parse_fix_bool, parse_fix_char, parse_fix_day_of_month,
    parse_fix_int, parse_fix_multi_char, parse_fix_multi_string, parse_fix_seqnum, parse_fix_text,
    parse_fix_uint,
};
use proptest::prelude::*;

// One nanosecond past the last representable instant of a day, i.e. the top of
// the leap-second range 23:59:60.999_999_999.
const NANOS_PER_DAY_PLUS_ONE_SEC: u64 = 86_401 * 1_000_000_000;

fn tenor_unit() -> impl Strategy<Value = TenorUnit> {
    prop_oneof![
        Just(TenorUnit::Day),
        Just(TenorUnit::Week),
        Just(TenorUnit::Month),
        Just(TenorUnit::Year),
    ]
}

proptest! {
    // -- No parser panics on arbitrary input --

    #[test]
    fn parsers_never_panic_on_arbitrary_bytes(bytes in proptest::collection::vec(any::<u8>(), 0..80)) {
        drive_all_parsers(&bytes);
    }

    #[test]
    fn parsers_never_panic_on_printable_ascii(s in "[\\x20-\\x7e]{0,48}") {
        drive_all_parsers(s.as_bytes());
    }

    // Concentrate on the bytes that drive the numeric/temporal parse paths
    // deepest (signs, digits, separators, units).
    #[test]
    fn parsers_never_panic_on_structured_bytes(s in "[-+0-9.:wZDWMY ]{0,48}") {
        drive_all_parsers(s.as_bytes());
    }

    // -- Round-trip: construct -> encode -> parse --

    #[test]
    fn decimal_roundtrip_reject_overflow(mantissa in any::<i64>(), scale in 20..=255u8) {
        prop_assert!(matches!(
            FixDecimal::new(mantissa, scale),
            Err(FixValueError::Overflow)
        ));
    }

    #[test]
    fn decimal_roundtrip(mantissa in any::<i64>(), scale in 0u8..=19) {
        let d = FixDecimal::new( mantissa, scale).unwrap();
        let mut buf = [0u8; 22];
        let n = d.encode(&mut buf);
        prop_assert_eq!(FixDecimal::parse(&buf[..n]).unwrap(), d);
    }

    #[test]
    fn date_roundtrip(year in 0u16..=9999, month in 1u8..=12, day in 1u8..=31) {
        let d = FixDate { year, month, day };
        let mut buf = [0u8; 8];
        let n = d.encode(&mut buf);
        prop_assert_eq!(FixDate::parse(&buf[..n]).unwrap(), d);
    }

    #[test]
    fn time_roundtrip(nanos in 0u64..NANOS_PER_DAY_PLUS_ONE_SEC) {
        // range includes the leap-second band [NANOS_PER_DAY, +1s)
        let t = FixTime { nanos_since_midnight: nanos };
        let mut buf = [0u8; 18];
        let n = t.encode(&mut buf);
        prop_assert_eq!(FixTime::parse(&buf[..n]).unwrap(), t);
    }

    #[test]
    fn tenor_roundtrip(unit in tenor_unit(), value in 1u32..=u32::MAX) {
        let t = FixTenor { unit, value: NonZeroU32::new(value).unwrap() };
        let mut buf = [0u8; 11];
        let n = t.encode(&mut buf);
        prop_assert_eq!(FixTenor::parse(&buf[..n]).unwrap(), t);
    }

    #[test]
    fn month_year_ym_roundtrip(year in 0u16..=9999, month in 1u8..=12) {
        let my = FixMonthYear::YearMonth { year, month };
        let mut buf = [0u8; 8];
        let n = my.encode(&mut buf);
        prop_assert_eq!(FixMonthYear::parse(&buf[..n]).unwrap(), my);
    }

    #[test]
    fn month_year_ymd_roundtrip(year in 0u16..=9999, month in 1u8..=12, day in 1u8..=31) {
        let my = FixMonthYear::YearMonthDay(FixDate { year, month, day });
        let mut buf = [0u8; 8];
        let n = my.encode(&mut buf);
        prop_assert_eq!(FixMonthYear::parse(&buf[..n]).unwrap(), my);
    }

    #[test]
    fn month_year_ymw_roundtrip(year in 0u16..=9999, month in 1u8..=12, week in 1u8..=5) {
        let my = FixMonthYear::YearMonthWeek { year, month, week };
        let mut buf = [0u8; 8];
        let n = my.encode(&mut buf);
        prop_assert_eq!(FixMonthYear::parse(&buf[..n]).unwrap(), my);
    }

    #[test]
    fn tz_time_roundtrip(
        nanos in 0u64..NANOS_PER_DAY_PLUS_ONE_SEC,
        offset in -1439i16..=1439,
    ) {
        let t = FixTzTime {
            time: FixTime { nanos_since_midnight: nanos },
            offset_minutes: offset,
        };
        let mut buf = [0u8; 24];
        let n = t.encode(&mut buf);
        prop_assert_eq!(FixTzTime::parse(&buf[..n]).unwrap(), t);
    }

    // FixTzTimestamp: build from a valid date/time/offset, round-trip the
    // bytes. Restrict to seconds (no leap, no offset of 0 which renders Z) so
    // the comparison is byte-exact.
    #[test]
    fn tz_timestamp_roundtrip(
        year in 1970u16..=9999,
        month in 1u8..=12,
        day in 1u8..=28,
        hour in 0u8..=23,
        minute in 0u8..=59,
        second in 0u8..=59,
        sign in prop::bool::ANY,
        oh in 0u8..=14,
        om in 0u8..=59,
    ) {
        // canonical "±HH:MM" with a non-zero magnitude
        let offset_mag = oh as u16 * 60 + om as u16;
        prop_assume!(offset_mag != 0);
        let s = format!(
            "{year:04}{month:02}{day:02}-{hour:02}:{minute:02}:{second:02}{}{oh:02}:{om:02}",
            if sign { '+' } else { '-' },
        );
        let ts = FixTzTimestamp::parse(s.as_bytes()).unwrap();
        let mut buf = [0u8; 33];
        let n = ts.encode(&mut buf);
        prop_assert_eq!(&buf[..n], s.as_bytes());
    }
}

/// Call every public parser; a panic here fails the property.
fn drive_all_parsers(bytes: &[u8]) {
    let _ = parse_fix_int(bytes);
    let _ = parse_fix_uint(bytes);
    let _ = parse_fix_seqnum(bytes);
    let _ = parse_fix_bool(bytes);
    let _ = parse_fix_char(bytes);
    let _ = parse_fix_day_of_month(bytes);
    let _ = parse_fix_text(bytes);
    let _ = FixDecimal::parse(bytes);
    let _ = FixDate::parse(bytes);
    let _ = FixTime::parse(bytes);
    let _ = FixTimestamp::parse(bytes);
    let _ = FixMonthYear::parse(bytes);
    let _ = FixTenor::parse(bytes);
    let _ = FixTzTime::parse(bytes);
    let _ = FixTzTimestamp::parse(bytes);
    // drive the iterators to completion so the inner parse work runs
    if let Ok(it) = parse_fix_multi_char(bytes) {
        let _ = it.count();
    }
    if let Ok(it) = parse_fix_multi_string(bytes) {
        let _ = it.count();
    }
}
