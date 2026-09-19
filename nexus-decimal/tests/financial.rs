//! Financial methods, serde, num-traits, and type conversions.

use nexus_decimal::Decimal;

type D64 = Decimal<i64, 8>;
type D96 = Decimal<i128, 12>;

// ============================================================================
// Financial: midpoint
// ============================================================================

#[test]
fn midpoint_basic() {
    let bid = D64::new(100, 0);
    let ask = D64::new(101, 0);
    assert_eq!(bid.midpoint(ask), D64::new(100, 50_000_000));
}

#[test]
fn midpoint_same() {
    let p = D64::new(42, 0);
    assert_eq!(p.midpoint(p), p);
}

#[test]
fn midpoint_negative() {
    let a = D64::new(-10, 0);
    let b = D64::new(10, 0);
    assert_eq!(a.midpoint(b), D64::ZERO);
}

// ============================================================================
// Financial: spread
// ============================================================================

#[test]
fn spread_basic() {
    let ask = D64::new(101, 0);
    let bid = D64::new(100, 0);
    assert_eq!(ask.spread(bid).unwrap(), D64::new(1, 0));
}

#[test]
fn spread_crossed_returns_none() {
    // spread(self, other) returns None when self < other
    let low = D64::new(99, 0);
    let high = D64::new(100, 0);
    assert!(low.spread(high).is_none());
}

// ============================================================================
// Financial: tick rounding
// ============================================================================

#[test]
fn round_to_tick() {
    let price = D64::new(1, 23_700_000); // 1.237
    let tick = D64::new(0, 5_000_000); // 0.05
    assert_eq!(price.round_to_tick(tick), Some(D64::new(1, 25_000_000))); // 1.25
}

#[test]
fn round_to_tick_odd_tick() {
    // tick=3: no true midpoint exists (2*remainder is always even, tick is odd).
    // The truncated half_tick=1 is not the midpoint; value=4 must round to 3 not 6.
    let tick = D64::from_raw(3);
    assert_eq!(D64::from_raw(4).round_to_tick(tick), Some(D64::from_raw(3)));
    assert_eq!(D64::from_raw(5).round_to_tick(tick), Some(D64::from_raw(6)));
    assert_eq!(
        D64::from_raw(-4).round_to_tick(tick),
        Some(D64::from_raw(-3))
    );
    assert_eq!(
        D64::from_raw(-5).round_to_tick(tick),
        Some(D64::from_raw(-6))
    );
}

#[test]
fn round_to_tick_even_tick_bankers() {
    // tick=4: true midpoint at remainder==2; banker's rounds to the even multiple.
    let tick = D64::from_raw(4);
    assert_eq!(D64::from_raw(6).round_to_tick(tick), Some(D64::from_raw(8))); // quotient 1 odd -> up
    assert_eq!(D64::from_raw(2).round_to_tick(tick), Some(D64::from_raw(0))); // quotient 0 even -> down
    assert_eq!(
        D64::from_raw(-6).round_to_tick(tick),
        Some(D64::from_raw(-8))
    ); // quotient -1 odd -> down
    assert_eq!(
        D64::from_raw(-2).round_to_tick(tick),
        Some(D64::from_raw(0))
    ); // quotient 0 even -> base
}

#[test]
fn floor_to_tick() {
    let price = D64::new(1, 23_700_000); // 1.237
    let tick = D64::new(0, 5_000_000); // 0.05
    assert_eq!(price.floor_to_tick(tick), Some(D64::new(1, 20_000_000))); // 1.20
}

#[test]
fn ceil_to_tick() {
    let price = D64::new(1, 23_700_000); // 1.237
    let tick = D64::new(0, 5_000_000); // 0.05
    assert_eq!(price.ceil_to_tick(tick), Some(D64::new(1, 25_000_000))); // 1.25
}

#[test]
fn floor_to_tick_exact() {
    let price = D64::new(1, 25_000_000); // exactly on tick
    let tick = D64::new(0, 5_000_000);
    assert_eq!(price.floor_to_tick(tick), Some(price));
}

// ============================================================================
// Financial: halve, div10, div100
// ============================================================================

#[test]
fn halve_basic() {
    assert_eq!(D64::new(10, 0).halve(), D64::new(5, 0));
    assert_eq!(D64::new(1, 0).halve(), D64::new(0, 50_000_000));
}

#[test]
fn halve_truncates_toward_zero() {
    // 3 / 2 = 1 (truncated)
    let three = D64::from_raw(3);
    assert_eq!(three.halve(), D64::from_raw(1));
    // -3 / 2 = -1 (truncated toward zero, not -2)
    let neg_three = D64::from_raw(-3);
    assert_eq!(neg_three.halve(), D64::from_raw(-1));
}

#[test]
fn div10_basic() {
    assert_eq!(D64::new(100, 0).div10(), D64::new(10, 0));
}

#[test]
fn div100_basic() {
    assert_eq!(D64::new(100, 0).div100(), D64::new(1, 0));
}

// ============================================================================
// Financial: basis points
// ============================================================================

#[test]
fn to_bps() {
    // 0.01 * 10000 = 100 bps
    let one_percent = D64::new(0, 1_000_000); // 0.01
    assert_eq!(one_percent.to_bps().unwrap(), D64::new(100, 0));
}

#[test]
fn from_bps() {
    // 100 bps = 0.01
    let result = D64::from_bps(100).unwrap();
    assert_eq!(result, D64::new(0, 1_000_000));
}

// ============================================================================
// Financial: mul_div
// ============================================================================

#[test]
fn mul_div_basic() {
    // 100 * 3 / 2 = 150
    let a = D64::new(100, 0);
    let b = D64::new(3, 0);
    let c = D64::new(2, 0);
    assert_eq!(a.mul_div(b, c).unwrap(), D64::new(150, 0));
}

#[test]
fn mul_div_zero_divisor() {
    assert!(D64::ONE.mul_div(D64::ONE, D64::ZERO).is_none());
}

// ============================================================================
// Financial: approx_eq, clamp_price
// ============================================================================

#[test]
fn approx_eq_within_tolerance() {
    let a = D64::new(100, 0);
    let b = D64::new(100, 1_000_000); // 100.01
    let tolerance = D64::new(0, 5_000_000); // 0.05
    assert!(a.approx_eq(b, tolerance));
}

#[test]
fn approx_eq_outside_tolerance() {
    let a = D64::new(100, 0);
    let b = D64::new(101, 0);
    let tolerance = D64::new(0, 50_000_000); // 0.5
    assert!(!a.approx_eq(b, tolerance));
}

#[test]
fn approx_eq_extreme_values_i64() {
    // MAX - MIN overflows i64. Must not panic, must return false.
    let max = D64::MAX;
    let min = D64::MIN;
    let tol = D64::from_raw(100);
    assert!(!max.approx_eq(min, tol));
    assert!(!min.approx_eq(max, tol));
}

#[test]
fn approx_eq_extreme_values_i32() {
    type D32 = Decimal<i32, 4>;
    assert!(!D32::MAX.approx_eq(D32::MIN, D32::from_raw(1)));
    assert!(!D32::MIN.approx_eq(D32::MAX, D32::from_raw(1)));
}

#[test]
fn approx_eq_extreme_values_i128() {
    assert!(!D96::MAX.approx_eq(D96::MIN, D96::from_raw(1)));
    assert!(!D96::MIN.approx_eq(D96::MAX, D96::from_raw(1)));
}

#[test]
fn clamp_price() {
    let min = D64::new(90, 0);
    let max = D64::new(110, 0);
    assert_eq!(D64::new(100, 0).clamp_price(min, max), D64::new(100, 0));
    assert_eq!(D64::new(80, 0).clamp_price(min, max), min);
    assert_eq!(D64::new(120, 0).clamp_price(min, max), max);
}

// ============================================================================
// Sum and Product iterators
// ============================================================================

#[test]
fn sum_iterator() {
    let values = vec![D64::new(1, 0), D64::new(2, 0), D64::new(3, 0)];
    let total: D64 = values.into_iter().sum();
    assert_eq!(total, D64::new(6, 0));
}

#[test]
fn sum_ref_iterator() {
    let values = [D64::new(1, 0), D64::new(2, 0), D64::new(3, 0)];
    let total: D64 = values.iter().sum();
    assert_eq!(total, D64::new(6, 0));
}

#[test]
fn product_iterator() {
    let values = vec![D64::new(2, 0), D64::new(3, 0), D64::new(4, 0)];
    let total: D64 = values.into_iter().product();
    assert_eq!(total, D64::new(24, 0));
}

// ============================================================================
// TryFrom conversions
// ============================================================================

#[test]
fn try_from_i64() {
    let d: D64 = 42i64.try_into().unwrap();
    assert_eq!(d, D64::new(42, 0));
}

#[cfg(feature = "std")]
#[test]
fn try_from_f64() {
    let d: D64 = 1.5f64.try_into().unwrap();
    assert_eq!(d, D64::new(1, 50_000_000));
}

// ============================================================================
// Rem operator
// ============================================================================

#[test]
fn rem_basic() {
    let a = D64::new(10, 0);
    let b = D64::new(3, 0);
    // 10.0 % 3.0 = 1.0 (on raw values: 1000000000 % 300000000 = 100000000)
    assert_eq!(a % b, D64::new(1, 0));
}

// ============================================================================
// Serde (feature-gated)
// ============================================================================

#[cfg(feature = "serde")]
mod serde_tests {
    use super::*;

    #[test]
    fn json_roundtrip_d64() {
        let original = D64::new(123, 45_678_900);
        let json = serde_json::to_string(&original).unwrap();
        assert_eq!(json, "\"123.456789\"");
        let parsed: D64 = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed, original);
    }

    #[test]
    fn json_zero() {
        let json = serde_json::to_string(&D64::ZERO).unwrap();
        assert_eq!(json, "\"0\"");
        let parsed: D64 = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed, D64::ZERO);
    }

    #[test]
    fn json_negative() {
        let d = D64::new(-42, 50_000_000);
        let json = serde_json::to_string(&d).unwrap();
        assert_eq!(json, "\"-42.5\"");
        let parsed: D64 = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed, d);
    }

    #[test]
    fn json_d96() {
        let original = D96::new(42, 123_000_000_000);
        let json = serde_json::to_string(&original).unwrap();
        let parsed: D96 = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed, original);
    }
}

// ============================================================================
// num-traits (feature-gated)
// ============================================================================

#[cfg(feature = "num-traits")]
mod num_traits_tests {
    use super::*;
    use num_traits::{Bounded, CheckedAdd, FromPrimitive, Num, One, Signed, ToPrimitive, Zero};

    #[test]
    fn zero_one() {
        assert!(D64::zero().is_zero());
        assert!(D64::one().is_one());
    }

    #[test]
    fn bounded() {
        assert_eq!(D64::min_value(), D64::MIN);
        assert_eq!(D64::max_value(), D64::MAX);
    }

    #[test]
    fn signed_abs() {
        let neg = D64::new(-42, 0);
        assert_eq!(neg.abs(), D64::new(42, 0));
        assert!(neg.is_negative());
        assert!(!neg.is_positive());
    }

    #[test]
    fn signed_signum() {
        // num-traits Signed::signum returns Decimal, not backing type
        let pos: D64 = Signed::signum(&D64::new(42, 0));
        let zero: D64 = Signed::signum(&D64::ZERO);
        let neg: D64 = Signed::signum(&D64::new(-42, 0));
        assert_eq!(pos, D64::ONE);
        assert_eq!(zero, D64::ZERO);
        assert_eq!(neg, D64::NEG_ONE);
    }

    #[test]
    fn checked_add_trait() {
        let a = D64::new(1, 0);
        let b = D64::new(2, 0);
        assert_eq!(CheckedAdd::checked_add(&a, &b), Some(D64::new(3, 0)));
    }

    #[test]
    fn from_str_radix_10() {
        let d = D64::from_str_radix("42.5", 10).unwrap();
        assert_eq!(d, D64::new(42, 50_000_000));
    }

    #[test]
    fn from_str_radix_non_10_errors() {
        assert!(D64::from_str_radix("42", 16).is_err());
    }

    #[test]
    fn to_primitive() {
        let d = D64::new(42, 0);
        assert_eq!(ToPrimitive::to_i64(&d), Some(42));
        assert_eq!(ToPrimitive::to_u64(&d), Some(42));
        assert!((ToPrimitive::to_f64(&d).unwrap() - 42.0).abs() < 1e-10);
    }

    #[test]
    fn from_primitive() {
        let d: D64 = FromPrimitive::from_i64(42).unwrap();
        assert_eq!(d, D64::new(42, 0));
    }

    #[test]
    fn generic_sum() {
        fn sum_generic<T: Num + Copy>(values: &[T]) -> T {
            values.iter().fold(T::zero(), |acc, &x| acc + x)
        }
        let values = [D64::new(1, 0), D64::new(2, 0), D64::new(3, 0)];
        assert_eq!(sum_generic(&values), D64::new(6, 0));
    }
}

// ============================================================================
// Midpoint: extreme values (overflow-free formula)
// ============================================================================

#[test]
fn midpoint_max_max() {
    assert_eq!(D64::MAX.midpoint(D64::MAX), D64::MAX);
}

#[test]
fn midpoint_min_min() {
    assert_eq!(D64::MIN.midpoint(D64::MIN), D64::MIN);
}

#[test]
fn midpoint_max_min() {
    // (MAX + MIN) / 2 — should be close to zero (they're symmetric-ish)
    let mid = D64::MAX.midpoint(D64::MIN);
    // i64::MAX = 9223372036854775807, i64::MIN = -9223372036854775808
    // avg = (MAX & MIN) + ((MAX ^ MIN) >> 1) = 0 + (all-bits-set >> 1) = -1
    // So midpoint of MAX and MIN raw values is -1 (which is -0.00000001 for D64)
    assert_eq!(mid.to_raw(), -1);
}

#[test]
fn midpoint_max_zero() {
    let mid = D64::MAX.midpoint(D64::ZERO);
    // Should be approximately MAX / 2
    let expected = D64::from_raw(D64::MAX.to_raw() / 2);
    assert_eq!(mid, expected);
}

#[test]
fn midpoint_min_zero() {
    let mid = D64::MIN.midpoint(D64::ZERO);
    let expected = D64::from_raw(D64::MIN.to_raw() / 2);
    assert_eq!(mid, expected);
}

#[test]
fn midpoint_reversed_order() {
    // midpoint(a, b) should equal midpoint(b, a)
    let a = D64::new(100, 0);
    let b = D64::new(200, 0);
    assert_eq!(a.midpoint(b), b.midpoint(a));
}

#[test]
fn midpoint_i32_extreme() {
    type D32 = Decimal<i32, 4>;
    assert_eq!(D32::MAX.midpoint(D32::MAX), D32::MAX);
    assert_eq!(D32::MIN.midpoint(D32::MIN), D32::MIN);
    let _ = D32::MAX.midpoint(D32::MIN); // must not panic
}

#[test]
fn midpoint_i128_extreme() {
    assert_eq!(D96::MAX.midpoint(D96::MAX), D96::MAX);
    assert_eq!(D96::MIN.midpoint(D96::MIN), D96::MIN);
    let _ = D96::MAX.midpoint(D96::MIN); // must not panic
}

// ============================================================================
// from_parts
// ============================================================================

#[test]
fn from_parts_positive() {
    let d = D64::from_parts(1, 25_000_000, false).unwrap();
    assert_eq!(d, D64::new(1, 25_000_000));
}

#[test]
fn from_parts_negative() {
    // The main reason from_parts exists: constructing -0.5
    let d = D64::from_parts(0, 50_000_000, true).unwrap();
    assert_eq!(d.to_raw(), -50_000_000);
}

#[test]
fn from_parts_negative_with_integer() {
    let d = D64::from_parts(1, 75_000_000, true).unwrap();
    assert_eq!(d, D64::new(-1, 75_000_000));
}

#[test]
fn from_parts_zero() {
    let d = D64::from_parts(0, 0, false).unwrap();
    assert_eq!(d, D64::ZERO);
}

#[test]
fn from_parts_negative_zero() {
    // -0 should still be 0
    let d = D64::from_parts(0, 0, true).unwrap();
    assert_eq!(d, D64::ZERO);
}

#[test]
fn from_parts_overflow() {
    // Integer too large to scale
    assert!(D64::from_parts(i64::MAX, 0, false).is_none());
}

#[test]
fn from_parts_i32() {
    type D32 = Decimal<i32, 4>;
    let d = D32::from_parts(0, 5_000, true).unwrap(); // -0.5
    assert_eq!(d.to_raw(), -5_000);
}

#[test]
fn from_parts_i128() {
    let d = D96::from_parts(0, 500_000_000_000, true).unwrap(); // -0.5
    assert_eq!(d.to_raw(), -500_000_000_000);
}

// ============================================================================
// write_to_buf
// ============================================================================

#[test]
fn write_to_buf_basic() {
    let d = D64::new(123, 45_000_000);
    let mut buf = [0u8; 64];
    let len = d.write_to_buf(&mut buf);
    let s = core::str::from_utf8(&buf[..len]).unwrap();
    assert_eq!(s, "123.45");
}

#[test]
fn write_to_buf_zero() {
    let mut buf = [0u8; 64];
    let len = D64::ZERO.write_to_buf(&mut buf);
    assert_eq!(&buf[..len], b"0");
}

#[test]
fn write_to_buf_negative() {
    let d = D64::new(-42, 50_000_000);
    let mut buf = [0u8; 64];
    let len = d.write_to_buf(&mut buf);
    let s = core::str::from_utf8(&buf[..len]).unwrap();
    assert_eq!(s, "-42.5");
}

#[test]
fn write_to_buf_integer_only() {
    let d = D64::new(100, 0);
    let mut buf = [0u8; 64];
    let len = d.write_to_buf(&mut buf);
    assert_eq!(&buf[..len], b"100");
}

#[test]
fn write_to_buf_matches_display() {
    use std::string::ToString;
    let values = [
        D64::new(0, 0),
        D64::new(1, 0),
        D64::new(-1, 0),
        D64::new(123, 45_000_000),
        D64::new(-99, 99_000_000),
        D64::MAX,
        D64::MIN,
    ];
    for d in values {
        let display_str = d.to_string();
        let mut buf = [0u8; 64];
        let len = d.write_to_buf(&mut buf);
        let buf_str = std::str::from_utf8(&buf[..len]).unwrap();
        assert_eq!(
            buf_str,
            display_str.as_str(),
            "mismatch for raw={}",
            d.to_raw()
        );
    }
}

// ============================================================================
// ceil_to_tick (undercovered)
// ============================================================================

#[test]
fn ceil_to_tick_basic() {
    let price = D64::new(1, 23_000_000); // 1.23
    let tick = D64::new(0, 5_000_000); // 0.05
    let result = price.ceil_to_tick(tick).unwrap();
    assert_eq!(result, D64::new(1, 25_000_000)); // 1.25
}

#[test]
fn ceil_to_tick_already_aligned() {
    let price = D64::new(1, 25_000_000); // 1.25
    let tick = D64::new(0, 25_000_000); // 0.25
    let result = price.ceil_to_tick(tick).unwrap();
    assert_eq!(result, price);
}

// ============================================================================
// div100 (additional coverage)
// ============================================================================

#[test]
fn div100_produces_fractional() {
    let d = D64::new(1, 0);
    assert_eq!(d.div100(), D64::new(0, 1_000_000)); // 0.01
}

#[test]
fn div100_negative() {
    let d = D64::new(-100, 0);
    assert_eq!(d.div100(), D64::new(-1, 0));
}

// ============================================================================
// BASIS_POINT constant
// ============================================================================

#[test]
fn basis_point_value() {
    assert_eq!(D64::BASIS_POINT.to_raw(), 10_000); // 10^8 / 10000
    assert_eq!(D64::BASIS_POINT, D64::from_raw(10_000));
}

#[test]
fn basis_point_cross_backing() {
    type X32 = Decimal<i32, 4>;
    type X64 = Decimal<i64, 4>;
    type X128 = Decimal<i128, 4>;

    assert_eq!(X32::BASIS_POINT.to_raw() as i64, X64::BASIS_POINT.to_raw());
    assert_eq!(
        X64::BASIS_POINT.to_raw() as i128,
        X128::BASIS_POINT.to_raw()
    );
}

// ============================================================================
// bps_of / pct_of
// ============================================================================

#[test]
fn bps_of_basic() {
    let price = D64::new(100, 0);
    // 5 bps of 100 = 100 * 5 / 10000 = 0.05
    assert_eq!(price.bps_of(5), Some(D64::new(0, 5_000_000)));
    // negative bps
    assert_eq!(price.bps_of(-5), Some(D64::from_raw(-5_000_000)));
    // zero bps
    assert_eq!(price.bps_of(0), Some(D64::ZERO));
}

#[test]
fn pct_of_basic() {
    let price = D64::new(100, 0);
    assert_eq!(price.pct_of(50), Some(D64::new(50, 0)));
    assert_eq!(price.pct_of(1), Some(D64::new(1, 0)));
    assert_eq!(price.pct_of(-10), Some(D64::new(-10, 0)));
}

#[test]
fn bps_of_i32() {
    type D32 = Decimal<i32, 4>;
    let price = D32::new(100, 0);
    assert_eq!(price.bps_of(5), Some(D32::new(0, 500)));
}

#[test]
fn bps_of_i128() {
    let price = D96::new(100, 0);
    let result = price.bps_of(5).unwrap();
    assert_eq!(result.to_raw(), 100_i128 * 1_000_000_000_000 * 5 / 10000);
}

// ============================================================================
// shift_bps / shift_pct
// ============================================================================

#[test]
fn shift_bps_basic() {
    let price = D64::new(100, 0);
    // shift by +5 bps: 100 * (10000 + 5) / 10000 = 100.05
    assert_eq!(price.shift_bps(5), Some(D64::new(100, 5_000_000)));
    // shift by 0 bps = identity
    assert_eq!(price.shift_bps(0), Some(price));
}

#[test]
fn shift_pct_basic() {
    let price = D64::new(100, 0);
    assert_eq!(price.shift_pct(10), Some(D64::new(110, 0)));
    assert_eq!(price.shift_pct(-10), Some(D64::new(90, 0)));
    assert_eq!(price.shift_pct(0), Some(price));
}

#[test]
fn shift_bps_overflow() {
    assert!(D64::MAX.shift_bps(10000).is_none());
}

// ============================================================================
// bps_diff / pct_diff
// ============================================================================

#[test]
fn bps_diff_basic() {
    let a = D64::new(100, 50_000_000); // 100.50
    let b = D64::new(100, 0); // 100.00
    // (100.50 - 100.00) * 10000 / 100.00 = 50 bps
    assert_eq!(a.bps_diff(b), Some(D64::new(50, 0)));
}

#[test]
fn bps_diff_zero_divisor() {
    assert!(D64::ONE.bps_diff(D64::ZERO).is_none());
}

#[test]
fn bps_diff_by_custom_divisor() {
    let ask = D64::new(101, 0);
    let bid = D64::new(100, 0);
    let mid = D64::new(100, 50_000_000);
    let result = ask.bps_diff_by(bid, mid).unwrap();
    // (101 - 100) * 10000 / 100.5 ≈ 99.50 bps
    assert!(result.to_raw() > 0);
}

#[test]
fn pct_diff_basic() {
    let a = D64::new(110, 0);
    let b = D64::new(100, 0);
    // (110 - 100) * 100 / 100 = 10%
    assert_eq!(a.pct_diff(b), Some(D64::new(10, 0)));
}

// ============================================================================
// tick_diff / add_ticks / is_tick_aligned
// ============================================================================

#[test]
fn tick_diff_basic() {
    let tick = D64::new(0, 1_000_000); // 0.01
    assert_eq!(
        D64::new(100, 50_000_000).tick_diff(D64::new(100, 0), tick),
        Some(50)
    );
}

#[test]
fn tick_diff_self() {
    let tick = D64::new(0, 1_000_000);
    assert_eq!(D64::ONE.tick_diff(D64::ONE, tick), Some(0));
}

#[test]
#[should_panic(expected = "tick must be positive")]
fn tick_diff_zero_tick() {
    let _ = D64::ONE.tick_diff(D64::ZERO, D64::ZERO);
}

#[test]
fn add_ticks_basic() {
    let tick = D64::new(0, 1_000_000); // 0.01
    assert_eq!(
        D64::new(100, 0).add_ticks(5, tick),
        Some(D64::new(100, 5_000_000))
    );
    assert_eq!(
        D64::new(100, 0).add_ticks(-3, tick),
        Some(D64::new(99, 97_000_000))
    );
}

#[test]
fn add_ticks_zero() {
    let tick = D64::new(0, 1_000_000);
    assert_eq!(D64::new(100, 0).add_ticks(0, tick), Some(D64::new(100, 0)));
}

#[test]
fn is_tick_aligned_basic() {
    let tick = D64::new(0, 1_000_000); // 0.01
    assert!(D64::new(100, 50_000_000).is_tick_aligned(tick));
    assert!(!D64::new(100, 5_500_000).is_tick_aligned(tick)); // 100.055 not on 0.01 grid
}

#[test]
fn is_tick_aligned_zero() {
    let tick = D64::new(0, 1_000_000);
    assert!(D64::ZERO.is_tick_aligned(tick));
}

// ============================================================================
// within_bps / within_ticks
// ============================================================================

#[test]
fn within_bps_basic() {
    let a = D64::new(100, 5_000_000); // 100.05
    let b = D64::new(100, 0); // 100.00
    // |100.05 - 100| = 0.05. |100| * 10 / 10000 = 0.10. 0.05 <= 0.10 → true
    assert!(a.within_bps(b, 10));
    // |101 - 100| = 1. |100| * 10 / 10000 = 0.10. 1 > 0.10 → false
    assert!(!D64::new(101, 0).within_bps(b, 10));
}

#[test]
fn within_bps_zero_tolerance() {
    assert!(D64::ONE.within_bps(D64::ONE, 0)); // same value, 0 tolerance
    assert!(!D64::TWO.within_bps(D64::ONE, 0)); // different, 0 tolerance
}

#[test]
fn within_bps_zero_reference() {
    // |self| <= |0| * bps / 10000 = 0, so only self == 0 passes
    assert!(D64::ZERO.within_bps(D64::ZERO, 100));
    assert!(!D64::ONE.within_bps(D64::ZERO, 100));
}

#[test]
fn within_ticks_basic() {
    let tick = D64::new(0, 1_000_000); // 0.01
    // 3 ticks away, tolerance = 5
    assert!(D64::new(100, 3_000_000).within_ticks(D64::new(100, 0), 5, tick));
    // 7 ticks away, tolerance = 5
    assert!(!D64::new(100, 7_000_000).within_ticks(D64::new(100, 0), 5, tick));
}

// ============================================================================
// round_bps / floor_bps / ceil_bps
// ============================================================================

#[test]
fn round_bps_basic() {
    let price = D64::new(1, 23_460_000); // 1.2346
    // Round to nearest 5 bps = 0.0005
    let tick_5bps = D64::new(0, 50_000); // 0.0005
    // Expected: same as round_to_tick with 5bps tick
    assert_eq!(price.round_bps(5), price.round_to_tick(tick_5bps));
}

#[test]
fn floor_bps_basic() {
    let price = D64::new(1, 23_460_000); // 1.2346
    let tick_5bps = D64::new(0, 50_000);
    assert_eq!(price.floor_bps(5), price.floor_to_tick(tick_5bps));
}

#[test]
fn ceil_bps_basic() {
    let price = D64::new(1, 23_460_000); // 1.2346
    let tick_5bps = D64::new(0, 50_000);
    assert_eq!(price.ceil_bps(5), price.ceil_to_tick(tick_5bps));
}

#[test]
fn round_bps_zero_returns_none() {
    assert!(D64::ONE.round_bps(0).is_none());
}

#[test]
fn round_bps_one() {
    let price = D64::new(1, 23_460_000); // 1.2346
    let tick_1bp = D64::new(0, 10_000); // 0.0001
    assert_eq!(price.round_bps(1), price.round_to_tick(tick_1bp));
}

// ============================================================================
// Cross-backing: i32
// ============================================================================

mod i32_financial {
    use nexus_decimal::Decimal;
    type D32 = Decimal<i32, 4>;

    #[test]
    fn shift_bps() {
        let price = D32::new(100, 0);
        assert_eq!(price.shift_bps(5), Some(D32::new(100, 500)));
    }

    #[test]
    fn add_ticks() {
        let tick = D32::new(0, 1); // 0.0001
        assert_eq!(D32::new(1, 0).add_ticks(5, tick), Some(D32::new(1, 5)));
    }

    #[test]
    fn tick_diff() {
        let tick = D32::new(0, 1);
        assert_eq!(D32::new(1, 5).tick_diff(D32::new(1, 0), tick), Some(5));
    }

    #[test]
    fn within_bps() {
        let a = D32::new(100, 5);
        let b = D32::new(100, 0);
        assert!(a.within_bps(b, 10));
    }
}

// ============================================================================
// Cross-backing: i128
// ============================================================================

mod i128_financial {
    use nexus_decimal::Decimal;
    type D128 = Decimal<i128, 18>;

    #[test]
    fn bps_of() {
        let price = D128::new(100, 0);
        let result = price.bps_of(5).unwrap();
        // 100 * 5 / 10000 = 0.05
        let expected = D128::new(0, 50_000_000_000_000_000);
        assert_eq!(result, expected);
    }

    #[test]
    fn shift_bps() {
        let price = D128::new(100, 0);
        let result = price.shift_bps(5).unwrap();
        let expected = D128::new(100, 50_000_000_000_000_000);
        assert_eq!(result, expected);
    }

    #[test]
    fn bps_diff() {
        let a = D128::new(100, 500_000_000_000_000_000);
        let b = D128::new(100, 0);
        let result = a.bps_diff(b).unwrap();
        assert_eq!(result, D128::new(50, 0));
    }

    #[test]
    fn add_ticks() {
        let tick = D128::new(0, 10_000_000_000_000_000); // 0.01
        assert_eq!(
            D128::new(100, 0).add_ticks(5, tick),
            Some(D128::new(100, 50_000_000_000_000_000))
        );
    }

    #[test]
    fn within_bps() {
        let a = D128::new(100, 50_000_000_000_000_000);
        let b = D128::new(100, 0);
        assert!(a.within_bps(b, 10));
    }
}
