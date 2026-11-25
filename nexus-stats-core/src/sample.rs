//! The numeric types the generic monitors accept.
//!
//! A monitor whose algorithm is the same over several numeric types is one
//! generic type, `WindowedMax<V, T>`, `PeakHold<T>`, `ZScoreNorm<T>`, bounded by
//! one of the sealed traits here. The traits are implemented for exactly the
//! supported primitive types and cannot be implemented outside this crate;
//! you name them only as bounds (`fn f<T: Sample>(p: &mut PeakHold<T>)`),
//! never implement them. Where a method exists for one type only (a float
//! `checked_update`, say), it is implemented for that instantiation and
//! documented on it.

use core::fmt::Debug;
use core::ops::{Add, Sub};

mod private {
    pub trait Sealed {}
    impl Sealed for f64 {}
    impl Sealed for f32 {}
    impl Sealed for i64 {}
}

/// A sample type for the comparison, extremum and timing monitors:
/// `f64` or `i64`.
///
/// Sealed: implemented for `f64` and `i64` here and nowhere else. It appears
/// as the bound on generic monitors such as
/// `WindowedMax<V, T>`, and that bound is the only
/// place a caller writes it.
pub trait Sample:
    Copy + PartialOrd + Debug + Add<Output = Self> + Sub<Output = Self> + private::Sealed + 'static
{
    /// Additive identity.
    const ZERO: Self;
    /// The lowest value: the starting point of a running maximum.
    const MIN: Self;
    /// The highest value: the starting point of a running minimum.
    const MAX: Self;

    /// Whether the value is finite. Always true for integers; used by shared
    /// constructors to validate configuration.
    fn is_finite(self) -> bool;

    /// Whether the value is a NaN. Never true for integers.
    fn is_nan(self) -> bool;

    /// The absolute value. `i64::MIN` saturates to `i64::MAX`.
    fn magnitude(self) -> Self;

    /// Whether `self` lies more than `threshold` away from `other`, exactly:
    /// `|self - other| > threshold`, computed without overflow for integers.
    fn further_than(self, other: Self, threshold: Self) -> bool;

    /// `self` clamped to `[lo, hi]` as `max(lo).min(hi)`: no `lo <= hi`
    /// assertion, so floats compile to a bare `maxsd`/`minsd` pair.
    fn clamp_to(self, lo: Self, hi: Self) -> Self;

    /// The value halfway between `self` and `other`, without overflow.
    fn midpoint(self, other: Self) -> Self;

    /// The point a fraction `t` of the way from `self` to `hi`, for
    /// `self <= hi` and `t` in `(0, 1)`: the interpolation step of the
    /// Hyndman-Fan type 7 quantile. At `t = 0.5` it is exactly
    /// [`midpoint`](Self::midpoint).
    ///
    /// Floats use NumPy's two-sided form, and R's `(1 - t) * self + t * hi`
    /// where `hi - self` is not finite (an infinite neighbor, or a spread
    /// past `f64::MAX`), so an infinity on one side is returned instead of
    /// NaN. Integers take `t * (hi - self)` exactly, for any spread, and
    /// round to the nearest value, ties toward zero, as `midpoint` does.
    fn lerp(self, hi: Self, t: f64) -> Self;

    /// `self - other`. Integers saturate at the type's bounds, so a
    /// difference of sentinel-sized values clamps where plain `-` would
    /// overflow; floats subtract as usual.
    fn sat_sub(self, other: Self) -> Self;

    /// `self + other`, saturating for integers as [`sat_sub`](Self::sat_sub).
    fn sat_add(self, other: Self) -> Self;

    /// The value as `f64` (exact for `f64`, rounded for large `i64`).
    fn to_f64(self) -> f64;

    /// `PeakHold<T>` decay parameter: a multiplicative rate for floats,
    /// nothing for integers (an integer peak drops to the current sample).
    #[doc(hidden)]
    type Decay: Copy + Debug;
    /// Applies one step of decay to `peak` after the hold expired.
    #[doc(hidden)]
    fn decay(peak: Self, decay: Self::Decay, sample: Self) -> Self;
}

impl Sample for f64 {
    const ZERO: Self = 0.0;
    const MIN: Self = f64::MIN;
    const MAX: Self = f64::MAX;

    #[inline]
    fn is_finite(self) -> bool {
        f64::is_finite(self)
    }

    #[inline]
    fn is_nan(self) -> bool {
        f64::is_nan(self)
    }

    #[inline]
    fn magnitude(self) -> f64 {
        self.abs()
    }

    #[inline]
    fn further_than(self, other: Self, threshold: Self) -> bool {
        (self - other).abs() > threshold
    }

    #[inline]
    fn clamp_to(self, lo: Self, hi: Self) -> Self {
        self.max(lo).min(hi)
    }

    #[inline]
    fn midpoint(self, other: Self) -> Self {
        f64::midpoint(self, other)
    }

    // Unfused, as NumPy computes it, so the results match NumPy's bit for bit.
    #[inline]
    #[allow(clippy::suboptimal_flops)]
    fn lerp(self, hi: Self, t: f64) -> Self {
        if t == 0.5 {
            return f64::midpoint(self, hi);
        }
        let diff = hi - self;
        if diff.is_finite() {
            // NumPy's `_lerp`: from the nearer end.
            if t < 0.5 {
                self + diff * t
            } else {
                hi - diff * (1.0 - t)
            }
        } else {
            (1.0 - t) * self + t * hi
        }
    }

    #[inline]
    fn sat_sub(self, other: Self) -> Self {
        self - other
    }

    #[inline]
    fn sat_add(self, other: Self) -> Self {
        self + other
    }

    #[inline]
    fn to_f64(self) -> f64 {
        self
    }

    type Decay = f64;
    #[inline]
    fn decay(peak: f64, rate: f64, _sample: f64) -> f64 {
        peak * rate
    }
}

impl Sample for i64 {
    const ZERO: Self = 0;
    const MIN: Self = i64::MIN;
    const MAX: Self = i64::MAX;

    #[inline]
    fn is_finite(self) -> bool {
        true
    }

    #[inline]
    fn is_nan(self) -> bool {
        false
    }

    #[inline]
    fn magnitude(self) -> i64 {
        self.saturating_abs()
    }

    #[inline]
    fn further_than(self, other: Self, threshold: Self) -> bool {
        // `threshold` is validated non-negative by every constructor that
        // stores one; a negative threshold would compare as a huge u64.
        self.abs_diff(other) > threshold.unsigned_abs()
    }

    #[inline]
    fn clamp_to(self, lo: Self, hi: Self) -> Self {
        Ord::max(self, lo).min(hi)
    }

    #[inline]
    fn midpoint(self, other: Self) -> Self {
        i64::midpoint(self, other)
    }

    #[inline]
    fn lerp(self, hi: Self, t: f64) -> Self {
        // `t` is exactly `mantissa * 2^-shift`, and `hi >= self`, so
        // `t * (hi - self)` is exact in 128 bits: its integer part is the
        // step from `self`, its fraction decides the rounding.
        let bits = t.to_bits();
        let exponent = ((bits >> 52) & 0x7ff) as u32;
        let (mantissa, shift) = if exponent == 0 {
            (bits & ((1 << 52) - 1), 1074)
        } else {
            (bits & ((1 << 52) - 1) | (1 << 52), 1075 - exponent)
        };
        let product = u128::from(mantissa) * u128::from(hi.wrapping_sub(self) as u64);
        let (step, rem, half) = if shift >= 128 {
            (0, product, u128::MAX)
        } else {
            (
                product >> shift,
                product & ((1 << shift) - 1),
                1 << (shift - 1),
            )
        };
        // `step < hi - self` because `t < 1`, so neither add overflows.
        let floor = self.wrapping_add(step as i64);
        floor + i64::from(rem > half || (rem == half && floor < 0))
    }

    #[inline]
    fn sat_sub(self, other: Self) -> Self {
        self.saturating_sub(other)
    }

    #[inline]
    fn sat_add(self, other: Self) -> Self {
        self.saturating_add(other)
    }

    #[inline]
    #[allow(clippy::cast_precision_loss)]
    fn to_f64(self) -> f64 {
        self as f64
    }

    type Decay = ();
    #[inline]
    fn decay(_peak: i64, (): (), sample: i64) -> i64 {
        sample
    }
}

/// A floating-point sample type for the normalizers: `f64` or `f32`.
///
/// Sealed. `f32` exists for one reason: a normalized feature vector that
/// feeds an `f32` inference model. The normalizers take and return `T` but
/// accumulate in `f64`, so `f32` is a boundary type, never an accumulator.
pub trait Float:
    Copy + PartialOrd + Debug + Add<Output = Self> + Sub<Output = Self> + private::Sealed + 'static
{
    /// Whether the value is finite.
    fn is_finite(self) -> bool;
    /// Whether the value is NaN.
    fn is_nan(self) -> bool;
    /// Widens to `f64`, exactly.
    fn to_f64(self) -> f64;
    /// Narrows from `f64` (rounding for `f32`).
    fn from_f64(x: f64) -> Self;
}

impl Float for f64 {
    #[inline]
    fn is_finite(self) -> bool {
        f64::is_finite(self)
    }
    #[inline]
    fn is_nan(self) -> bool {
        f64::is_nan(self)
    }
    #[inline]
    fn to_f64(self) -> f64 {
        self
    }
    #[inline]
    fn from_f64(x: f64) -> Self {
        x
    }
}

impl Float for f32 {
    #[inline]
    fn is_finite(self) -> bool {
        f32::is_finite(self)
    }
    #[inline]
    fn is_nan(self) -> bool {
        f32::is_nan(self)
    }
    #[inline]
    fn to_f64(self) -> f64 {
        f64::from(self)
    }
    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    fn from_f64(x: f64) -> Self {
        x as f32
    }
}
#[cfg(test)]
#[allow(clippy::suboptimal_flops)]
mod lerp_tests {
    use super::Sample;

    #[test]
    fn half_is_the_midpoint() {
        for (lo, hi) in [(0.1, 0.3), (1.0, 1.0 + 4.0 * f64::EPSILON), (-7.5, 1e300)] {
            assert_eq!(Sample::lerp(lo, hi, 0.5), f64::midpoint(lo, hi));
        }
        for (lo, hi) in [
            (-3, 0),
            (-2, -1),
            (1, 2),
            (i64::MIN, i64::MAX),
            (0, (1 << 53) + 1),
        ] {
            assert_eq!(Sample::lerp(lo, hi, 0.5), i64::midpoint(lo, hi));
        }
    }

    #[test]
    fn float_follows_numpy_from_the_nearer_end() {
        let (lo, hi) = (0.1_f64, 0.7_f64);
        assert_eq!(Sample::lerp(lo, hi, 0.25), lo + (hi - lo) * 0.25);
        assert_eq!(Sample::lerp(lo, hi, 0.75), hi - (hi - lo) * 0.25);
    }

    #[test]
    fn float_keeps_a_one_sided_infinity() {
        assert_eq!(Sample::lerp(1.0, f64::INFINITY, 0.25), f64::INFINITY);
        assert_eq!(
            Sample::lerp(f64::NEG_INFINITY, 1.0, 0.75),
            f64::NEG_INFINITY
        );
        assert_eq!(
            Sample::lerp(f64::INFINITY, f64::INFINITY, 0.25),
            f64::INFINITY
        );
        assert!(Sample::lerp(f64::NEG_INFINITY, f64::INFINITY, 0.25).is_nan());
        let spread = Sample::lerp(-f64::MAX, f64::MAX, 0.25);
        assert!(spread.is_finite() && spread < 0.0);
    }

    #[test]
    fn integer_rounds_to_nearest_ties_toward_zero() {
        assert_eq!(Sample::lerp(0_i64, 10, 0.26), 3);
        assert_eq!(Sample::lerp(0_i64, 10, 0.24), 2);
        assert_eq!(Sample::lerp(0_i64, 2, 0.25), 0);
        assert_eq!(Sample::lerp(-2_i64, 0, 0.25), -1);
        assert_eq!(Sample::lerp(-4_i64, 0, 0.375), -2);
        // `0.999` is not exact in binary. The expected value is for its
        // binary value, worked out with exact rational arithmetic.
        assert_eq!(
            Sample::lerp(i64::MIN, i64::MAX, 0.999),
            9_204_925_292_781_066_239
        );
    }
}
