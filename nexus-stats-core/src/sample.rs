//! The numeric types the generic monitors accept.
//!
//! A monitor whose algorithm is the same over several numeric types is one
//! generic type, `WindowedMax<T>`, `PeakHold<T>`, `ZScoreNorm<T>`, bounded by
//! one of the sealed traits here. The traits are implemented for exactly the
//! supported primitive types and cannot be implemented outside this crate;
//! you name them only as bounds (`fn f<T: Sample>(w: &mut WindowedMax<T>)`),
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
/// `WindowedMax<T>`, and that bound is the only
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
