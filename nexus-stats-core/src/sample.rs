//! The numeric types the generic monitors accept.
//!
//! A monitor whose algorithm is the same over several numeric types is one
//! generic type, `Drawdown<T>`, `WindowedMax<T>`, `ZScoreNorm<T>`, bounded by
//! one of the sealed traits here. The traits are implemented for exactly the
//! supported primitive types and cannot be implemented outside this crate;
//! you name them only as bounds (`fn f<T: Sample>(d: &mut Drawdown<T>)`),
//! never implement them. Where a method's
//! signature differs by type (float `update` returns `Result` because it
//! rejects NaN and infinity; integer `update` cannot fail), the method is
//! implemented per instantiation and documented on it.

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
/// [`Drawdown<T>`](crate::monitoring::Drawdown), and that bound is the only
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

    /// Whether `self` lies more than `threshold` away from `other`, exactly:
    /// `|self - other| > threshold`, computed without overflow for integers.
    fn further_than(self, other: Self, threshold: Self) -> bool;

    /// `self` clamped to `[lo, hi]` as `max(lo).min(hi)`: no `lo <= hi`
    /// assertion, so floats compile to a bare `maxsd`/`minsd` pair.
    fn clamp_to(self, lo: Self, hi: Self) -> Self;

    /// The value halfway between `self` and `other`, without overflow.
    fn midpoint(self, other: Self) -> Self;

    /// The value as `f64` (exact for `f64`, rounded for large `i64`).
    fn to_f64(self) -> f64;

    /// Exponential smoother for this type: alpha-weighted for floats, the
    /// kernel-style fixed-point shift EMA for integers. Used by `Jitter<T>`.
    #[doc(hidden)]
    type Ema: EmaKernel<Self>;
    /// What configures the smoother: an alpha in (0, 1) for floats, a span
    /// (rounded to `2^k - 1`) for integers.
    #[doc(hidden)]
    type EmaConfig: Copy + Debug;
    /// Smoother configuration from a span, the one knob both types share.
    #[doc(hidden)]
    fn ema_config_from_span(span: u64) -> Self::EmaConfig;
    /// Name of the smoother knob in error messages: `alpha` or `span`.
    #[doc(hidden)]
    const EMA_CONFIG_NAME: &'static str;

    /// `PeakHold<T>` decay parameter: a multiplicative rate for floats,
    /// nothing for integers (an integer peak drops to the current sample).
    #[doc(hidden)]
    type Decay: Copy + Debug;
    /// Applies one step of decay to `peak` after the hold expired.
    #[doc(hidden)]
    fn decay(peak: Self, decay: Self::Decay, sample: Self) -> Self;
}

/// The exponential smoother behind `Jitter<T>`. Hidden: an implementation
/// detail of the sealed sample types.
#[doc(hidden)]
pub trait EmaKernel<T>: Copy + Debug {
    /// Builds a smoother. `Err` if the configuration is invalid.
    fn new(config: T::EmaConfig) -> Result<Self, crate::ConfigError>
    where
        T: Sample;
    /// Folds a sample in: the first sample seeds the smoother.
    fn fold(&mut self, x: T);
    /// Seeds the smoother with a value, as if it had converged there.
    fn seed(&mut self, x: T);
    /// Current smoothed value (zero before the first sample).
    fn value(&self) -> T;
    /// Forgets everything; configuration is kept.
    fn reset(&mut self);
}

/// Alpha-weighted EMA for floats.
#[doc(hidden)]
#[derive(Debug, Clone, Copy)]
pub struct AlphaEma {
    alpha: f64,
    one_minus_alpha: f64,
    value: f64,
    initialized: bool,
}

impl EmaKernel<f64> for AlphaEma {
    #[inline]
    fn new(alpha: f64) -> Result<Self, crate::ConfigError> {
        if !(alpha > 0.0 && alpha < 1.0) {
            return Err(crate::ConfigError::Invalid("alpha must be in (0, 1)"));
        }
        Ok(Self {
            alpha,
            one_minus_alpha: 1.0 - alpha,
            value: 0.0,
            initialized: false,
        })
    }
    #[inline]
    fn fold(&mut self, x: f64) {
        if self.initialized {
            self.value = crate::math::MulAdd::fma(self.alpha, x, self.one_minus_alpha * self.value);
        } else {
            self.value = x;
            self.initialized = true;
        }
    }
    #[inline]
    fn seed(&mut self, x: f64) {
        self.value = x;
        self.initialized = true;
    }
    #[inline]
    fn value(&self) -> f64 {
        self.value
    }
    #[inline]
    fn reset(&mut self) {
        self.value = 0.0;
        self.initialized = false;
    }
}

/// Fixed-point shift EMA for integers (`acc += (x << k - acc) >> k`), as in
/// the kernel's RTT estimators. The span is rounded to `2^k - 1`.
#[doc(hidden)]
#[derive(Debug, Clone, Copy)]
pub struct ShiftEma {
    acc: i128,
    shift: u32,
    /// The span actually used, `2^k - 1`.
    pub span: u64,
    initialized: bool,
}

impl EmaKernel<i64> for ShiftEma {
    #[inline]
    fn new(span: u64) -> Result<Self, crate::ConfigError> {
        if span < 1 {
            return Err(crate::ConfigError::Invalid("span must be >= 1"));
        }
        let effective = crate::smoothing::ema::next_power_of_two_minus_one(span);
        Ok(Self {
            acc: 0,
            shift: crate::smoothing::ema::log2_of_span_plus_one(effective),
            span: effective,
            initialized: false,
        })
    }
    #[inline]
    fn fold(&mut self, x: i64) {
        let shifted = i128::from(x) << self.shift;
        if self.initialized {
            self.acc += (shifted - self.acc) >> self.shift;
        } else {
            self.acc = shifted;
            self.initialized = true;
        }
    }
    #[inline]
    fn seed(&mut self, x: i64) {
        self.acc = i128::from(x) << self.shift;
        self.initialized = true;
    }
    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    fn value(&self) -> i64 {
        (self.acc >> self.shift) as i64
    }
    #[inline]
    fn reset(&mut self) {
        self.acc = 0;
        self.initialized = false;
    }
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
    fn to_f64(self) -> f64 {
        self
    }

    type Ema = AlphaEma;
    type EmaConfig = f64;
    const EMA_CONFIG_NAME: &'static str = "alpha";
    #[inline]
    #[allow(clippy::cast_precision_loss)]
    fn ema_config_from_span(span: u64) -> f64 {
        2.0 / (span as f64 + 1.0)
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
    #[allow(clippy::cast_precision_loss)]
    fn to_f64(self) -> f64 {
        self as f64
    }

    type Ema = ShiftEma;
    type EmaConfig = u64;
    const EMA_CONFIG_NAME: &'static str = "span";
    #[inline]
    fn ema_config_from_span(span: u64) -> u64 {
        span
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
