/// Returns `Err(DataError::NotANumber)` / `Err(DataError::Infinite)` from the
/// enclosing function when a float input is not finite. The first line of
/// every `update` that takes a float, in this crate and the subcrates.
#[doc(hidden)]
#[macro_export]
macro_rules! check_finite {
    ($val:expr) => {
        if !$val.is_finite() {
            return Err(if $val.is_nan() {
                $crate::DataError::NotANumber
            } else {
                $crate::DataError::Infinite
            });
        }
    };
}

/// Returns `Ok` if `value` is a number no larger in magnitude than `limit`.
///
/// # Errors
///
/// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `value` is
///   NaN.
/// - [`DataError::Infinite`](crate::DataError::Infinite) if `value` is
///   infinite.
/// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if `value` is
///   finite and larger in magnitude than `limit`.
#[inline]
pub fn check_input(value: f64, limit: f64) -> Result<(), crate::DataError> {
    // Cold: naming the reason stays off the accepted path.
    #[cold]
    fn refusal(value: f64) -> crate::DataError {
        if value.is_nan() {
            crate::DataError::NotANumber
        } else if value.is_infinite() {
            crate::DataError::Infinite
        } else {
            crate::DataError::OutOfRange
        }
    }

    // NaN and infinity fail this comparison too, so one test accepts.
    if value.abs() <= limit {
        return Ok(());
    }
    Err(refusal(value))
}

/// `2^64`: more samples than a `u64` count can hold.
const TWO_POW_64: f64 = 18_446_744_073_709_551_616.0;

/// The largest value one powered term may reach: `1e240`.
///
/// Our choice, far below the overflow threshold `f64::MAX` (written Ω in
/// the floating-point literature). A difference of two inputs can be twice
/// an input, so its fourth power is `2^4` times larger; `2^64` terms that
/// size still sum below the threshold.
pub const POWER_LIMIT: f64 = 1e240;
const _: () = assert!(TWO_POW_64 * 16.0 * POWER_LIMIT < f64::MAX);

/// The largest input whose square stays within [`POWER_LIMIT`]: `1e120`.
pub const LIMIT_FOR_SQUARES: f64 = 1e120;
const _: () = assert!(LIMIT_FOR_SQUARES * LIMIT_FOR_SQUARES <= POWER_LIMIT);

/// A divisor below this has lost precision to underflow.
///
/// The smallest normal number over machine epsilon: the form of LAPACK's
/// `SMLNUM` (safe minimum over precision), which it uses to guard a
/// division.
pub const SMALLEST_DIVISOR: f64 = f64::MIN_POSITIVE / f64::EPSILON;

/// The variance that rounding alone produces around `mean`:
/// `(f64::EPSILON * mean)^2`.
///
/// A variance at or below it means the values are equal to within
/// rounding. This is the test SciPy's `skew` and `kurtosis` use.
#[must_use]
pub const fn rounding_variance(mean: f64) -> f64 {
    let rounding = f64::EPSILON * mean;
    rounding * rounding
}

/// f32 variant of [`check_finite`].
#[doc(hidden)]
#[inline]
pub fn check_finite_f32(val: f32) -> Result<(), crate::DataError> {
    if !val.is_finite() {
        return Err(if val.is_nan() {
            crate::DataError::NotANumber
        } else {
            crate::DataError::Infinite
        });
    }
    Ok(())
}

/// Square root.
///
/// Requires `std` or `libm` feature. Types using this (`std_dev()`,
/// `ShiryaevRoberts`) won't compile without one of these features.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn sqrt(x: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        x.sqrt()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::sqrt(x)
    }
}

/// Exponential function.
///
/// Requires `std` or `libm` feature. Types using this (`ShiryaevRoberts`,
/// `halflife()` constructors) won't compile without one of these features.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn exp(x: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        x.exp()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::exp(x)
    }
}

/// Natural logarithm.
///
/// Requires `std` or `libm` feature. Types using this (`Entropy`,
/// `TransferEntropy`) won't compile without one of these features.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn ln(x: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        x.ln()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::log(x)
    }
}

/// `x` raised to the power `y`.
///
/// Requires `std` or `libm` feature.
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn powf(x: f64, y: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        x.powf(y)
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::pow(x, y)
    }
}

/// Natural logarithm (f32).
///
/// Requires `std` or `libm` feature.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn ln_f32(x: f32) -> f32 {
    #[cfg(feature = "std")]
    {
        x.ln()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::logf(x)
    }
}

/// Exponential function (f32).
///
/// Requires `std` or `libm` feature.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn exp_f32(x: f32) -> f32 {
    #[cfg(feature = "std")]
    {
        x.exp()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::expf(x)
    }
}

/// Log-gamma function via Lanczos approximation (g=7).
///
/// Accurate to ~15 digits for x > 0.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[allow(
    clippy::excessive_precision,
    clippy::unreadable_literal,
    clippy::suboptimal_flops
)]
pub fn ln_gamma(x: f64) -> f64 {
    const G: f64 = 7.5;
    const C: [f64; 9] = [
        0.99999999999980993,
        676.5203681218851,
        -1259.1392167224028,
        771.32342877765313,
        -176.61502916214059,
        12.507343278686905,
        -0.13857109526572012,
        9.9843695780195716e-6,
        1.5056327351493116e-7,
    ];

    let x = x - 1.0;
    let mut sum = C[0];
    for i in 1..9 {
        sum += C[i] / (x + i as f64);
    }
    let t = x + G;
    0.5 * ln(2.0 * core::f64::consts::PI) + (x + 0.5) * ln(t) - t + ln(sum)
}

/// Multiply-add: `self * b + c`, fused when the target does it in one
/// instruction.
///
/// Rust's `f64::mul_add` is an FMA instruction only when the target has the
/// feature (x86_64 with `-C target-cpu=native` or `-C target-feature=+fma`;
/// always on aarch64). Without it, LLVM lowers `mul_add` to a call into
/// compiler-builtins' software `fma`, which costs more than the arithmetic
/// it replaces. So this shim fuses when `std` is available and the target
/// has FMA, and otherwise computes `self * b + c` with two roundings. The
/// two differ in the last bit; neither path ever calls out.
#[doc(hidden)]
pub trait MulAdd {
    /// `self * b + c`, fused when the target has FMA.
    fn fma(self, b: Self, c: Self) -> Self;
}

#[cfg(all(feature = "std", any(target_feature = "fma", target_arch = "aarch64")))]
macro_rules! impl_mul_add {
    ($t:ty) => {
        impl MulAdd for $t {
            #[inline(always)]
            fn fma(self, b: $t, c: $t) -> $t {
                self.mul_add(b, c)
            }
        }
    };
}

#[cfg(not(all(feature = "std", any(target_feature = "fma", target_arch = "aarch64"))))]
macro_rules! impl_mul_add {
    ($t:ty) => {
        impl MulAdd for $t {
            // The lint's suggestion is the software-fma call this path exists
            // to avoid.
            #[allow(clippy::suboptimal_flops)]
            #[inline(always)]
            fn fma(self, b: $t, c: $t) -> $t {
                self * b + c
            }
        }
    };
}

impl_mul_add!(f64);
impl_mul_add!(f32);

/// `1.0` for `true`, `0.0` for `false`, as a conversion rather than a select:
/// a select between two float constants lowers to a jump on the predicate.
#[inline]
#[must_use]
pub fn indicator(b: bool) -> f64 {
    f64::from(u8::from(b))
}

/// EMA weight for a half-life of `halflife` samples: `1 - exp(-ln 2 / halflife)`.
///
/// The result is in `(0, 1)` for a positive finite `halflife`; builders reach
/// this through [`EwWeight::resolve`], which validates it first.
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
#[must_use]
pub fn alpha_from_halflife(halflife: f64) -> f64 {
    1.0 - exp(-core::f64::consts::LN_2 / halflife)
}

/// EMA weight for a span of `n` samples: `2 / (n + 1)`, the pandas `span`
/// convention. In `(0, 1)` for `n >= 2`.
#[inline]
#[must_use]
#[allow(clippy::cast_precision_loss)]
pub fn alpha_from_span(n: u64) -> f64 {
    2.0 / (n as f64 + 1.0)
}

/// How a builder was told its exponential weight: directly, as a half-life,
/// or as a span. Builders store the knob the caller set and resolve it in
/// `build`, so a bad value is reported under the name the caller used.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EwWeight {
    /// The weight itself, in `(0, 1)`.
    Alpha(f64),
    /// Samples for a weight to decay by half; positive and finite.
    #[cfg(any(feature = "std", feature = "libm"))]
    Halflife(f64),
    /// Pandas `span`; at least 2.
    Span(u64),
}

impl EwWeight {
    /// The smallest usable weight: half of machine epsilon.
    ///
    /// Our choice. Below it `1 - alpha` rounds to 1 and nothing is ever
    /// forgotten. The `halflife` knob already stops here, by rounding.
    const SMALLEST: f64 = f64::EPSILON / 2.0;

    /// The weight in `(0, 1)`.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` naming the knob that was set: `alpha` outside
    /// `(0, 1)`, a `halflife` that is not positive and finite, a `span`
    /// below 2, or any of the three giving a weight too small to use.
    pub fn resolve(self) -> Result<f64, crate::ConfigError> {
        let alpha = match self {
            Self::Alpha(a) => {
                if !in_unit_interval(a) {
                    return Err(crate::ConfigError::Invalid("alpha must be in (0, 1)"));
                }
                if a < Self::SMALLEST {
                    return Err(crate::ConfigError::Invalid(
                        "alpha is too small for a usable weight",
                    ));
                }
                a
            }
            #[cfg(any(feature = "std", feature = "libm"))]
            Self::Halflife(h) => {
                if !positive_finite(h) {
                    return Err(crate::ConfigError::Invalid(
                        "halflife must be positive and finite",
                    ));
                }
                // A half-life so short that `1 - exp(-x)` rounds to one, or
                // so long that it rounds to zero, has no usable weight.
                let alpha = alpha_from_halflife(h);
                if !in_unit_interval(alpha) {
                    return Err(crate::ConfigError::Invalid(
                        "halflife is too small or too large for a usable weight",
                    ));
                }
                alpha
            }
            Self::Span(n) => {
                if n < 2 {
                    return Err(crate::ConfigError::Invalid("span must be at least 2"));
                }
                let alpha = alpha_from_span(n);
                if alpha < Self::SMALLEST {
                    return Err(crate::ConfigError::Invalid(
                        "span is too large for a usable weight",
                    ));
                }
                alpha
            }
        };
        Ok(alpha)
    }
}

/// `z` such that `P(Z > z) = p` for a standard normal, for `p` in `(0, 0.5]`:
/// the Abramowitz & Stegun 26.2.23 rational approximation (|error| < 4.5e-4).
///
/// Used for the two-sided credible intervals (`p = (1 - confidence) / 2`).
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
#[must_use]
pub fn upper_tail_z(p: f64) -> f64 {
    let t = sqrt(-2.0 * ln(p));
    let num = 0.010_328f64.fma(t, 0.802_853).fma(t, 2.515_517);
    let den = 0.001_308f64.fma(t, 0.189_269).fma(t, 1.432_788).fma(t, 1.0);
    t - num / den
}

/// Dot product `Σ a[i] · b[i]` as one fused chain (`fma` per term).
///
/// `b` is indexed by `a`'s length: one bounds check up front, and the loop
/// count is `a.len()`. Pass the slice whose length the compiler can see
/// first (a caller's feature slice rather than a boxed weight vector), and
/// the loop unrolls to that length where it is a constant.
///
/// # Panics
///
/// If `b` is shorter than `a`.
#[inline]
#[must_use]
pub fn dot(a: &[f64], b: &[f64]) -> f64 {
    let b = &b[..a.len()];
    a.iter().zip(b).fold(0.0, |acc, (&x, &y)| x.fma(y, acc))
}

/// `y[i] += alpha · x[i]` for every `i` (BLAS `axpy`), fused per element.
///
/// `y` is indexed by `x`'s length, like [`dot`].
///
/// # Panics
///
/// If `y` is shorter than `x`.
#[inline]
pub fn axpy(alpha: f64, x: &[f64], y: &mut [f64]) {
    let y = &mut y[..x.len()];
    for (yi, &xi) in y.iter_mut().zip(x) {
        *yi = alpha.fma(xi, *yi);
    }
}

/// `true` for a finite value strictly greater than zero; `false` for NaN.
///
/// The builders' validation idiom: `x <= 0.0` is `false` for NaN and lets it
/// through, this does not.
#[inline]
#[must_use]
pub fn positive_finite(x: f64) -> bool {
    x.is_finite() && x > 0.0
}

/// `true` for a finite value greater than or equal to zero; `false` for NaN.
#[inline]
#[must_use]
pub fn nonnegative_finite(x: f64) -> bool {
    x.is_finite() && x >= 0.0
}

/// `true` for a value strictly inside `(0, 1)`; `false` for NaN.
#[inline]
#[must_use]
pub fn in_unit_interval(x: f64) -> bool {
    x > 0.0 && x < 1.0
}

#[cfg(test)]
mod tests {
    #[test]
    fn rounding_variance_is_epsilon_times_the_mean_squared() {
        let eps = f64::EPSILON;
        assert_eq!(super::rounding_variance(1.0), eps * eps);
        assert_eq!(super::rounding_variance(-1e6), (eps * 1e6) * (eps * 1e6));
        assert_eq!(super::rounding_variance(0.0), 0.0);

        // Usable where a type derives a constant of its own.
        const AT_TWO: f64 = super::rounding_variance(2.0);
        assert_eq!(AT_TWO, 4.0 * eps * eps);
    }

    #[test]
    fn a_weight_too_small_to_use_is_refused_under_every_knob() {
        use super::EwWeight::{Alpha, Span};
        use crate::ConfigError::Invalid;

        let smallest = f64::EPSILON / 2.0;
        assert_eq!(Alpha(smallest).resolve(), Ok(smallest));
        let too_small = Err(Invalid("alpha is too small for a usable weight"));
        assert_eq!(Alpha(smallest / 2.0).resolve(), too_small);
        assert_eq!(Alpha(5e-324).resolve(), too_small);

        assert!(Span(1 << 50).resolve().is_ok());
        assert_eq!(
            Span(u64::MAX).resolve(),
            Err(Invalid("span is too large for a usable weight"))
        );
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn a_halflife_too_long_to_use_is_refused() {
        use super::EwWeight::Halflife;
        use crate::ConfigError::Invalid;

        assert!(Halflife(10.0).resolve().is_ok());
        assert_eq!(
            Halflife(1e18).resolve(),
            Err(Invalid(
                "halflife is too small or too large for a usable weight"
            ))
        );
    }

    #[test]
    fn check_input_accepts_up_to_the_limit_and_names_each_refusal() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        // 5e-324 is the smallest subnormal.
        for accepted in [0.0, -0.0, 1.5, -1.5, 10.0, -10.0, 5e-324, -5e-324] {
            assert_eq!(super::check_input(accepted, 10.0), Ok(()), "{accepted}");
        }
        assert_eq!(super::check_input(f64::NAN, 10.0), Err(NotANumber));
        assert_eq!(super::check_input(f64::INFINITY, 10.0), Err(Infinite));
        assert_eq!(super::check_input(f64::NEG_INFINITY, 10.0), Err(Infinite));
        assert_eq!(super::check_input(10.000_001, 10.0), Err(OutOfRange));
        assert_eq!(super::check_input(-10.000_001, 10.0), Err(OutOfRange));
        assert_eq!(super::check_input(f64::MAX, 10.0), Err(OutOfRange));
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn powf_matches_integer_powers() {
        assert!((powf(2.0, 10.0) - 1024.0).abs() < 1e-9);
        assert!((powf(9.0, 0.5) - 3.0).abs() < 1e-12);
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    use super::*;

    #[test]
    #[cfg(any(feature = "std", feature = "libm"))]
    fn ln_gamma_factorial_values() {
        // Γ(1) = 1, so ln_gamma(1) = 0
        assert!((ln_gamma(1.0) - 0.0).abs() < 1e-12);
        // Γ(5) = 4! = 24, so ln_gamma(5) = ln(24)
        assert!((ln_gamma(5.0) - ln(24.0)).abs() < 1e-12);
        // Γ(1/2) = √π, so ln_gamma(0.5) = 0.5 * ln(π)
        assert!(
            0.5f64
                .mul_add(-ln(core::f64::consts::PI), ln_gamma(0.5))
                .abs()
                < 1e-12
        );
    }

    #[test]
    #[cfg(any(feature = "std", feature = "libm"))]
    fn ln_f32_matches_f64() {
        for &x in &[0.5f32, 1.0, 2.0, 10.0, 100.0] {
            let f32_result = ln_f32(x);
            let f64_result = ln(x as f64) as f32;
            assert!(
                (f32_result - f64_result).abs() < 1e-6,
                "ln_f32({x}) = {f32_result}, expected ≈ {f64_result}"
            );
        }
    }

    #[test]
    #[cfg(any(feature = "std", feature = "libm"))]
    fn exp_f32_matches_f64() {
        for &x in &[-2.0f32, -1.0, 0.0, 1.0, 2.0] {
            let f32_result = exp_f32(x);
            let f64_result = exp(x as f64) as f32;
            assert!(
                (f32_result - f64_result).abs() < 1e-5,
                "exp_f32({x}) = {f32_result}, expected ≈ {f64_result}"
            );
        }
    }
}
