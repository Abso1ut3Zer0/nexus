/// Validates that a float value is finite (not NaN, not Inf).
/// Returns `Err(DataError)` with the appropriate variant if invalid.
/// Used at the top of every update method that accepts float input.
macro_rules! check_finite {
    ($val:expr) => {
        if !$val.is_finite() {
            return Err(if $val.is_nan() {
                crate::DataError::NotANumber
            } else {
                crate::DataError::Infinite
            });
        }
    };
}

/// Validates that a float value is finite (not NaN, not Inf).
///
/// Returns `Err(DataError::NotANumber)` for NaN, `Err(DataError::Infinite)`
/// for infinity, `Ok(())` for finite values.
#[doc(hidden)]
#[inline]
pub fn check_finite(val: f64) -> Result<(), crate::DataError> {
    if !val.is_finite() {
        return Err(if val.is_nan() {
            crate::DataError::NotANumber
        } else {
            crate::DataError::Infinite
        });
    }
    Ok(())
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
