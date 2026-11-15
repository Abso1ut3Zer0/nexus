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

/// Trait providing `fma` (fused multiply-add) across all feature configurations.
///
/// With `std`: uses hardware FMA intrinsic.
/// With `libm`: uses `libm::fma` / `libm::fmaf`.
/// Without either: falls back to `a * b + c` (no fusion, but correct).
#[doc(hidden)]
pub trait MulAdd {
    /// Fused multiply-add: `self * b + c`.
    fn fma(self, b: Self, c: Self) -> Self;
}

impl MulAdd for f64 {
    #[inline]
    fn fma(self, b: f64, c: f64) -> f64 {
        #[cfg(feature = "std")]
        {
            self.mul_add(b, c)
        }
        #[cfg(all(not(feature = "std"), feature = "libm"))]
        {
            libm::fma(self, b, c)
        }
        #[cfg(not(any(feature = "std", feature = "libm")))]
        {
            self * b + c
        }
    }
}

impl MulAdd for f32 {
    #[inline]
    fn fma(self, b: f32, c: f32) -> f32 {
        #[cfg(feature = "std")]
        {
            self.mul_add(b, c)
        }
        #[cfg(all(not(feature = "std"), feature = "libm"))]
        {
            libm::fmaf(self, b, c)
        }
        #[cfg(not(any(feature = "std", feature = "libm")))]
        {
            self * b + c
        }
    }
}

#[cfg(test)]
mod tests {
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
