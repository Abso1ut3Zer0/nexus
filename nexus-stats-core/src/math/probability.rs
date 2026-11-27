//! Quantiles of probability distributions that several crates use.
//!
//! A quantile is the value a distribution stays at or below with a given
//! probability. This module holds the ones shared across the stats crates.
//! A distribution with one crate's callers lives in that crate, in a
//! module of the same name (the gamma estimate is in
//! `nexus-stats-regression`).
//!
//! | Function | What it gives | SciPy's form |
//! |---|---|---|
//! | `normal_quantile` | the standard normal quantile | `scipy.stats.norm.ppf(p)` |
//!
//! Closed forms only, with no iteration and no table. Hidden from the
//! public docs: callers use an estimator's own methods.

// The polynomials keep the letters of their source.
#![allow(clippy::many_single_char_names)]

use crate::math::{MulAdd, ln, sqrt};

/// The value a standard normal variable is at most with probability `p`,
/// for `p` in `(0, 1)`. Negative below one half and positive above it.
///
/// This is `scipy.stats.norm.ppf(p)`, by Acklam's rational approximation.
/// With `q = p - 1/2` and `r = q^2`, in the middle of the range it is
///
/// ```text
/// z = q A(r) / (r B(r) + 1)
/// ```
///
/// and in a tail (`p < 0.02425`, mirrored above `1 - 0.02425`), with
/// `q = sqrt(-2 ln p)`,
///
/// ```text
/// z = C(q) / (q D(q) + 1)
/// ```
///
/// where `A`, `B`, `C` and `D` are the polynomials whose coefficients are
/// in the code.
/// Its relative error is below `1.2e-9`, and below `1.8e-9` for a
/// subnormal `p`.
#[allow(clippy::excessive_precision, clippy::unreadable_literal)]
#[must_use]
pub fn normal_quantile(p: f64) -> f64 {
    const A: [f64; 6] = [
        -3.969683028665376e+01,
        2.209460984245205e+02,
        -2.759285104469687e+02,
        1.383577518672690e+02,
        -3.066479806614716e+01,
        2.506628277459239e+00,
    ];
    const B: [f64; 5] = [
        -5.447609879822406e+01,
        1.615858368580409e+02,
        -1.556989798598866e+02,
        6.680131188771972e+01,
        -1.328068155288572e+01,
    ];
    const C: [f64; 6] = [
        -7.784894002430293e-03,
        -3.223964580411365e-01,
        -2.400758277161838e+00,
        -2.549732539343734e+00,
        4.374664141464968e+00,
        2.938163982698783e+00,
    ];
    const D: [f64; 4] = [
        7.784695709041462e-03,
        3.224671290700398e-01,
        2.445134137142996e+00,
        3.754408661907416e+00,
    ];
    /// Below this, and above its mirror, the tail form applies.
    const TAIL: f64 = 0.02425;

    if p > 1.0 - TAIL {
        return -normal_quantile(1.0 - p);
    }
    if p < TAIL {
        let q = sqrt(-2.0 * ln(p));
        return horner(&C, q) / horner(&D, q).fma(q, 1.0);
    }
    let q = p - 0.5;
    let r = q * q;
    horner(&A, r) * q / horner(&B, r).fma(r, 1.0)
}

/// The polynomial with `coefficients` from the highest power down, at `x`,
/// by Horner's rule: `((c0 x + c1) x + c2) x + ...`.
#[inline]
fn horner(coefficients: &[f64], x: f64) -> f64 {
    // PERF: one fused multiply-add per coefficient.
    coefficients.iter().fold(0.0, |sum, &c| sum.fma(x, c))
}

#[cfg(test)]
#[allow(clippy::unreadable_literal, clippy::excessive_precision)]
mod tests {
    use super::*;

    /// `(p, scipy.stats.norm.ppf(p))`
    const NORMAL_QUANTILES: [(f64, f64); 9] = [
        (1e-09, -5.9978070150076865),
        (1e-06, -4.753424308822899),
        (0.0005, -3.2905267314918945),
        (0.025, -1.9599639845400545),
        (0.3, -0.5244005127080409),
        (0.5, 0.0),
        (0.8, 0.8416212335729143),
        (0.975, 1.959963984540054),
        (0.999999, 4.753424308817087),
    ];
    fn relative_error(got: f64, want: f64) -> f64 {
        (got - want).abs() / want.abs()
    }

    #[test]
    fn the_normal_quantile_matches_scipy() {
        for (p, want) in NORMAL_QUANTILES {
            let got = normal_quantile(p);
            if want == 0.0 {
                assert!(got.abs() < 1e-15, "p {p}: {got}");
            } else {
                assert!(relative_error(got, want) < 1.2e-9, "p {p}: {got} vs {want}");
            }
        }
    }

    #[test]
    fn the_normal_quantile_is_odd_about_one_half() {
        // `p` values whose mirror `1 - p` is exact.
        for p in [
            0.5_f64.powi(30),
            0.5_f64.powi(10),
            0.015625,
            0.125,
            0.25,
            0.375,
        ] {
            assert_eq!(normal_quantile(1.0 - p), -normal_quantile(p), "p {p}");
        }
        assert_eq!(normal_quantile(0.5), 0.0);
    }
}
