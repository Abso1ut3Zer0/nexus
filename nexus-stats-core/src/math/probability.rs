//! Quantiles of the probability distributions the estimators use.
//!
//! A quantile is the value a distribution stays at or below with a given
//! probability. A 95% interval is the pair of quantiles that leave 2.5%
//! below and 2.5% above.
//!
//! Everything here is a closed form. Each is a few operations, with no
//! iteration, no search and no table. Nothing can fail to converge. These are estimates
//! built for streaming, where the counts are large. Each function states
//! how close it is, measured against a 40-digit reference.
//!
//! | Function | What it estimates | SciPy's exact form |
//! |---|---|---|
//! | `normal_quantile` | the standard normal quantile | `scipy.stats.norm.ppf(p)` |
//! | `gamma_quantile_approx` | the quantile of a `Gamma(shape, 1)` counted from below | `scipy.stats.gamma.ppf(p, shape)` |
//! | `gamma_quantile_upper_approx` | the same counted from above | `scipy.stats.gamma.isf(q, shape)` |
//!
//! The gamma functions take the shape only and assume a rate of one. For a
//! `Gamma(shape, rate)`, divide the quantile by the rate.
//!
//! There is no exact gamma quantile here, on purpose. The exact one needs
//! an iterative search over the incomplete gamma function, whose hard cases
//! are large shapes and extreme tails (SciPy's issue 26471, open in 2026,
//! is one about large shapes). Large shapes are where a streaming
//! estimator lives. The closed form is at its best there. For exact values
//! on a small sample, compute them offline with SciPy or R.
//!
//! These are internal: the estimators call them, and they are hidden from
//! the public docs.

// The formulas are written as their sources give them, letter for letter,
// and none of this is on a per-sample path.
#![allow(clippy::suboptimal_flops, clippy::many_single_char_names)]

use crate::math::{ln, sqrt};

/// The value a standard normal variable is at most with probability `p`,
/// for `p` in `(0, 1)`. Negative below one half and positive above it.
///
/// This is `scipy.stats.norm.ppf(p)`, by Acklam's rational approximation.
/// Its relative error is below `1.2e-9`, and below `1.8e-9` for a
/// subnormal `p`.
#[must_use]
#[allow(clippy::excessive_precision, clippy::unreadable_literal)]
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
        return horner(&C, q) / (horner(&D, q) * q + 1.0);
    }
    let q = p - 0.5;
    let r = q * q;
    horner(&A, r) * q / (horner(&B, r) * r + 1.0)
}

/// The polynomial with `coefficients` from the highest power down, at `x`.
#[inline]
fn horner(coefficients: &[f64], x: f64) -> f64 {
    coefficients.iter().fold(0.0, |sum, &c| sum * x + c)
}

/// An estimate of the value a `Gamma(shape, 1)` variable is at most with
/// probability `p`, by Wilson and Hilferty's closed form (1931).
///
/// It uses that the cube root of a gamma variable is close to normal. No
/// iteration, about five nanoseconds. Never below zero.
///
/// Every answer is a little off the exact quantile, by an amount that
/// shrinks as the shape grows. This is how far, as a fraction of the
/// value, for a tail of 0.025 (the lower end of a 95% interval) and of
/// 0.0005 (of a 99.9% one). It is a distance, not a rate of failure.
///
/// | Shape | At 95% | At 99.9% |
/// |---|---|---|
/// | 3 | 2.5% | 28% |
/// | 5 | 0.75% | 8.6% |
/// | 11 | 0.14% | 1.6% |
/// | 31 | 0.02% | 0.23% |
/// | 101 | 0.0023% | 0.031% |
/// | 1,001 | 6 in 10 million | 8 in a million |
/// | 10,001 | 2 in 100 million | 2.5 in 10 million |
/// | 1,000,001 | 2 in 100 billion | 2.4 in 10 billion |
///
/// It keeps improving beyond that, to about `2e-13` at a shape of `1e8`.
/// Below a shape of 3 it is poor. It is zero where the closed form goes
/// negative, which at a tail of 0.025 is a shape below about 0.63.
#[must_use]
pub fn gamma_quantile_approx(shape: f64, p: f64) -> f64 {
    wilson_hilferty(shape, normal_quantile(p))
}

/// An estimate of the value a `Gamma(shape, 1)` variable exceeds with
/// probability `q`: [`gamma_quantile_approx`] counted from above.
///
/// It is `gamma_quantile_approx(shape, 1 - q)` without forming `1 - q`,
/// which has no digits left when `q` is tiny. An interval takes its upper
/// end from here. At the shapes and tails in that table it is at least as
/// close as the lower end. It too is poor for a small shape, and it is
/// zero below a shape of about 0.02.
#[must_use]
pub fn gamma_quantile_upper_approx(shape: f64, q: f64) -> f64 {
    wilson_hilferty(shape, -normal_quantile(q))
}

/// Wilson and Hilferty's quantile of a `Gamma(shape, 1)`, at the normal
/// quantile `z`.
fn wilson_hilferty(shape: f64, z: f64) -> f64 {
    let cube_root = 1.0 - 1.0 / (9.0 * shape) + z / (3.0 * sqrt(shape));
    (shape * cube_root * cube_root * cube_root).max(0.0)
}

#[cfg(test)]
#[allow(clippy::unreadable_literal, clippy::excessive_precision)]
mod tests {
    use super::*;

    /// `(shape, tail, lower, upper)`: the exact quantiles of a `Gamma(shape, 1)`
    /// with probability `tail` below `lower` and above `upper`, from mpmath
    /// 1.4.1 at 40 digits (`gammainc(..., regularized=True)` inverted by
    /// `findroot`). SciPy 1.18.1's `gamma.ppf` / `gamma.isf` agree to 15 digits.
    const EXACT_QUANTILES: [(f64, f64, f64, f64); 36] = [
        (3.0, 0.05, 0.8176914471639534, 6.29579362187199),
        (3.0, 0.025, 0.6186721228956013, 7.224687667723961),
        (3.0, 0.005, 0.3378633887277333, 9.273792089255545),
        (3.0, 0.0005, 0.14970384992316443, 12.051399497491746),
        (5.0, 0.05, 1.97014956805953, 9.153519026637573),
        (5.0, 0.025, 1.6234863901184207, 10.241588675403698),
        (5.0, 0.005, 1.0779282406523194, 12.594089785985586),
        (5.0, 0.0005, 0.6324910403321942, 15.7099062537001),
        (11.0, 0.05, 6.1690072893953225, 16.9622192357219),
        (11.0, 0.025, 5.491160367236838, 18.39035604201778),
        (11.0, 0.005, 4.321358200333207, 21.39782749965427),
        (11.0, 0.0005, 3.202234075470444, 25.255559379265975),
        (31.0, 0.05, 22.44451178212511, 40.69050759444955),
        (31.0, 0.025, 21.062995979141853, 42.82686539480767),
        (31.0, 0.005, 18.53420768385046, 47.20932647393723),
        (31.0, 0.0005, 15.87399253850506, 52.64472948300404),
        (101.0, 0.05, 85.05714501910897, 118.07927278209706),
        (101.0, 0.025, 82.26615879303894, 121.62679379242638),
        (101.0, 0.005, 76.99203340575258, 128.76058012010245),
        (101.0, 0.0005, 71.16633647098456, 137.37529372057548),
        (1001.0, 0.05, 949.533845394138, 1053.6031221333008),
        (1001.0, 0.025, 939.9420337524415, 1063.952136016302),
        (1001.0, 0.005, 921.3833286958388, 1084.3728680643892),
        (1001.0, 0.0005, 900.1566743726239, 1108.3940211570052),
        (10001.0, 0.05, 9837.076886694862, 10166.060136127071),
        (10001.0, 0.025, 9805.942667599955, 10197.951624661473),
        (10001.0, 0.005, 9745.282730737363, 10260.473826873618),
        (10001.0, 0.0005, 9675.20318057752, 10333.348428605632),
        (100001.0, 0.05, 99481.41814605017, 100521.71888230444),
        (100001.0, 0.025, 99382.1495647746, 100621.74473974388),
        (100001.0, 0.005, 99188.3255604309, 100817.43103329056),
        (100001.0, 0.0005, 98963.7136238891, 101044.8380767309),
        (1000001.0, 0.05, 998356.7142612911, 1001646.4227676168),
        (1000001.0, 0.025, 998041.982360312, 1001961.9119454322),
        (1000001.0, 0.005, 997427.0477333264, 1002578.7088640063),
        (1000001.0, 0.0005, 996713.7471282742, 1003294.8045814902),
    ];
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

    /// The largest distance from exact the docs state for the lower end,
    /// by shape, with about a tenth of room. `tail` picks the column: 95%
    /// for a tail of 0.025 or more, 99.9% below that.
    fn documented_error(shape: f64, tail: f64) -> f64 {
        let (at_95, at_999) = match shape {
            s if s >= 1_000_001.0 => (1.9e-11, 2.6e-10),
            s if s >= 100_001.0 => (5.2e-10, 8.0e-9),
            s if s >= 10_001.0 => (1.7e-8, 2.6e-7),
            s if s >= 1_001.0 => (5.8e-7, 8.6e-6),
            s if s >= 101.0 => (2.4e-5, 3.2e-4),
            s if s >= 31.0 => (1.9e-4, 2.4e-3),
            s if s >= 11.0 => (1.4e-3, 1.65e-2),
            s if s >= 5.0 => (7.6e-3, 8.8e-2),
            _ => (2.6e-2, 2.9e-1),
        };
        if tail >= 0.025 { at_95 } else { at_999 }
    }

    /// Both ends of a 95% and of a 99.9% interval against the exact
    /// quantiles, within the distance the docs state for each shape.
    #[test]
    fn the_estimate_is_as_close_to_exact_as_documented() {
        for (shape, tail, lower, upper) in EXACT_QUANTILES {
            if tail != 0.025 && tail != 0.0005 {
                continue;
            }
            let limit = documented_error(shape, tail);
            let got = (
                gamma_quantile_approx(shape, tail),
                gamma_quantile_upper_approx(shape, tail),
            );
            assert!(
                relative_error(got.0, lower) < limit && relative_error(got.1, upper) < limit,
                "shape {shape} tail {tail}: {got:?} vs ({lower}, {upper}), limit {limit}"
            );
        }
    }

    /// A tail between the two columns is between them in accuracy.
    #[test]
    fn a_tail_in_between_is_no_worse_than_the_smaller_one() {
        for (shape, tail, lower, upper) in EXACT_QUANTILES {
            let limit = documented_error(shape, 0.0005);
            let got = (
                gamma_quantile_approx(shape, tail),
                gamma_quantile_upper_approx(shape, tail),
            );
            assert!(
                relative_error(got.0, lower) < limit && relative_error(got.1, upper) < limit,
                "shape {shape} tail {tail}: {got:?} vs ({lower}, {upper})"
            );
        }
    }

    /// For a very small shape both ends are zero. The exact upper end is
    /// not: at a shape of 0.01 it is 0.0471 for a tail of 0.025.
    #[test]
    fn a_very_small_shape_gives_zero_at_both_ends() {
        assert_eq!(gamma_quantile_approx(0.01, 0.025), 0.0);
        assert_eq!(gamma_quantile_upper_approx(0.01, 0.025), 0.0);
        // The lower end is zero up to a shape of about 0.63 at this tail.
        assert_eq!(gamma_quantile_approx(0.6, 0.025), 0.0);
        assert!(gamma_quantile_approx(0.65, 0.025) > 0.0);
        // The upper end is back above zero well before that.
        assert!(gamma_quantile_upper_approx(0.05, 0.025) > 0.2);
    }

    /// The error falls as the shape grows, at every tail.
    #[test]
    fn the_estimate_improves_with_the_shape() {
        for tail in [0.05, 0.025, 0.005, 0.0005] {
            let mut last = f64::INFINITY;
            for (shape, row_tail, lower, _) in EXACT_QUANTILES {
                if row_tail != tail {
                    continue;
                }
                let error = relative_error(gamma_quantile_approx(shape, tail), lower);
                assert!(
                    error < last,
                    "shape {shape} tail {tail}: {error} after {last}"
                );
                last = error;
            }
        }
    }

    #[test]
    fn the_estimate_rises_with_p_and_is_never_below_zero() {
        for shape in [0.05, 1.0, 6.0, 90.0, 9_000.0, 5e8] {
            let mut last = -1.0;
            for exponent in (1..=40).rev() {
                let x = gamma_quantile_approx(shape, 10f64.powi(-exponent));
                assert!(x >= last && x >= 0.0, "shape {shape} p 1e-{exponent}");
                last = x;
            }
            for exponent in 1..=40 {
                let x = gamma_quantile_upper_approx(shape, 10f64.powi(-exponent));
                assert!(x >= last && x.is_finite(), "shape {shape} q 1e-{exponent}");
                last = x;
            }
        }
        // Zero where the closed form goes negative.
        assert_eq!(gamma_quantile_approx(0.05, 0.001), 0.0);
    }

    /// The two forms are one curve: the same value where `1 - q` is exact.
    #[test]
    fn the_upper_form_is_the_lower_form_counted_from_above() {
        for q in [0.5, 0.25, 0.125, 0.0625] {
            assert_eq!(
                gamma_quantile_upper_approx(40.0, q),
                gamma_quantile_approx(40.0, 1.0 - q)
            );
        }
    }
}
