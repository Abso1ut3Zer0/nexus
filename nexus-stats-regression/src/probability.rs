//! Quantiles of the gamma and beta distributions, for the estimators in
//! this crate.
//!
//! The normal quantile these build on is shared, and lives in
//! `nexus_stats_core::math::probability`. What is here has callers in this
//! crate only.
//!
//! | Function | What it estimates | SciPy's exact form |
//! |---|---|---|
//! | `gamma_interval_approx` | both ends of an equal-tailed interval of a `Gamma(shape, 1)` | `scipy.stats.gamma.ppf(tail, shape)` and `gamma.isf(tail, shape)` |
//! | `beta_interval_approx` | both ends of an equal-tailed interval of a `Beta(alpha, beta)` | `scipy.stats.beta.ppf(tail, alpha, beta)` and `beta.isf(tail, alpha, beta)` |
//! | `beta_one_sided_interval_approx` | the same, for a record with one outcome never seen under a prior below 1 | the same |
//! | `count_interval_approx` | both ends of an equal-tailed interval of a count, by its mean and dispersion | `scipy.stats.poisson.ppf` / `binom.ppf` and their `isf` |
//! | `chi_square_upper_tail_approx` | the probability a chi-square variable is above a value | `scipy.stats.chi2.sf(x, df)` |
//!
//! The gamma one takes the shape only and assumes a rate of one. For a
//! `Gamma(shape, rate)`, divide by the rate.
//!
//! Each is a closed form: a few operations, with no iteration, no search
//! and no table, so nothing can fail to converge. Each is an estimate
//! built for streaming, where the counts are large, and states how close
//! it is, measured against an exact reference.
//!
//! There is no exact quantile here, on purpose. The exact one needs an
//! iterative search over an incomplete gamma or beta function, whose hard cases
//! are large shapes and extreme tails (SciPy's issue 26471, open in 2026,
//! is one about large shapes). Large shapes are where a streaming
//! estimator lives. The closed form is at its best there. For exact values
//! on a small sample, compute them offline with SciPy or R.

use nexus_stats_core::math::probability::{normal_quantile, normal_upper_tail};
use nexus_stats_core::math::{MulAdd, exp, exp_m1, ln, ln_1p, powf, sqrt};

/// An estimate of both ends of an equal-tailed interval of a
/// `Gamma(shape, 1)`, by Wilson and Hilferty's closed form (1931).
///
/// The interval leaves probability `tail` outside at each end, for `tail`
/// in `(0, 0.5]`. With `z` the standard normal quantile at `1 - tail`:
///
/// ```text
/// v     = 1 / (9 shape)
/// lower = shape (1 - v - z sqrt(v))^3
/// upper = shape (1 - v + z sqrt(v))^3
/// ```
///
/// It uses that the cube root of a gamma variable over its shape is close
/// to a normal with mean `1 - v` and variance `v`. No iteration, about 20
/// cycles for the pair. Neither end is below zero.
///
/// Every answer is a little off the exact quantile, by an amount that
/// shrinks as the shape grows and grows with the confidence asked for.
/// This is how far, as a fraction of the value, for the two ends of an
/// interval at each confidence (the farther of the two). It is a
/// distance, not a rate of failure.
///
/// | Shape | 90% | 95% | 99% | 99.9% |
/// |---|---|---|---|---|
/// | 3 | 0.9% | 2.5% | 9.4% | 28% |
/// | 5 | 0.22% | 0.75% | 2.9% | 8.5% |
/// | 11 | 0.027% | 0.14% | 0.56% | 1.6% |
/// | 31 | 0.0044% | 0.018% | 0.083% | 0.23% |
/// | 101 | 6.4e-6 | 2.3e-5 | 0.011% | 0.031% |
/// | 1,001 | 1.7e-7 | 5.5e-7 | 3.0e-6 | 8.2e-6 |
/// | 10,001 | 4.7e-9 | 1.6e-8 | 8.9e-8 | 2.4e-7 |
/// | 100,001 | 1.5e-10 | 4.9e-10 | 2.8e-9 | 7.6e-9 |
/// | 1,000,001 | 6.3e-12 | 1.7e-11 | 9.0e-11 | 2.4e-10 |
///
/// The distance depends on the shape and the tail only, not on the rate.
/// It falls steadily as the shape grows, with no shape at which it rises.
/// Below a shape of 3 it is poor. It is zero where the closed form goes
/// negative, which at a tail of 0.025 is a shape below about 0.63 for the
/// lower end and about 0.02 for the upper.
pub(crate) fn gamma_interval_approx(shape: f64, tail: f64) -> (f64, f64) {
    gamma_interval_between(shape, shape, tail)
}

/// The lower end of [`gamma_interval_approx`] at `lower_shape` with the
/// upper end at `upper_shape`. The classical interval for a count takes its
/// two ends from shapes one apart.
pub(crate) fn gamma_interval_between(lower_shape: f64, upper_shape: f64, tail: f64) -> (f64, f64) {
    // PERF: both ends are the same distance from the center, so the normal
    // quantile is taken once.
    let z = -normal_quantile(tail);
    (
        wilson_hilferty(lower_shape, -z),
        wilson_hilferty(upper_shape, z),
    )
}

/// `x`, or zero where it is below zero. NaN stays NaN, where `f64::max`
/// would turn it into a number.
#[inline]
fn not_below_zero(x: f64) -> f64 {
    if x < 0.0 {
        return 0.0;
    }
    x
}

/// An estimate of both ends of an equal-tailed interval of a count with
/// the given `mean` and `dispersion`, its variance over its mean: the
/// interval of the Gamma with that mean and variance.
///
/// A Poisson count has a dispersion of 1 and a binomial one of
/// `1 - probability`. Within about one count of exact at 95%.
pub(crate) fn count_interval_approx(mean: f64, dispersion: f64, tail: f64) -> (f64, f64) {
    // Nothing is expected, so nothing will come.
    if mean == 0.0 {
        return (0.0, 0.0);
    }
    let (lower, upper) = gamma_interval_approx(mean / dispersion, tail);
    (lower * dispersion, upper * dispersion)
}

/// Wilson and Hilferty's quantile of a `Gamma(shape, 1)`, at the normal
/// quantile `z`:
///
/// ```text
/// v = 1 / (9 shape)
/// x = shape (1 - v + z sqrt(v))^3
/// ```
///
/// The cube root of a `Gamma(shape, 1)` variable over its shape is close
/// to a normal with mean `1 - v` and variance `v`. The quantile of that
/// normal is cubed and scaled back. Zero where the cube root would be
/// below zero.
#[inline]
fn wilson_hilferty(shape: f64, z: f64) -> f64 {
    let variance = 1.0 / (9.0 * shape);
    let cube_root = z.fma(sqrt(variance), 1.0 - variance);
    not_below_zero(shape * cube_root * cube_root * cube_root)
}

/// An estimate of both ends of an equal-tailed interval of a
/// `Beta(alpha, beta)`, by Abramowitz and Stegun's closed form (26.5.22).
///
/// The interval leaves probability `tail` outside at each end, for `tail`
/// in `(0, 0.5]`. Both parameters must be at least 1. With `z` the
/// standard normal quantile at `1 - tail`:
///
/// ```text
/// lambda = (z^2 - 3) / 6
/// h      = 2 / (1 / (2 alpha - 1) + 1 / (2 beta - 1))
/// spread = z sqrt(h + lambda) / h
/// skew   = (1 / (2 beta - 1) - 1 / (2 alpha - 1)) (lambda + 5/6 - 2 / (3 h))
/// lower  = alpha / (alpha + beta e^(2 (spread - skew)))
/// upper  = alpha / (alpha + beta e^(2 (-spread - skew)))
/// ```
///
/// No iteration. Both ends are inside `[0, 1]`, and swapping `alpha` with
/// `beta` mirrors the interval about one half.
///
/// Every answer is a little off the exact quantile, by an amount that
/// shrinks as the smaller parameter grows. This is how far an end is from
/// the exact end, as a fraction of its distance to the nearer of 0 and 1
/// (the farther of the two ends, at the worst ratio of the larger
/// parameter to the smaller, from 1 to 1,000,000):
///
/// | Smaller parameter | 90% | 95% | 99% | 99.9% |
/// |---|---|---|---|---|
/// | 3 | 2.5% | 3.2% | 4.2% | 5.7% |
/// | 5 | 0.90% | 1.1% | 1.2% | 1.2% |
/// | 11 | 0.21% | 0.23% | 0.19% | 0.21% |
/// | 31 | 0.037% | 0.037% | 0.020% | 0.050% |
/// | 101 | 5.6e-5 | 5.3e-5 | 2.0e-5 | 8.7e-5 |
/// | 1,001 | 1.6e-6 | 1.5e-6 | 3.3e-7 | 2.8e-6 |
/// | 10,001 | 5.0e-8 | 4.4e-8 | 7.7e-9 | 8.8e-8 |
/// | 100,001 | 1.6e-9 | 1.4e-9 | 2.3e-10 | 2.8e-9 |
/// | 1,000,001 | 4.8e-11 | 4.5e-11 | 1.0e-11 | 1.1e-10 |
///
/// The larger parameter hardly matters. Between a smaller parameter of 1
/// and 3 the interval is poor: 8% off at 2, at 95%. At exactly 1 the
/// quantile has an exact closed form, and that is used. Below one half the
/// form is not defined. These are measurements against SciPy 1.18.1, not
/// proven bounds.
pub(crate) fn beta_interval_approx(alpha: f64, beta: f64, tail: f64) -> (f64, f64) {
    beta_interval_between((alpha, beta), (alpha, beta), tail)
}

/// The lower end of [`beta_interval_approx`] for the `lower` parameters
/// with the upper end for the `upper` ones, each `(alpha, beta)`. The
/// classical interval for a proportion takes its two ends from parameters
/// one apart.
pub(crate) fn beta_interval_between(lower: (f64, f64), upper: (f64, f64), tail: f64) -> (f64, f64) {
    let z = -normal_quantile(tail);
    (
        beta_lower_end(lower.0, lower.1, tail, z),
        beta_upper_end(upper.0, upper.1, tail, z),
    )
}

/// The value a `Beta(alpha, beta)` is below with probability `tail`.
fn beta_lower_end(alpha: f64, beta: f64, tail: f64, z: f64) -> f64 {
    // Exact: with `beta` of 1 the distribution function is `x^alpha`, and
    // with `alpha` of 1 it is `1 - (1 - x)^beta`.
    if beta == 1.0 {
        return powf(tail, 1.0 / alpha);
    }
    if alpha == 1.0 {
        // `1 - (1 - tail)^(1 / beta)`, without the subtraction from 1.
        return -exp_m1(ln_1p(-tail) / beta);
    }
    abramowitz_stegun(alpha, beta, z)
}

/// The value a `Beta(alpha, beta)` is above with probability `tail`.
fn beta_upper_end(alpha: f64, beta: f64, tail: f64, z: f64) -> f64 {
    if beta == 1.0 {
        return exp(ln_1p(-tail) / alpha);
    }
    if alpha == 1.0 {
        // `1 - tail^(1 / beta)`, without the subtraction from 1.
        return -exp_m1(ln(tail) / beta);
    }
    abramowitz_stegun(alpha, beta, -z)
}

/// An estimate of both ends of an equal-tailed interval of a
/// `Beta(alpha, beta)` with one parameter from one half up to 1 and the
/// other at least 10: the posterior of a record with one outcome never
/// seen, under a prior below 1.
///
/// With `small` the smaller parameter and `large` the other, the rare
/// side of a Beta is close to a Gamma over the common side. With `g` a
/// quantile of a `Gamma(small, 1)` by Wilson and Hilferty's form:
///
/// ```text
/// rare side = g / (large + (small - 1) / 2 + g / 2)
/// ```
///
/// and the interval is that, or one minus it where the small parameter is
/// `beta`. The end away from the edge is within 2.5% of exact at 90%, 95%
/// and 99%, and 6% at 99.9%, as a fraction of its distance to the nearer
/// of 0 and 1. It does not improve with more data, since the small
/// parameter never grows. The end at the edge reads the edge, or closer
/// to it than the truth. Both ends are kept to `[0, 1]`, which matters
/// only past a confidence of about seven nines. Measured against SciPy
/// 1.18.1.
pub(crate) fn beta_one_sided_interval_approx(alpha: f64, beta: f64, tail: f64) -> (f64, f64) {
    let z = -normal_quantile(tail);
    let (small, large) = if alpha < beta {
        (alpha, beta)
    } else {
        (beta, alpha)
    };
    let rare_side = |g: f64| g / (large + (small - 1.0) / 2.0 + g / 2.0);
    let (near, far) = (
        rare_side(wilson_hilferty(small, -z)),
        rare_side(wilson_hilferty(small, z)),
    );
    // At an extreme confidence the form overshoots the far edge.
    let (near, far) = (within_unit(near), within_unit(far));
    if alpha < beta {
        return (near, far);
    }
    (1.0 - far, 1.0 - near)
}

/// `x` kept to `[0, 1]`. NaN stays NaN.
#[inline]
fn within_unit(x: f64) -> f64 {
    if x > 1.0 {
        return 1.0;
    }
    not_below_zero(x)
}

/// Abramowitz and Stegun's 26.5.22: the value a `Beta(alpha, beta)` is
/// below with the probability a standard normal is above `z`.
fn abramowitz_stegun(alpha: f64, beta: f64, z: f64) -> f64 {
    let lambda = z.fma(z, -3.0) / 6.0;
    let from_alpha = 1.0 / 2.0f64.fma(alpha, -1.0);
    let from_beta = 1.0 / 2.0f64.fma(beta, -1.0);
    let h = 2.0 / (from_alpha + from_beta);
    let spread = z * sqrt(h + lambda) / h;
    let skew = (from_beta - from_alpha) * (lambda + 5.0 / 6.0 - 2.0 / (3.0 * h));
    alpha / beta.fma(exp(2.0 * (spread - skew)), alpha)
}

/// An estimate of the probability that a chi-square variable with
/// `degrees` degrees of freedom is above `x`, by Wilson and Hilferty's
/// closed form run from the value to the probability.
///
/// ```text
/// v = 2 / (9 degrees)
/// z = ((x / degrees)^(1/3) - (1 - v)) / sqrt(v)
/// p = the probability a standard normal is above z
/// ```
///
/// This is the estimate over the exact value, by degrees of freedom and
/// the exact probability:
///
/// | Degrees | 0.5 | 0.05 | 0.001 |
/// |---|---|---|---|
/// | 1 | 1.015 | 0.94 | 1.17 |
/// | 4 | 1.004 | 0.987 | 1.12 |
/// | 9 | 1.001 | 0.995 | 1.07 |
/// | 29 | 1.000 | 0.999 | 1.03 |
/// | 99 | 1.000 | 1.000 | 1.01 |
/// | 999 | 1.000 | 1.000 | 1.001 |
///
/// Below about one in a million it says only "very small". Measured
/// against SciPy 1.18.1.
pub(crate) fn chi_square_upper_tail_approx(x: f64, degrees: f64) -> f64 {
    let variance = 2.0 / (9.0 * degrees);
    let cube_root = powf(x / degrees, 1.0 / 3.0);
    normal_upper_tail((cube_root - (1.0 - variance)) / sqrt(variance))
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

    fn relative_error(got: f64, want: f64) -> f64 {
        (got - want).abs() / want.abs()
    }

    /// The distance from exact the docs state, with a tenth of room, for
    /// the documented shape at or below `shape` and the documented
    /// confidence whose tail is at or below `tail`.
    fn documented_distance(shape: f64, tail: f64) -> f64 {
        let by_confidence = match shape {
            s if s >= 1_000_001.0 => [6.96e-12, 1.86e-11, 9.88e-11, 2.59e-10],
            s if s >= 100_001.0 => [1.65e-10, 5.44e-10, 3.05e-9, 8.36e-9],
            s if s >= 10_001.0 => [5.22e-9, 1.76e-8, 9.80e-8, 2.69e-7],
            s if s >= 1_001.0 => [1.82e-7, 6.08e-7, 3.28e-6, 9.03e-6],
            s if s >= 101.0 => [7.08e-6, 2.51e-5, 1.23e-4, 3.41e-4],
            s if s >= 31.0 => [4.87e-5, 2.01e-4, 9.09e-4, 2.54e-3],
            s if s >= 11.0 => [2.95e-4, 1.50e-3, 6.17e-3, 1.77e-2],
            s if s >= 5.0 => [2.45e-3, 8.22e-3, 3.17e-2, 9.40e-2],
            _ => [9.94e-3, 2.79e-2, 1.04e-1, 3.10e-1],
        };
        // 90%, 95%, 99%, 99.9%.
        let column = match tail {
            t if t >= 0.05 => 0,
            t if t >= 0.025 => 1,
            t if t >= 0.005 => 2,
            _ => 3,
        };
        by_confidence[column]
    }

    /// Both ends, at every shape and confidence in the table, against the
    /// exact quantiles and within the distance the docs state.
    #[test]
    fn the_estimate_is_as_close_to_exact_as_documented() {
        for (shape, tail, lower, upper) in EXACT_QUANTILES {
            let limit = documented_distance(shape, tail);
            let got = (
                gamma_interval_approx(shape, tail).0,
                gamma_interval_approx(shape, tail).1,
            );
            assert!(
                relative_error(got.0, lower) < limit && relative_error(got.1, upper) < limit,
                "shape {shape} tail {tail}: {got:?} vs ({lower}, {upper}), limit {limit}"
            );
        }
    }

    /// For a very small shape both ends are zero. The exact upper end is
    /// not: at a shape of 0.01 it is 0.0471 for a tail of 0.025.
    #[test]
    fn a_very_small_shape_gives_zero_at_both_ends() {
        assert_eq!(gamma_interval_approx(0.01, 0.025).0, 0.0);
        assert_eq!(gamma_interval_approx(0.01, 0.025).1, 0.0);
        // The lower end is zero up to a shape of about 0.63 at this tail.
        assert_eq!(gamma_interval_approx(0.6, 0.025).0, 0.0);
        assert!(gamma_interval_approx(0.65, 0.025).0 > 0.0);
        // The upper end is back above zero well before that.
        assert!(gamma_interval_approx(0.05, 0.025).1 > 0.2);
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
                let error = relative_error(gamma_interval_approx(shape, tail).0, lower);
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
                let x = gamma_interval_approx(shape, 10f64.powi(-exponent)).0;
                assert!(x >= last && x >= 0.0, "shape {shape} p 1e-{exponent}");
                last = x;
            }
            for exponent in 1..=40 {
                let x = gamma_interval_approx(shape, 10f64.powi(-exponent)).1;
                assert!(x >= last && x.is_finite(), "shape {shape} q 1e-{exponent}");
                last = x;
            }
        }
        // Zero where the closed form goes negative.
        assert_eq!(gamma_interval_approx(0.05, 0.001).0, 0.0);
    }

    /// `(alpha, beta, tail, lower, upper)`: the exact quantiles of a
    /// `Beta(alpha, beta)` with probability `tail` below `lower` and above
    /// `upper`, from SciPy 1.18.1's `beta.ppf` and `beta.isf`. mpmath 1.4.1
    /// at 30 digits puts the stated tail outside each end to 13 digits, on
    /// the rows with parameters up to 1,100.
    const EXACT_BETA_QUANTILES: [(f64, f64, f64, f64, f64); 40] = [
        (3.0, 3.0, 0.05, 0.1892553774377708, 0.8107446225622292),
        (3.0, 3.0, 0.025, 0.14663279963467313, 0.8533672003653269),
        (3.0, 3.0, 0.005, 0.0828291872014768, 0.9171708127985232),
        (3.0, 3.0, 0.0005, 0.037547900671868216, 0.9624520993281318),
        (
            3.0,
            300.0,
            0.05,
            0.0027129083139739705,
            0.020699224102251054,
        ),
        (
            3.0,
            300.0,
            0.025,
            0.0020532869606757144,
            0.023716762604377026,
        ),
        (
            3.0,
            300.0,
            0.005,
            0.0011218444700342835,
            0.03034051611718598,
        ),
        (
            3.0,
            300.0,
            0.0005,
            0.0004972332200356727,
            0.03924751517666717,
        ),
        (11.0, 11.0, 0.05, 0.32810871510135664, 0.6718912848986434),
        (11.0, 11.0, 0.025, 0.29780683878364417, 0.7021931612163559),
        (11.0, 11.0, 0.005, 0.24244941450187046, 0.7575505854981295),
        (11.0, 11.0, 0.0005, 0.18564495917081517, 0.8143550408291849),
        (
            11.0,
            1100.0,
            0.05,
            0.005567291513195817,
            0.01523335682596176,
        ),
        (
            11.0,
            1100.0,
            0.025,
            0.004957078491266074,
            0.016505298681849943,
        ),
        (
            11.0,
            1100.0,
            0.005,
            0.0039031161478220162,
            0.019178477746654436,
        ),
        (
            11.0,
            1100.0,
            0.0005,
            0.002893769377748443,
            0.02259678070736989,
        ),
        (101.0, 101.0, 0.05, 0.4422566089718203, 0.5577433910281797),
        (101.0, 101.0, 0.025, 0.4312911836276137, 0.5687088163723863),
        (101.0, 101.0, 0.005, 0.4100124980809424, 0.5899875019190576),
        (101.0, 101.0, 0.0005, 0.3856366565526869, 0.614363343447313),
        (
            101.0,
            10100.0,
            0.05,
            0.008345062713153072,
            0.01156612158658334,
        ),
        (
            101.0,
            10100.0,
            0.025,
            0.008072342911760533,
            0.011911532984666252,
        ),
        (
            101.0,
            10100.0,
            0.005,
            0.007556779799741682,
            0.01260576312145614,
        ),
        (
            101.0,
            10100.0,
            0.0005,
            0.006986987533808093,
            0.013443461287215226,
        ),
        (1001.0, 1001.0, 0.05, 0.48162308094842904, 0.518376919051571),
        (1001.0, 1001.0, 0.025, 0.478105656281757, 0.5218943437182431),
        (
            1001.0,
            1001.0,
            0.005,
            0.47123598894727126,
            0.5287640110527287,
        ),
        (
            1001.0,
            1001.0,
            0.0005,
            0.46327426378887604,
            0.536725736211124,
        ),
        (
            1001.0,
            100100.0,
            0.05,
            0.009394376572488976,
            0.010418626870150497,
        ),
        (
            1001.0,
            100100.0,
            0.025,
            0.009299920621529333,
            0.010520424048468128,
        ),
        (
            1001.0,
            100100.0,
            0.005,
            0.009117137088681936,
            0.01072126011866933,
        ),
        (
            1001.0,
            100100.0,
            0.0005,
            0.00890803577928692,
            0.010957453872770848,
        ),
        (
            100001.0,
            100001.0,
            0.05,
            0.498161010854063,
            0.5018389891459369,
        ),
        (
            100001.0,
            100001.0,
            0.025,
            0.49780871238802493,
            0.5021912876119751,
        ),
        (
            100001.0,
            100001.0,
            0.005,
            0.4971201699729327,
            0.5028798300270674,
        ),
        (
            100001.0,
            100001.0,
            0.0005,
            0.49632114286027884,
            0.5036788571397212,
        ),
        (
            100001.0,
            10000100.0,
            0.05,
            0.009849801333599901,
            0.009952289211140105,
        ),
        (
            100001.0,
            10000100.0,
            0.025,
            0.009840021082383394,
            0.009962142954747347,
        ),
        (
            100001.0,
            10000100.0,
            0.005,
            0.00982092465681669,
            0.009981420112361472,
        ),
        (
            100001.0,
            10000100.0,
            0.0005,
            0.009798794403330828,
            0.01000382162623939,
        ),
    ];

    /// The distance from exact the docs state, with a tenth of room, for
    /// the documented smaller parameter at or below `smaller` and the
    /// documented confidence whose tail is at or below `tail`.
    fn documented_beta_distance(smaller: f64, tail: f64) -> f64 {
        let by_confidence = match smaller {
            s if s >= 100_001.0 => [1.71e-9, 1.57e-9, 2.50e-10, 3.06e-9],
            s if s >= 1_001.0 => [1.78e-6, 1.60e-6, 3.58e-7, 3.07e-6],
            s if s >= 101.0 => [6.11e-5, 5.78e-5, 2.17e-5, 9.59e-5],
            s if s >= 11.0 => [2.35e-3, 2.55e-3, 2.04e-3, 2.33e-3],
            _ => [2.71e-2, 3.49e-2, 4.63e-2, 6.28e-2],
        };
        // 90%, 95%, 99%, 99.9%.
        let column = match tail {
            t if t >= 0.05 => 0,
            t if t >= 0.025 => 1,
            t if t >= 0.005 => 2,
            _ => 3,
        };
        by_confidence[column]
    }

    /// How far `got` is from `want`, as a fraction of `want`'s distance to
    /// the nearer of 0 and 1.
    fn beta_distance(got: f64, want: f64) -> f64 {
        (got - want).abs() / want.min(1.0 - want)
    }

    #[test]
    fn the_beta_estimate_is_as_close_to_exact_as_documented() {
        for (alpha, beta, tail, lower, upper) in EXACT_BETA_QUANTILES {
            let limit = documented_beta_distance(alpha.min(beta), tail);
            let got = beta_interval_approx(alpha, beta, tail);
            assert!(
                beta_distance(got.0, lower) < limit && beta_distance(got.1, upper) < limit,
                "({alpha}, {beta}) tail {tail}: {got:?} vs ({lower}, {upper}), limit {limit}"
            );
        }
    }

    /// Successes and failures are one question asked two ways.
    #[test]
    fn swapping_the_parameters_mirrors_the_beta_interval() {
        for (alpha, beta) in [(1.0, 1.0), (3.0, 40.0), (250.0, 7.0), (1e6, 12.0)] {
            for tail in [0.25, 0.025, 0.0005] {
                let (lower, upper) = beta_interval_approx(alpha, beta, tail);
                let (mirror_lower, mirror_upper) = beta_interval_approx(beta, alpha, tail);
                assert!((lower - (1.0 - mirror_upper)).abs() < 1e-15);
                assert!((upper - (1.0 - mirror_lower)).abs() < 1e-15);
            }
        }
    }

    /// From a parameter of 1 up, at any tail, the ends are numbers in
    /// order inside `[0, 1]`.
    #[test]
    fn the_beta_ends_stay_in_order_and_in_range() {
        for alpha in [1.0, 1.5, 4.0, 300.0, 1e9, 1e15] {
            for beta in [1.0, 2.0, 77.0, 1e6, 1e15] {
                for exponent in 1..=40 {
                    let (lower, upper) = beta_interval_approx(alpha, beta, 10f64.powi(-exponent));
                    assert!(
                        0.0 <= lower && lower <= upper && upper <= 1.0,
                        "({alpha}, {beta}) tail 1e-{exponent}: ({lower}, {upper})"
                    );
                }
                let (lower, upper) = beta_interval_approx(alpha, beta, 0.5);
                assert!(lower == upper, "({alpha}, {beta}) at a tail of one half");
            }
        }
    }

    /// Chi-square values at exact upper-tail probabilities, from SciPy
    /// 1.18.1's `chi2.isf(p, df)`, come back within the documented ratio.
    #[test]
    fn the_chi_square_tail_is_as_close_to_exact_as_documented() {
        // `(df, p, chi2.isf(p, df), allowed relative error)`
        let cases = [
            (4.0, 0.5, 3.3566939800333215, 0.005),
            (4.0, 0.05, 9.487729036781154, 0.015),
            (29.0, 0.05, 42.55696780429269, 0.002),
            (29.0, 0.001, 58.30117348979492, 0.035),
            (999.0, 0.001, 1142.8478393617174, 0.002),
        ];
        for (degrees, p, x, allowed) in cases {
            let got = chi_square_upper_tail_approx(x, degrees);
            assert!((got / p - 1.0).abs() < allowed, "df {degrees} p {p}: {got}");
        }
        // No scatter at all is as likely as can be.
        assert!(chi_square_upper_tail_approx(0.0, 10.0) > 0.999_999);
    }

    /// With a parameter of exactly 1 the quantile is exact.
    #[test]
    fn a_beta_parameter_of_one_gives_the_exact_ends() {
        // Beta(1, 1) is uniform.
        let (lower, upper) = beta_interval_approx(1.0, 1.0, 0.025);
        assert!((lower - 0.025).abs() < 1e-15 && (upper - 0.975).abs() < 1e-15);
        // Beta(a, 1) is below x with probability x^a.
        let (lower, upper) = beta_interval_approx(4.0, 1.0, 0.025);
        assert!((lower.powi(4) - 0.025).abs() < 1e-15 && (upper.powi(4) - 0.975).abs() < 1e-15);
        // Beta(1, b) is above x with probability (1 - x)^b.
        let (lower, upper) = beta_interval_approx(1.0, 4.0, 0.025);
        assert!(((1.0 - lower).powi(4) - 0.975).abs() < 1e-15);
        assert!(((1.0 - upper).powi(4) - 0.025).abs() < 1e-15);
    }

    /// With a parameter of 1 and a very large count on the other side, the
    /// ends stay accurate where `1 - x` would have lost them. Exact values
    /// are `-expm1(log1p(-tail) / b)` and `-expm1(log(tail) / b)`.
    #[test]
    fn a_parameter_of_one_stays_accurate_at_very_large_counts() {
        for beta in [1e9_f64, 1e15, 1e18] {
            let (lower, upper) = beta_interval_approx(1.0, beta, 0.025);
            let want = (-(-0.025_f64).ln_1p() / beta, -(0.025_f64.ln()) / beta);
            assert!((lower / want.0 - 1.0).abs() < 1e-8, "beta {beta}: {lower}");
            assert!((upper / want.1 - 1.0).abs() < 1e-8, "beta {beta}: {upper}");
            assert!(0.0 < lower && lower < upper);
        }
    }

    /// `(alpha, beta, confidence, lower, upper)`: exact ends from SciPy
    /// 1.18.1's `beta.interval`.
    const ONE_SIDED: [(f64, f64, f64, f64, f64); 5] = [
        (10.5, 0.5, 0.95, 0.7828037324907895, 0.9999521095668424),
        (100.5, 0.5, 0.95, 0.9752547299847301, 0.9999951019268956),
        (1000.5, 0.5, 0.999, 0.9939619849833474, 0.9999999998036995),
        (0.5, 50.5, 0.95, 9.771663301804069e-06, 0.048758459444071374),
        (20.75, 0.75, 0.9, 0.8862825455094463, 0.9991947161932753),
    ];

    /// The end away from the edge is within the documented distance, and
    /// the end at the edge is between the exact end and the edge.
    #[test]
    fn the_one_sided_beta_estimate_is_as_close_as_documented() {
        for (alpha, beta, confidence, lower, upper) in ONE_SIDED {
            let got = beta_one_sided_interval_approx(alpha, beta, (1.0 - confidence) / 2.0);
            let limit = if confidence > 0.99 { 0.06 } else { 0.025 };
            if alpha > beta {
                assert!(
                    beta_distance(got.0, lower) < limit,
                    "({alpha}, {beta}): {got:?}"
                );
                assert!(upper <= got.1 && got.1 <= 1.0, "({alpha}, {beta}): {got:?}");
            } else {
                assert!(
                    beta_distance(got.1, upper) < limit,
                    "({alpha}, {beta}): {got:?}"
                );
                assert!(0.0 <= got.0 && got.0 <= lower, "({alpha}, {beta}): {got:?}");
            }
        }
    }

    /// A value that is not a number comes back as one, never as zero.
    #[test]
    fn nan_is_not_turned_into_a_number() {
        let (lower, upper) = gamma_interval_approx(f64::NAN, 0.025);
        assert!(lower.is_nan() && upper.is_nan());
        let (lower, upper) = count_interval_approx(f64::NAN, 1.0, 0.025);
        assert!(lower.is_nan() && upper.is_nan());
        let (lower, upper) = count_interval_approx(-5.0, 1.0, 0.025);
        assert!(lower.is_nan() && upper.is_nan());
        assert_eq!(count_interval_approx(0.0, 1.0, 0.025), (0.0, 0.0));
    }

    /// At any tail, and with either parameter the small one, the ends of
    /// the one-sided form are numbers in order inside `[0, 1]`.
    #[test]
    fn the_one_sided_beta_ends_stay_in_order_and_in_range() {
        for small in [0.5, 0.75, 0.999] {
            for large in [10.0, 500.0, 1e9] {
                for exponent in 1..=40 {
                    let tail = 10f64.powi(-exponent);
                    for (alpha, beta) in [(small, large), (large, small)] {
                        let (lower, upper) = beta_one_sided_interval_approx(alpha, beta, tail);
                        assert!(
                            0.0 <= lower && lower <= upper && upper <= 1.0,
                            "({alpha}, {beta}) tail 1e-{exponent}: ({lower}, {upper})"
                        );
                    }
                }
            }
        }
    }
}
