//! Quantiles of the gamma distribution, for the estimators in this crate.
//!
//! The normal quantile these build on is shared, and lives in
//! `nexus_stats_core::math::probability`. What is here has callers in this
//! crate only.
//!
//! | Function | What it estimates | SciPy's exact form |
//! |---|---|---|
//! | `gamma_interval_approx` | both ends of an equal-tailed interval of a `Gamma(shape, 1)` | `scipy.stats.gamma.ppf(tail, shape)` and `gamma.isf(tail, shape)` |
//!
//! It takes the shape only and assumes a rate of one. For a
//! `Gamma(shape, rate)`, divide by the rate.
//!
//! It is a closed form: a few operations, with no iteration, no search and
//! no table, so nothing can fail to converge. It is an estimate built for
//! streaming, where the counts are large, and it states how close it is,
//! measured against a 40-digit reference.
//!
//! There is no exact gamma quantile here, on purpose. The exact one needs
//! an iterative search over the incomplete gamma function, whose hard cases
//! are large shapes and extreme tails (SciPy's issue 26471, open in 2026,
//! is one about large shapes). Large shapes are where a streaming
//! estimator lives. The closed form is at its best there. For exact values
//! on a small sample, compute them offline with SciPy or R.

use nexus_stats_core::math::probability::normal_quantile;
use nexus_stats_core::math::{MulAdd, sqrt};

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
    // PERF: both ends are the same distance from the center, so the normal
    // quantile and the square root are taken once.
    let z = -normal_quantile(tail);
    (wilson_hilferty(shape, -z), wilson_hilferty(shape, z))
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
}
