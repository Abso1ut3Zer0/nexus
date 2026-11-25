//! Cumulative probabilities and quantiles of the probability distributions
//! the estimators use.
//!
//! Two questions about a distribution come up when an estimate needs an
//! interval or a tail probability:
//!
//! - **The cumulative probability** (`..._cdf`): the chance that a value
//!   drawn from the distribution is at most `x`.
//! - **The quantile** (`..._quantile`): the reverse. The `x` that a value
//!   is at most with probability `p`. A 95% interval is the pair of
//!   quantiles at 0.025 and 0.975.
//!
//! Neither has a formula in elementary functions for the distributions
//! here, so each is computed to convergence. Nothing in this module is a
//! table. The functions are named for the distribution and the question,
//! and each matches the SciPy function its docs name, which is what its
//! tests check against.
//!
//! | Function | SciPy |
//! |---|---|
//! | `normal_quantile` | `scipy.stats.norm.ppf(p)` |
//! | `gamma_cdf` | `scipy.stats.gamma.cdf(x, shape)`, which is `scipy.special.gammainc(shape, x)` |
//! | `gamma_quantile` | `scipy.stats.gamma.ppf(p, shape)` |
//! | `gamma_quantile_approx` | the same, by a closed form that is fast and less accurate |
//!
//! The gamma functions take the shape only and assume a rate of one. For a
//! `Gamma(shape, rate)`, divide a quantile by the rate, and multiply `x`
//! by the rate before asking for its cumulative probability.
//!
//! These are internal: the estimators call them, and they are hidden from
//! the public docs. A caller of this library reads an estimator's own
//! methods, such as `GammaPoisson::credible_interval`.
//!
//! To add a distribution, name the functions the same way, cite the
//! method, and test against SciPy across the range of every argument,
//! including the tails and the largest and smallest shapes.

// The formulas are written as their sources give them, letter for letter,
// and none of this is on a per-sample path.
#![allow(clippy::suboptimal_flops, clippy::many_single_char_names)]

use crate::math::{exp, ln, ln_gamma, sqrt};

/// Above this shape the gamma quantile uses Wilson and Hilferty's form,
/// which is within one part in a million of the exact value from here up.
/// The exact iteration costs more as the shape grows.
const EXACT_SHAPE_LIMIT: f64 = 10_000.0;

/// The value a standard normal variable is at most with probability `p`,
/// for `p` in `(0, 1)`. Negative below one half and positive above it.
///
/// This is `scipy.stats.norm.ppf(p)`, by Acklam's rational approximation,
/// with a relative error below `1.2e-9`.
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

/// The probability that a `Gamma(shape, 1)` variable is at most `x`. For
/// `shape > 0`. Zero for `x` at or below zero.
///
/// In the textbooks this is the regularized lower incomplete gamma
/// function, `P(shape, x)`. It is `scipy.special.gammainc(shape, x)`,
/// to eleven digits.
///
/// A series below `x = shape + 1` and a continued fraction above it, each
/// run to convergence (Numerical Recipes 6.2).
#[must_use]
pub fn gamma_cdf(shape: f64, x: f64) -> f64 {
    gamma_p(shape, x, ln_gamma(shape))
}

/// [`gamma_cdf`] with `ln Gamma(a)` already in hand. `a` is the shape,
/// named as in the source.
fn gamma_p(a: f64, x: f64, ln_gamma_a: f64) -> f64 {
    if x <= 0.0 {
        return 0.0;
    }
    // `x^a e^-x / Gamma(a)`, the factor both forms share.
    let scale = exp(a * ln(x) - x - ln_gamma_a);
    if x < a + 1.0 {
        return scale * series(a, x);
    }
    1.0 - scale * continued_fraction(a, x)
}

/// The most terms either form takes. Both converge in a few times
/// `sqrt(a)` terms, far below this for any shape under the exact limit.
const MAX_TERMS: u32 = 100_000;

/// `sum of x^n / (a (a+1) ... (a+n))`, for `x < a + 1`.
fn series(a: f64, x: f64) -> f64 {
    let mut term = 1.0 / a;
    let mut sum = term;
    let mut denominator = a;
    for _ in 0..MAX_TERMS {
        denominator += 1.0;
        term *= x / denominator;
        sum += term;
        if term < sum * f64::EPSILON {
            break;
        }
    }
    sum
}

/// Lentz's evaluation of the continued fraction for the upper function,
/// for `x >= a + 1`.
fn continued_fraction(a: f64, x: f64) -> f64 {
    /// Stands in for a zero denominator.
    const TINY: f64 = 1e-300;
    let nonzero = |v: f64| if v.abs() < TINY { TINY } else { v };

    let mut b = x + 1.0 - a;
    let mut c = 1.0 / TINY;
    let mut d = 1.0 / nonzero(b);
    let mut value = d;
    for i in 1..MAX_TERMS {
        let i = f64::from(i);
        let numerator = -i * (i - a);
        b += 2.0;
        d = 1.0 / nonzero(numerator * d + b);
        c = nonzero(b + numerator / c);
        let factor = d * c;
        value *= factor;
        if (factor - 1.0).abs() < f64::EPSILON {
            break;
        }
    }
    value
}

/// The value a `Gamma(shape, 1)` variable is at most with probability
/// `p`: the `x` with `gamma_cdf(shape, x) = p`. For `shape > 0` and `p` in
/// `(0, 1)`. Divide by the rate for a `Gamma(shape, rate)`.
///
/// This is `scipy.stats.gamma.ppf(p, shape)`, to ten digits up to a shape
/// of 10,000. It starts from [`gamma_quantile_approx`] and refines it with
/// Halley steps on [`gamma_cdf`] (Numerical Recipes 6.2.1). Above a shape
/// of 10,000 it returns that estimate, which is within one part in a
/// million there and costs far less than the iteration would. A quantile too
/// small for an `f64` (a small shape with a small `p`) is zero.
#[must_use]
pub fn gamma_quantile(shape: f64, p: f64) -> f64 {
    /// Stop when a step moves the answer by less than this fraction.
    const TOLERANCE: f64 = 1e-13;
    const MAX_STEPS: u32 = 32;

    if shape > EXACT_SHAPE_LIMIT {
        return gamma_quantile_approx(shape, p);
    }
    let ln_gamma_shape = ln_gamma(shape);
    let mut x = starting_quantile(shape, p, ln_gamma_shape);
    if x == 0.0 {
        return 0.0;
    }
    for _ in 0..MAX_STEPS {
        let error = gamma_p(shape, x, ln_gamma_shape) - p;
        let density = exp((shape - 1.0) * ln(x) - x - ln_gamma_shape);
        if density == 0.0 {
            break;
        }
        // Halley's step: Newton's, corrected by the density's slope.
        let newton = error / density;
        let curvature = newton * ((shape - 1.0) / x - 1.0);
        let step = newton / (1.0 - 0.5 * curvature.min(1.0));
        // Never past zero: halve instead.
        x = if step < x { x - step } else { 0.5 * x };
        if step.abs() < TOLERANCE * x {
            break;
        }
    }
    x
}

/// Where the iteration starts. Wilson and Hilferty's estimate, or the
/// small-`x` form `(p Gamma(shape + 1))^(1/shape)` where that estimate is
/// not usable (a shape below one, or an estimate at or below zero). Zero
/// if the small-`x` form is below the smallest positive `f64`.
fn starting_quantile(shape: f64, p: f64, ln_gamma_shape: f64) -> f64 {
    let estimate = gamma_quantile_approx(shape, p);
    if shape >= 1.0 && estimate > 0.0 {
        return estimate;
    }
    let small = exp((ln(p) + ln_gamma_shape + ln(shape)) / shape);
    if small < f64::MIN_POSITIVE {
        return 0.0;
    }
    small
}

/// A fast estimate of [`gamma_quantile`], by Wilson and Hilferty's closed
/// form (1931).
///
/// It uses that the cube root of a gamma variable is close to normal. No
/// iteration, about five nanoseconds. Never below zero.
///
/// Against the exact quantile, over `p` from 0.005 to 0.995, it is within
/// 3% from a shape of 5, within 0.6% from 11, within 0.02% from 100, and
/// poor below 5.
#[must_use]
pub fn gamma_quantile_approx(shape: f64, p: f64) -> f64 {
    let cube_root = 1.0 - 1.0 / (9.0 * shape) + normal_quantile(p) / (3.0 * sqrt(shape));
    (shape * cube_root * cube_root * cube_root).max(0.0)
}

#[cfg(test)]
#[allow(clippy::unreadable_literal, clippy::excessive_precision)]
mod tests {
    use super::*;

    // Reference values from SciPy 1.18.1.
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
    /// `(a, x, scipy.special.gammainc(a, x))`
    const GAMMA_P: [(f64, f64, f64); 15] = [
        (0.05, 0.001, 0.7271792290529225),
        (0.5, 0.2, 0.47291074313446196),
        (0.5, 3.0, 0.9856941215645704),
        (1.0, 1.0, 0.6321205588285577),
        (2.5, 0.4, 0.022966656243073737),
        (2.5, 6.0, 0.9652122194937581),
        (10.0, 3.0, 0.0011024881301154815),
        (10.0, 10.0, 0.5420702855281478),
        (10.0, 25.0, 0.9997785233617512),
        (100.0, 80.0, 0.0171083130351331),
        (100.0, 101.0, 0.5528962934345113),
        (100.0, 140.0, 0.9998389428252874),
        (3000.0, 2900.0, 0.032859991921121025),
        (3000.0, 3100.0, 0.9649999863009537),
        (9999.0, 10050.0, 0.6958470035681733),
    ];
    /// `(shape, p, scipy.stats.gamma.ppf(p, shape))`
    const GAMMA_QUANTILES: [(f64, f64, f64); 70] = [
        (0.05, 1e-06, 5.844632057286552e-121),
        (0.05, 0.005, 5.573875481878775e-47),
        (0.05, 0.025, 5.31566188991436e-33),
        (0.05, 0.5, 5.573878440746256e-07),
        (0.05, 0.975, 0.5671737617538583),
        (0.05, 0.995, 1.5446254665734744),
        (0.05, 0.999999, 8.696862667893743),
        (0.5, 1e-06, 7.853981633978593e-13),
        (0.5, 0.005, 1.9635211110257972e-05),
        (0.5, 0.025, 0.0004910345585876278),
        (0.5, 0.5, 0.227468211559786),
        (0.5, 0.975, 2.511943093657444),
        (0.5, 0.995, 3.9397192883112084),
        (0.5, 0.999999, 11.964063488439734),
        (1.0, 1e-06, 1.0000005000003338e-06),
        (1.0, 0.005, 0.005012541823544282),
        (1.0, 0.025, 0.025317807984289876),
        (1.0, 0.5, 0.6931471805599455),
        (1.0, 0.975, 3.6888794541139354),
        (1.0, 0.995, 5.298317366548036),
        (1.0, 0.999999, 13.815510557935518),
        (2.0, 1e-06, 0.0014148806614793436),
        (2.0, 0.005, 0.103494546748091),
        (2.0, 0.025, 0.24220927854396496),
        (2.0, 0.5, 1.6783469900166612),
        (2.0, 0.975, 5.571643390938898),
        (2.0, 0.995, 7.430129500280121),
        (2.0, 0.999999, 16.68842079082944),
        (5.0, 1e-06, 0.16906300162147725),
        (5.0, 0.005, 1.0779282406523194),
        (5.0, 0.025, 1.6234863901184207),
        (5.0, 0.5, 4.670908882795985),
        (5.0, 0.975, 10.241588675403694),
        (5.0, 0.995, 12.594089785985584),
        (5.0, 0.999999, 23.43152342335784),
        (11.0, 1e-06, 1.595883879479403),
        (11.0, 0.005, 4.321358200333207),
        (11.0, 0.025, 5.49116036723684),
        (11.0, 0.5, 10.668522403836317),
        (11.0, 0.975, 18.39035604201778),
        (11.0, 0.995, 21.397827499654273),
        (11.0, 0.999999, 34.427884340321256),
        (31.0, 1e-06, 11.289152878124826),
        (31.0, 0.005, 18.53420768385046),
        (31.0, 0.025, 21.062995979141853),
        (31.0, 0.5, 30.667311387657918),
        (31.0, 0.975, 42.82686539480766),
        (31.0, 0.995, 47.20932647393722),
        (31.0, 0.999999, 64.97431844523122),
        (101.0, 1e-06, 60.200484910958565),
        (101.0, 0.005, 76.99203340575258),
        (101.0, 0.025, 82.26615879303894),
        (101.0, 0.5, 100.66686294933625),
        (101.0, 0.975, 121.62679379242638),
        (101.0, 0.995, 128.76058012010245),
        (101.0, 0.999999, 156.1552909398307),
        (1001.0, 1e-06, 857.7395464777528),
        (1001.0, 0.005, 921.3833286958389),
        (1001.0, 0.025, 939.9420337524415),
        (1001.0, 0.5, 1000.6666864072174),
        (1001.0, 0.975, 1063.952136016302),
        (1001.0, 0.995, 1084.3728680643892),
        (1001.0, 0.999999, 1158.653019939093),
        (9000.0, 1e-06, 8556.226986017622),
        (9000.0, 0.005, 8757.51392791989),
        (9000.0, 0.025, 8815.010448278765),
        (9000.0, 0.5, 8999.666668861542),
        (9000.0, 0.975, 9186.883842467863),
        (9000.0, 0.995, 9246.242625228375),
        (9000.0, 0.999999, 9458.169249890654),
    ];
    /// `(shape, p, scipy.stats.gamma.ppf(p, shape))` above the hand-off.
    const LARGE_SHAPE_QUANTILES: [(f64, f64, f64); 15] = [
        (20000.0, 0.005, 19637.601199973433),
        (20000.0, 0.025, 19723.767600607054),
        (20000.0, 0.5, 19999.66666765434),
        (20000.0, 0.975, 20278.126698463333),
        (20000.0, 0.995, 20366.15537769735),
        (100000.0, 0.005, 99187.32963316483),
        (100000.0, 0.025, 99381.15266374472),
        (100000.0, 0.5, 99999.6666668642),
        (100000.0, 0.975, 100620.74164077373),
        (100000.0, 0.995, 100816.42696055658),
        (1000000.0, 0.005, 997426.0490212408),
        (1000000.0, 0.025, 998040.9833402939),
        (1000000.0, 0.5, 999999.6666666864),
        (1000000.0, 0.975, 1001960.9109654503),
        (1000000.0, 0.995, 1002577.707576092),
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

    #[test]
    fn the_incomplete_gamma_function_matches_scipy() {
        for (a, x, want) in GAMMA_P {
            let got = gamma_cdf(a, x);
            assert!(
                relative_error(got, want) < 1e-11,
                "P({a}, {x}): {got} vs {want}"
            );
        }
        assert_eq!(gamma_cdf(3.0, 0.0), 0.0);
        assert_eq!(gamma_cdf(3.0, -1.0), 0.0);
        assert_eq!(gamma_cdf(3.0, 1e6), 1.0);
    }

    /// `P(1, x) = 1 - e^-x`, and `P(a, x)` rises with `x`.
    #[test]
    fn the_incomplete_gamma_function_has_its_known_shape() {
        for x in [0.01, 0.5, 1.9, 2.1, 7.0, 30.0] {
            let want = -f64::exp_m1(-x);
            assert!(relative_error(gamma_cdf(1.0, x), want) < 1e-14, "x {x}");
        }
        for a in [0.3, 4.0, 250.0] {
            let mut last = 0.0;
            for step in 1..200 {
                let p = gamma_cdf(a, a * f64::from(step) / 50.0);
                assert!(p >= last && p <= 1.0, "a {a} step {step}");
                last = p;
            }
        }
    }

    #[test]
    fn the_gamma_quantile_matches_scipy() {
        for (shape, p, want) in GAMMA_QUANTILES {
            let got = gamma_quantile(shape, p);
            assert!(
                relative_error(got, want) < 1e-10,
                "shape {shape} p {p}: {got} vs {want}"
            );
        }
    }

    /// The quantile undoes `P`, across shapes and tails.
    #[test]
    fn the_gamma_quantile_inverts_the_incomplete_gamma_function() {
        for shape in [0.02, 0.7, 1.0, 3.5, 48.0, 700.0, 9_999.0] {
            for p in [1e-8, 1e-3, 0.1, 0.5, 0.9, 0.999, 1.0 - 1e-8] {
                let x = gamma_quantile(shape, p);
                if x == 0.0 {
                    continue; // too small for an `f64`: the next test
                }
                let back = gamma_cdf(shape, x);
                assert!(
                    (back - p).abs() < 5e-11 * p.max(1e-3),
                    "shape {shape} p {p}: {back}"
                );
            }
        }
    }

    /// With a shape of 0.02 the `1e-8` quantile is about `1e-399`, which no
    /// `f64` holds. The answer is zero, not a number from a failed search.
    #[test]
    fn a_quantile_too_small_to_represent_is_zero() {
        assert_eq!(gamma_quantile(0.02, 1e-8), 0.0);
        assert_eq!(gamma_quantile(0.001, 0.4), 0.0);
        // The same shape still has quantiles that do fit.
        let x = gamma_quantile(0.02, 0.5);
        assert!(x > 0.0 && (gamma_cdf(0.02, x) - 0.5).abs() < 1e-11);
    }

    #[test]
    fn the_gamma_quantile_rises_with_p() {
        for shape in [0.1, 1.0, 6.0, 90.0, 9_000.0, 50_000.0] {
            let mut last = 0.0;
            for step in 1..100 {
                let x = gamma_quantile(shape, f64::from(step) / 100.0);
                assert!(x > last, "shape {shape} step {step}");
                last = x;
            }
        }
    }

    /// Above the hand-off the estimate is the answer, within one part in a
    /// million of SciPy. The two sides of the hand-off agree as closely.
    #[test]
    fn a_large_shape_uses_the_estimate_within_one_part_in_a_million() {
        for (shape, p, want) in LARGE_SHAPE_QUANTILES {
            let got = gamma_quantile(shape, p);
            assert_eq!(got, gamma_quantile_approx(shape, p));
            assert!(relative_error(got, want) < 1e-6, "shape {shape} p {p}");
        }
        for p in [0.005, 0.025, 0.5, 0.975, 0.995] {
            let below = gamma_quantile(EXACT_SHAPE_LIMIT, p);
            let above = gamma_quantile(EXACT_SHAPE_LIMIT + 1.0, p);
            assert!(
                above > below && relative_error(above, below) < 1.1e-4,
                "p {p}"
            );
        }
    }

    /// The accuracy the estimate's documentation states.
    #[test]
    fn the_estimate_is_as_accurate_as_documented() {
        for (shape, limit) in [(5.0, 0.03), (11.0, 0.006), (101.0, 2e-4)] {
            for p in [0.005, 0.025, 0.5, 0.975, 0.995] {
                let exact = gamma_quantile(shape, p);
                let estimate = gamma_quantile_approx(shape, p);
                assert!(
                    relative_error(estimate, exact) < limit,
                    "shape {shape} p {p}: {estimate} vs {exact}"
                );
            }
        }
        // Never below zero, even where it is poor.
        assert_eq!(gamma_quantile_approx(0.05, 0.001), 0.0);
    }
}
