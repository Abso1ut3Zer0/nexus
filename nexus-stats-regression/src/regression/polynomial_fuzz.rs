//! Fuzz for `PolynomialRegression` and `EwPolynomialRegression`: random
//! feeds, run as a caller would, checked at points along the way against a
//! reference built from the stored points.
//!
//! The reference has a fit exactly when there are as many distinct x as
//! coefficients (distinct nonzero x through the origin): every weight is
//! positive, so that is the rank of the design. A fit returned where it has
//! none fails, whatever its value. Where both have one, the fit must leave
//! no more residual than a Householder QR solve on the points (Golub and
//! Van Loan, 2013, section 5.3), and `r_squared` must lie in `[0, 1]` and
//! agree with the residual of the coefficients `coefficients` returns.

// The feeds and the reference are written as the formulas read, unfused.
#![allow(clippy::suboptimal_flops)]
use std::vec::Vec;

use super::{Coefficients, EwPolynomialRegression, PolynomialRegression};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// Uniform on [0, 1).
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn pick<T: Copy>(&mut self, from: &[T]) -> T {
        from[self.below(from.len())]
    }
}

/// One caller's feed: `x` in one of several shapes about an offset, `y` a
/// polynomial in `x` on a level, with or without noise. Also the spread of
/// x, for a caller who sets `x_scale`.
fn feed(rng: &mut Rng, degree: usize, len: usize) -> (Vec<(f64, f64)>, f64) {
    let offset = rng.pick(&[0.0, 1.0e3, 1.0e6, 1.7e9, -5.0e8]);
    let step = rng.pick(&[1.0e-3, 1.0, 60.0]);
    let level = rng.pick(&[0.0, 100.0, 5.0e4, 1.0e9]);
    // One feed in eight is flat: y is the level, exactly.
    let flat = rng.below(8) == 0;
    let noise = if flat {
        0.0
    } else {
        rng.pick(&[0.0, 1.0e-6, 1.0])
    };
    let shape = rng.below(5);
    // Few distinct x, anywhere in the range: from one up to two more than
    // the number of coefficients.
    let levels: Vec<f64> = (0..=rng.below(degree + 3))
        .map(|_| rng.unit() * step * len as f64)
        .collect();
    let mut coeffs = [0.0; 9];
    for c in &mut coeffs[..=degree] {
        *c = if flat { 0.0 } else { rng.unit() * 2.0 - 1.0 };
    }
    let mut x = offset;
    let points: Vec<(f64, f64)> = (0..len)
        .map(|i| {
            x = match shape {
                0 => offset + i as f64 * step,
                1 => offset + (rng.unit() * 2.0 - 1.0) * step * len as f64,
                2 => offset + levels[rng.below(levels.len())],
                3 if i < len / 2 => offset + rng.unit() * step,
                3 => offset + 1.0e4 * step + rng.unit() * step,
                _ => x + step * (1.0 + rng.unit()),
            };
            // y in units of the spread of x, so the curve is visible.
            let t = (x - offset) / (step * len as f64);
            let mut y = 0.0;
            for &c in coeffs[..=degree].iter().rev() {
                y = y * t + c;
            }
            (x, level + 10.0 * y + noise * (rng.unit() * 2.0 - 1.0))
        })
        .collect();
    let (low, high) = points
        .iter()
        .fold((f64::INFINITY, f64::NEG_INFINITY), |(l, h), p| {
            (l.min(p.0), h.max(p.0))
        });
    (points, if high > low { (high - low) / 2.0 } else { 1.0 })
}

/// What the stored points give: whether a fit exists, and the residual of
/// a stable solve.
struct Reference {
    has_fit: bool,
    /// Weighted residual sum of squares of the QR fit, if it solved.
    residual: Option<f64>,
    /// The ratio of the largest to the smallest diagonal of R: a lower
    /// bound on the condition number of the scaled design.
    condition: f64,
    /// Weighted total sum of squares: about the mean with an intercept,
    /// about zero through the origin.
    total: f64,
}

fn reference(points: &[(f64, f64)], weights: &[f64], dim: usize, intercept: bool) -> Reference {
    let mut xs: Vec<f64> = points
        .iter()
        .map(|p| p.0)
        .filter(|&x| intercept || x != 0.0)
        .collect();
    xs.sort_by(f64::total_cmp);
    xs.dedup();
    let has_fit = xs.len() >= dim;

    let weight: f64 = weights.iter().sum();
    let mean_y = points
        .iter()
        .zip(weights)
        .map(|(p, w)| w * p.1)
        .sum::<f64>()
        / weight;
    let center_y = if intercept { mean_y } else { 0.0 };
    let total = points
        .iter()
        .zip(weights)
        .map(|(p, w)| w * (p.1 - center_y) * (p.1 - center_y))
        .sum();

    // Columns are powers of t = (x - center) / spread: centered and scaled
    // with an intercept, scaled only through the origin.
    let mean_x = points
        .iter()
        .zip(weights)
        .map(|(p, w)| w * p.0)
        .sum::<f64>()
        / weight;
    let center_x = if intercept { mean_x } else { 0.0 };
    let spread = points
        .iter()
        .map(|p| (p.0 - center_x).abs())
        .fold(0.0, f64::max);
    let solved = (has_fit && spread > 0.0)
        .then(|| {
            let first = usize::from(!intercept);
            let rows: Vec<Vec<f64>> = points
                .iter()
                .zip(weights)
                .map(|(p, w)| {
                    let t = (p.0 - center_x) / spread;
                    let mut row: Vec<f64> =
                        (first..first + dim).map(|k| t.powi(k as i32)).collect();
                    row.push(p.1 - center_y);
                    let root = w.sqrt();
                    for v in &mut row {
                        *v *= root;
                    }
                    row
                })
                .collect();
            least_squares_residual(rows, dim)
        })
        .flatten();
    Reference {
        has_fit,
        residual: solved.map(|s| s.0),
        condition: solved.map_or(f64::INFINITY, |s| s.1),
        total,
    }
}

/// Householder QR on rows `[design | rhs]`; the residual is the part of the
/// right-hand side below the first `dim` rows. `None` if the design is
/// numerically rank deficient.
// Negated so that a NaN norm counts as rank deficient.
#[allow(clippy::neg_cmp_op_on_partial_ord)]
fn least_squares_residual(mut rows: Vec<Vec<f64>>, dim: usize) -> Option<(f64, f64)> {
    let m = rows.len();
    let (mut largest, mut smallest) = (0.0f64, f64::INFINITY);
    for k in 0..dim {
        let norm = (k..m).map(|i| rows[i][k] * rows[i][k]).sum::<f64>().sqrt();
        largest = largest.max(norm);
        smallest = smallest.min(norm);
        if !(norm > 1e-10 * largest) {
            return None;
        }
        let alpha = if rows[k][k] > 0.0 { -norm } else { norm };
        let mut v: Vec<f64> = (k..m).map(|i| rows[i][k]).collect();
        v[0] -= alpha;
        let vv: f64 = v.iter().map(|a| a * a).sum();
        for j in k..=dim {
            let dot: f64 = (k..m).map(|i| v[i - k] * rows[i][j]).sum();
            let f = 2.0 * dot / vv;
            for i in k..m {
                rows[i][j] -= f * v[i - k];
            }
        }
    }
    let residual = (dim..m).map(|i| rows[i][dim] * rows[i][dim]).sum();
    Some((residual, largest / smallest))
}

fn residual_of(coeffs: &Coefficients, points: &[(f64, f64)], weights: &[f64]) -> f64 {
    points
        .iter()
        .zip(weights)
        .map(|(p, w)| {
            let e = p.1 - coeffs.eval(p.0);
            w * e * e
        })
        .sum()
}

/// How the type under test was set up.
#[derive(Clone, Copy)]
struct Setup {
    dim: usize,
    intercept: bool,
    x_scale: f64,
    /// Up to this many coefficients, a well-conditioned fit must be found.
    promised: usize,
}

/// Checks one reading against the reference over the points so far.
fn check(
    case: &str,
    setup: &Setup,
    got: Option<Coefficients>,
    r_squared: Option<f64>,
    points: &[(f64, f64)],
    weights: &[f64],
) {
    let Setup {
        dim,
        intercept,
        x_scale,
        promised,
    } = *setup;
    let want = reference(points, weights, dim, intercept);
    let Some(coeffs) = got else {
        assert!(r_squared.is_none(), "{case}: r_squared without a fit");
        // Up to `promised` coefficients, a well-conditioned fit is always
        // found, at any offset, with x_scale within a factor of 100 of the
        // range of x.
        let (low, high) = points
            .iter()
            .fold((f64::INFINITY, f64::NEG_INFINITY), |(l, h), p| {
                (l.min(p.0), h.max(p.0))
            });
        let scaled = (0.01..=100.0).contains(&(x_scale / (high - low)));
        assert!(
            !(dim <= promised && want.condition < 1e3 && scaled),
            "{case}: no fit, where the reference's condition is {:e}",
            want.condition
        );
        return;
    };
    assert!(want.has_fit, "{case}: a fit where the reference has none");

    let residual = residual_of(&coeffs, points, weights);
    let weight: f64 = weights.iter().sum();
    let y_size = points.iter().map(|p| p.1.abs()).fold(0.0, f64::max);
    // What rounding y alone leaves in a residual.
    let floor = weight * (64.0 * f64::EPSILON * y_size).powi(2);
    if let Some(best) = want.residual {
        assert!(
            residual <= best + 1e-6 * want.total + floor,
            "{case}: residual {residual:e}, QR {best:e}, total {:e}",
            want.total
        );
    }

    // And its R² too, where y has spread well past rounding.
    assert!(
        !(dim <= promised && r_squared.is_none() && want.total > 1e6 * floor),
        "{case}: a fit but no r_squared, total {:e}",
        want.total
    );
    // With no spread in y there is no R² to give.
    assert!(
        !(want.total == 0.0 && r_squared.is_some()),
        "{case}: r_squared {r_squared:?} on a flat y"
    );
    if let Some(r2) = r_squared {
        assert!((0.0..=1.0).contains(&r2), "{case}: r_squared {r2}");
        if want.total > floor {
            let direct = 1.0 - residual / want.total;
            assert!(
                (r2 - direct).abs() <= 1e-6 + floor / want.total,
                "{case}: r_squared {r2}, from the points {direct}"
            );
        }
    }
}

const CASES: u64 = 400;

#[test]
fn polynomial_regression_against_the_points() {
    for seed in 1..=CASES {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let degree = 1 + rng.below(8);
        let intercept = rng.below(4) != 0;
        let len = rng.pick(&[degree + 1, 3 * degree, 50, 300]);
        let (points, spread) = feed(&mut rng, degree, len);
        let x_scale = if rng.below(2) == 0 { 1.0 } else { spread };
        let mut r = PolynomialRegression::builder()
            .degree(degree)
            .intercept(intercept)
            .x_scale(x_scale)
            .build()
            .unwrap();
        let dim = degree + usize::from(intercept);
        let weights = vec![1.0; len];
        for (i, &(x, y)) in points.iter().enumerate() {
            r.update(x, y).unwrap();
            if i + 1 == len || i % 37 == 0 {
                let case = format!(
                    "seed {seed} degree {degree} intercept {intercept} x_scale {x_scale} at {i}"
                );
                check(
                    &case,
                    &Setup {
                        dim,
                        intercept,
                        x_scale,
                        promised: 3,
                    },
                    r.coefficients(),
                    r.r_squared(),
                    &points[..=i],
                    &weights[..=i],
                );
            }
        }
    }
}

#[test]
fn ew_polynomial_regression_against_the_points() {
    for seed in 1..=CASES {
        let mut rng = Rng(seed.wrapping_mul(0xD1B5_4A32_D192_ED03));
        let degree = 1 + rng.below(8);
        let intercept = rng.below(4) != 0;
        let dim = degree + usize::from(intercept);
        let alpha = rng.pick(&[0.01, 0.05]) / dim as f64;
        let len = rng.pick(&[3 * dim, 100, 400]);
        let (points, spread) = feed(&mut rng, degree, len);
        let x_scale = if rng.below(2) == 0 { 1.0 } else { spread };
        let mut r = EwPolynomialRegression::builder()
            .degree(degree)
            .intercept(intercept)
            .alpha(alpha)
            .x_scale(x_scale)
            .build()
            .unwrap();
        for (i, &(x, y)) in points.iter().enumerate() {
            r.update(x, y).unwrap();
            if i + 1 == len || i % 37 == 0 {
                // The weight of point j after i + 1 updates.
                let weights: Vec<f64> = (0..=i)
                    .map(|j| (1.0 - alpha).powi((i - j) as i32))
                    .collect();
                let case = format!(
                    "seed {seed} degree {degree} intercept {intercept} x_scale {x_scale} alpha {alpha} at {i}"
                );
                check(
                    &case,
                    &Setup {
                        dim,
                        intercept,
                        x_scale,
                        promised: 3,
                    },
                    r.coefficients(),
                    r.r_squared(),
                    &points[..=i],
                    &weights,
                );
            }
        }
    }
}

/// Long runs: the anchor has to move many times, and every move is
/// checked by the fit at the end. Weights below `1e-30` of the newest are
/// left out of the reference; they cannot change a residual at the
/// tolerance used.
#[test]
fn ew_polynomial_regression_over_long_runs() {
    for seed in 1..=24u64 {
        let mut rng = Rng(seed.wrapping_mul(0x2545_F491_4F6C_DD1D));
        let degree = 1 + rng.below(4);
        let dim = degree + 1;
        let alpha = 0.05 / dim as f64;
        let len = 40_000;
        // A random feed; x moving on with y level; or x level with y
        // jumping. The anchor has to follow whichever moves.
        let (points, x_scale) = match seed % 3 {
            0 => {
                let (points, spread) = feed(&mut rng, degree, len);
                // The caller scales x to the effective window, not the run.
                (points, spread * 2.0 / (len as f64 * alpha))
            }
            1 => {
                let points = (0..len)
                    .map(|i| (1.7e9 + i as f64, 1.0e9 + rng.unit()))
                    .collect();
                (points, 1.0 / alpha)
            }
            _ => {
                // y jumps by 1e9 halfway, and its spread stays near 1.
                let points = (0..len)
                    .map(|i| {
                        let x = 100.0 * rng.unit();
                        let jump = if i < len / 2 { 0.0 } else { 1.0e9 };
                        (1.7e9 + x, jump + 0.1 * x + rng.unit())
                    })
                    .collect();
                (points, 50.0)
            }
        };
        let mut r = EwPolynomialRegression::builder()
            .degree(degree)
            .alpha(alpha)
            .x_scale(x_scale)
            .build()
            .unwrap();
        for (i, &(x, y)) in points.iter().enumerate() {
            r.update(x, y).unwrap();
            if (i + 1) % 10_000 == 0 {
                let kept =
                    ((-30.0 * core::f64::consts::LN_10 / (1.0 - alpha).ln()) as usize).min(i);
                let from = i - kept;
                let weights: Vec<f64> = (from..=i)
                    .map(|j| (1.0 - alpha).powi((i - j) as i32))
                    .collect();
                let case = format!("long seed {seed} degree {degree} alpha {alpha} at {i}");
                check(
                    &case,
                    &Setup {
                        dim,
                        intercept: true,
                        x_scale,
                        // Scaled to its window, a long run always has a fit.
                        promised: 9,
                    },
                    r.coefficients(),
                    r.r_squared(),
                    &points[from..=i],
                    &weights,
                );
            }
        }
    }
}
