use nexus_stats_core::math::MulAdd;

// Online Polynomial Regression: Sufficient Statistics + Normal Equations
//
// Accumulates power sums of x and cross-products with y, about an anchor
// that follows the data. Solves the normal equations via Gaussian
// elimination at query time. O(degree) per update, O(degree³) per query
// (bounded, max 9×9).

/// Polynomial coefficients returned by regression queries, in
/// `u = (x - x_ref) / x_scale`.
///
/// With intercept: `values[0]` is the constant, `values[1]` the coefficient
/// of `u`, and so on. Without intercept: `values[0]` is the coefficient of
/// `u`, `values[1]` of `u²`, and so on. [`eval`](Self::eval) takes a raw
/// `x`; [`to_raw_basis`](Self::to_raw_basis) gives the coefficients on
/// powers of `x`. The form follows MATLAB's `polyfit` with `mu`, and
/// NumPy's `Polynomial.fit` with `domain` and `window`.
#[derive(Debug, Clone, Copy)]
pub struct Coefficients {
    pub(crate) values: [f64; 9],
    pub(crate) len: usize,
    /// Whether `values[0]` is the constant term (else the fit has none and
    /// `values[0]` multiplies `u`).
    pub(crate) intercept: bool,
    /// The fit is in `u = (x - x_ref) / x_scale`.
    pub(crate) x_ref: f64,
    pub(crate) x_scale: f64,
}

impl Coefficients {
    /// Evaluates the fitted polynomial at `x` (O(degree)).
    ///
    /// `coefficients()` solves the normal equations; take it once and call
    /// `eval` per point instead of `predict` when evaluating many points.
    #[inline]
    #[must_use]
    pub fn eval(&self, x: f64) -> f64 {
        let u = (x - self.x_ref) / self.x_scale;
        // Power form, not Horner: the `y` and `u_pow` chains are independent,
        // so at the degrees this type fits (<= 8) it is about half the
        // latency of Horner's single dependent chain.
        let mut y = 0.0;
        let mut u_pow = if self.intercept { 1.0 } else { u };
        for &c in &self.values[..self.len] {
            y = c.fma(u_pow, y);
            u_pow *= u;
        }
        y
    }

    /// The reference point: the fit is in `u = (x - x_ref) / x_scale`.
    /// With an intercept, a recent sample's x (the anchor, see
    /// [`PolynomialRegression`]); `0` through the origin.
    #[inline]
    #[must_use]
    pub fn x_ref(&self) -> f64 {
        self.x_ref
    }

    /// The scale: the fit is in `u = (x - x_ref) / x_scale`.
    #[inline]
    #[must_use]
    pub fn x_scale(&self) -> f64 {
        self.x_scale
    }

    /// The same polynomial with coefficients on powers of raw `x`
    /// (`x_ref = 0`, `x_scale = 1`).
    ///
    /// Far from zero these coefficients are ill-conditioned in themselves:
    /// they are large and cancel when evaluated, so prefer [`eval`](Self::eval)
    /// on the shifted form.
    #[must_use]
    pub fn to_raw_basis(&self) -> Coefficients {
        let first = usize::from(!self.intercept);
        let mut raw = [0.0; 9];
        let mut inv_scale_pow = 1.0;
        for _ in 0..first {
            inv_scale_pow /= self.x_scale;
        }
        for idx in 0..self.len {
            let k = idx + first;
            let ck = self.values[idx] * inv_scale_pow;
            inv_scale_pow /= self.x_scale;
            // c_k (x - r)^k = c_k sum_j C(k, j) x^j (-r)^(k - j)
            let mut neg_r_pow = 1.0;
            for j in (first..=k).rev() {
                raw[j - first] = (ck * BINOM[k][j]).fma(neg_r_pow, raw[j - first]);
                neg_r_pow *= -self.x_ref;
            }
        }
        Coefficients {
            values: raw,
            len: self.len,
            intercept: self.intercept,
            x_ref: 0.0,
            x_scale: 1.0,
        }
    }

    /// Coefficients as a slice.
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[f64] {
        &self.values[..self.len]
    }

    /// Number of coefficients.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether there are no coefficients (should never happen in practice).
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get the i-th coefficient, or `None` if out of range.
    #[inline]
    #[must_use]
    pub fn get(&self, i: usize) -> Option<f64> {
        if i < self.len {
            Some(self.values[i])
        } else {
            None
        }
    }
}

impl core::ops::Index<usize> for Coefficients {
    type Output = f64;
    #[inline]
    fn index(&self, i: usize) -> &f64 {
        assert!(
            i < self.len,
            "coefficient index {i} out of range (len={})",
            self.len
        );
        &self.values[i]
    }
}

/// Binomial coefficients `C(k, j)` for `k, j <= 16`, exact in `f64`.
pub(crate) const BINOM: [[f64; 17]; 17] = binomials();

const fn binomials() -> [[f64; 17]; 17] {
    let mut t = [[0.0; 17]; 17];
    let mut k = 0;
    while k < 17 {
        t[k][0] = 1.0;
        let mut j = 1;
        while j <= k {
            t[k][j] = t[k - 1][j - 1] + if j < k { t[k - 1][j] } else { 0.0 };
            j += 1;
        }
        k += 1;
    }
    t
}

/// Moves the reference of power sums `sums[k] = Σ w·u^k`, `k in 0..=top`, so
/// that every `u` becomes `u + delta`: `Σ w·(u + delta)^k = Σ_j C(k, j)
/// delta^(k-j) sums[j]` (the binomial shift of Pébay 2008). Descending `k`
/// keeps the lower sums unshifted until they are read.
#[inline]
pub(crate) fn shift_power_sums(sums: &mut [f64], top: usize, delta: f64) {
    let mut pow = [1.0; 17];
    for i in 1..=top {
        pow[i] = pow[i - 1] * delta;
    }
    for k in (1..=top).rev() {
        let mut acc = sums[k];
        for j in 0..k {
            acc = (BINOM[k][j] * pow[k - j]).fma(sums[j], acc);
        }
        sums[k] = acc;
    }
}

/// Moves the reference of the anchored sums by `du` in u and `dv` in v:
/// every u becomes `u + du` and every v becomes `v + dv`.
#[inline]
pub(crate) fn shift_to(
    sum_x: &mut [f64; 17],
    sum_xy: &mut [f64; 9],
    sum_y2: &mut f64,
    degree: usize,
    du: f64,
    dv: f64,
) {
    shift_power_sums(sum_x, 2 * degree, du);
    shift_power_sums(sum_xy, degree, du);
    // Σ (v + dv)² = Σ v² + 2·dv·Σ v + dv²·n, with Σ v = sum_xy[0] and
    // n = sum_x[0] before sum_xy picks up dv.
    *sum_y2 = (2.0 * dv).fma(sum_xy[0], (dv * dv).fma(sum_x[0], *sum_y2));
    // Σ u^k (v + dv) = Σ u^k v + dv·Σ u^k
    for k in 0..=degree {
        sum_xy[k] = dv.fma(sum_x[k], sum_xy[k]);
    }
}

/// Whether the anchor has drifted more than two standard deviations from
/// the weighted mean, in u or in v: `mean² > 4·var`, written without
/// division as `5·s1² > 4·n·s2`. False while the spread is zero.
#[inline]
pub(crate) fn anchor_drifted(sum_x: &[f64; 17], sum_xy: &[f64; 9], sum_y2: f64) -> bool {
    let n = sum_x[0];
    let (su, suu) = (sum_x[1], sum_x[2]);
    let (sv, svv) = (sum_xy[0], sum_y2);
    5.0 * su * su > 4.0 * n * suu || 5.0 * sv * sv > 4.0 * n * svv
}

/// The first distinct x values seen, up to the number a fit needs.
///
/// The normal equations are singular exactly when fewer distinct x than
/// coefficients have been seen (nonzero x through the origin, where an x of
/// zero adds nothing). Rounding can hide that from the solve, so this is
/// checked directly.
#[derive(Debug, Clone, Copy)]
pub(crate) struct DistinctX {
    seen: [f64; 9],
    len: usize,
}

impl DistinctX {
    pub(crate) const fn new() -> Self {
        Self {
            seen: [0.0; 9],
            len: 0,
        }
    }

    /// Records `x` until `needed` distinct values have been seen.
    #[inline]
    pub(crate) fn record(&mut self, x: f64, needed: usize, intercept: bool) {
        if self.len < needed && (intercept || x != 0.0) && !self.seen[..self.len].contains(&x) {
            self.seen[self.len] = x;
            self.len += 1;
        }
    }

    /// Whether `needed` distinct values have been seen.
    #[inline]
    pub(crate) fn reached(&self, needed: usize) -> bool {
        self.len >= needed
    }
}

/// The normal equations `A·beta = b` from the anchored sums: `A[i][j]` is
/// the sum of `u^(i + j)`, `b[i]` the sum of `u^i·v`, both shifted up one
/// power through the origin.
pub(crate) fn normal_system(
    sum_x: &[f64; 17],
    sum_xy: &[f64; 9],
    dim: usize,
    intercept: bool,
) -> ([[f64; 9]; 9], [f64; 9]) {
    let offset = usize::from(!intercept);
    let mut a = [[0.0; 9]; 9];
    let mut b = [0.0; 9];
    for i in 0..dim {
        for j in 0..dim {
            a[i][j] = sum_x[i + j + 2 * offset];
        }
        b[i] = sum_xy[i + offset];
    }
    (a, b)
}

/// R² of the coefficients `beta` solved from the anchored sums, or `None`.
///
/// The residual sum of squares is taken as `sum_y2 - 2·beta·b + beta·A·beta`:
/// the residual of `beta` itself, so an error in `beta` can only raise it,
/// never take R² past 1. With an intercept the total is about the weighted
/// mean (centered R²), through the origin about zero (uncentered R²).
///
/// R² is in `[0, 1]` for any data. What evaluating these sums rounds is
/// trimmed; past that the sums no longer describe data, and there is no
/// reading. Neither is there when the total is zero or, with an intercept,
/// only rounding (the test SciPy's `skew` uses, see
/// [`rounding_variance`](nexus_stats_core::math::rounding_variance)). NaN
/// falls on the `None` side of every test.
// Negated comparisons so that NaN falls on the `None` side.
#[allow(clippy::neg_cmp_op_on_partial_ord)]
pub(crate) fn r_squared(
    sums: (&[f64; 17], &[f64; 9], f64),
    y_ref: f64,
    beta: &[f64],
    intercept: bool,
) -> Option<f64> {
    let (sum_x, sum_xy, sum_y2) = sums;
    let dim = beta.len();
    let (a, b) = normal_system(sum_x, sum_xy, dim, intercept);

    let weight = sum_x[0];
    let (ss_tot, ss_tot_size) = if intercept {
        let sum_y = sum_xy[0];
        let mean_y = y_ref + sum_y / weight;
        let squared_mean = sum_y * sum_y / weight;
        let ss_tot = sum_y2 - squared_mean;
        if !(ss_tot > weight * nexus_stats_core::math::rounding_variance(mean_y)) {
            return None;
        }
        (ss_tot, sum_y2 + squared_mean)
    } else {
        if !(sum_y2 > 0.0) {
            return None;
        }
        (sum_y2, sum_y2)
    };

    let (mut cross, mut cross_size) = (0.0, 0.0);
    let (mut quad, mut quad_size) = (0.0, 0.0);
    for i in 0..dim {
        let term = beta[i] * b[i];
        cross += term;
        cross_size += term.abs();
        let (mut row, mut row_size) = (0.0, 0.0);
        for j in 0..dim {
            let term = a[i][j] * beta[j];
            row += term;
            row_size += term.abs();
        }
        quad += beta[i] * row;
        quad_size += (beta[i] * row_size).abs();
    }
    let ss_res = (-2.0f64).fma(cross, sum_y2) + quad;

    // Each sum above is a dot product of at most `dim` terms, nested at most
    // twice, so its rounding is within `(2·dim + 3)·EPSILON` of the size of
    // what it adds (Higham, "Accuracy and Stability of Numerical
    // Algorithms", 2002, section 3.1).
    let rounding = (2 * dim + 3) as f64
        * f64::EPSILON
        * (2.0f64.fma(cross_size, sum_y2) + quad_size + ss_tot_size);
    let r_squared = 1.0 - ss_res / ss_tot;
    let trim = rounding / ss_tot;
    (-trim..=1.0 + trim)
        .contains(&r_squared)
        .then(|| r_squared.clamp(0.0, 1.0))
}

/// Gaussian elimination with partial pivoting on a fixed-size system.
/// Returns `true` if the solve succeeded (non-singular).
/// On success, `rhs` contains the solution.
pub(crate) fn gauss_solve_f64(dim: usize, a: &mut [[f64; 9]; 9], b: &mut [f64; 9]) -> bool {
    // Singularity is judged relative to the matrix scale: the normal equations'
    // entries grow as n·x^(2d), so an absolute pivot floor would call large-x
    // problems regular and small-x ones singular. NaN anywhere fails the
    // `>` tests below and reports singular instead of leaking out.
    let mut scale = 0.0f64;
    for row in a.iter().take(dim) {
        for &v in row.iter().take(dim) {
            scale = scale.max(v.abs());
        }
    }
    if !nexus_stats_core::math::positive_finite(scale) {
        return false;
    }
    let tol = scale * f64::EPSILON * dim as f64;
    for col in 0..dim {
        let mut max_row = col;
        let mut max_val = a[col][col].abs();
        for row in (col + 1)..dim {
            let v = a[row][col].abs();
            if v > max_val {
                max_val = v;
                max_row = row;
            }
        }
        if max_val.is_nan() || max_val <= tol {
            return false;
        }
        if max_row != col {
            a.swap(col, max_row);
            b.swap(col, max_row);
        }
        for row in (col + 1)..dim {
            let factor = a[row][col] / a[col][col];
            for j in col..dim {
                a[row][j] -= factor * a[col][j];
            }
            b[row] -= factor * b[col];
        }
    }
    for i in (0..dim).rev() {
        for j in (i + 1)..dim {
            b[i] -= a[i][j] * b[j];
        }
        b[i] /= a[i][i];
    }
    b.iter().take(dim).all(|v| v.is_finite())
}

/// Online polynomial regression via sufficient statistics.
///
/// Accumulates sums of powers of x and cross-products with y.
/// Solves the normal equations at query time via Gaussian elimination
/// with partial pivoting.
///
/// Degree and intercept are configured at construction via the builder.
/// Supports degree 1 (linear) through 8 (octic).
///
/// # Anchoring
///
/// Power sums of a raw x cancel once x is far from zero: a degree-2 fit to
/// 100 samples one apart is lost at an offset of 1e4. So the sums are kept in
/// `u = (x - x_ref) / x_scale` and `v = y - y_ref`, about an anchor that is
/// a recent sample. When the anchor has drifted more than two standard
/// deviations from the mean of `u` or of `v`, it moves to the current
/// sample, and every sum is shifted to it with the binomial identity
/// (Pébay, 2008). pandas re-sets the anchor of its rolling moments on the
/// same kind of test (`aggregations.pyx`). The coefficients come back in
/// `u`, with the anchor and scale in [`Coefficients`].
///
/// The type moves its anchor itself, where `VarianceRatio` leaves `resync()`
/// to the caller: that type stores its prices and can rebuild at any time,
/// while a regression keeps only its sums, so the shift has to happen
/// before the digits are lost.
///
/// Through the origin there is no anchor, since shifting x would change the
/// model; only `x_scale` applies.
///
/// A fit needs as many distinct x as coefficients (distinct nonzero x
/// through the origin); until then [`coefficients`](Self::coefficients) is
/// `None`.
///
/// # Limits
///
/// Measured against an exact rational reference. R² is evaluated from the
/// sums, which also carry the rounding of every update and shift, so it can
/// differ from the R² of the returned coefficients: by up to 1.1e-6 here,
/// and 1.6e-5 for [`EwPolynomialRegression`] at degree 8. For the same
/// reason [`r_squared`](Self::r_squared) is rarely `None` where the exact R²
/// is 1 or within 1e-10 of it: 11 cases in 6,000, at degrees 4 to 8.
///
/// Keep `x_scale` near the range of x. With it under a tenth of the range,
/// the solve called 47 of 168 well-posed fits with an intercept singular at
/// degree 6, and 140 of 200 at degree 8. With it from a tenth of the range
/// up to the range, no fit with an intercept was lost; through the origin,
/// where nothing is re-centred, only fits whose design, scaled to
/// `[-1, 1]`, has a condition number of 5.8e5 or more.
///
/// [`EwPolynomialRegression`]: super::EwPolynomialRegression
///
/// # Complexity
/// - O(degree) per update. An update that moves the anchor shifts every sum,
///   which is O(degree²). A steadily growing x, such as a timestamp, never moves it; a jump in
///   level that outweighs the history does.
/// - O(degree³) per coefficient query.
/// - ~344 bytes state. Zero allocation.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::regression::PolynomialRegression;
///
/// // Fit y = x² - 3x + 2 (quadratic)
/// let mut r = PolynomialRegression::builder().degree(2).build().unwrap();
/// for x in -50..50i64 {
///     let xf = x as f64;
///     r.update(xf, xf * xf - 3.0 * xf + 2.0);
/// }
/// let c = r.coefficients().unwrap();
/// assert_eq!(c.len(), 3); // [constant, x, x²]
/// ```
#[derive(Debug, Clone)]
pub struct PolynomialRegression {
    // Power sums of u = (x - x_ref) / x_scale and v = y - y_ref:
    // sum_x[k] = Σ u^k, sum_xy[k] = Σ u^k·v, sum_y2 = Σ v². With an intercept
    // (x_ref, y_ref) is the anchor, a recent sample, so the sums' size
    // follows the data's spread, not its offset. Through the origin both
    // references are 0.
    sum_x: [f64; 17],
    sum_xy: [f64; 9],
    sum_y2: f64,
    x_ref: f64,
    y_ref: f64,
    x_scale: f64,
    distinct: DistinctX,
    count: u64,
    degree: usize,
    intercept: bool,
}

/// Builder for [`PolynomialRegression`].
#[derive(Debug, Clone)]
pub struct PolynomialRegressionBuilder {
    degree: Option<usize>,
    intercept: bool,
    x_scale: f64,
}

impl PolynomialRegression {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> PolynomialRegressionBuilder {
        PolynomialRegressionBuilder {
            degree: None,
            intercept: true,
            x_scale: 1.0,
        }
    }

    /// System dimension.
    #[inline]
    fn dim(&self) -> usize {
        self.degree + self.intercept as usize
    }

    /// Configured polynomial degree.
    #[inline]
    #[must_use]
    pub fn degree(&self) -> usize {
        self.degree
    }

    /// Whether the intercept (constant term) is included.
    #[inline]
    #[must_use]
    pub fn has_intercept(&self) -> bool {
        self.intercept
    }

    /// Feeds an (x, y) observation.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if either value is NaN, or
    /// `DataError::Infinite` if either value is infinite.
    #[inline]
    pub fn update(&mut self, x: f64, y: f64) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(x);
        check_finite!(y);
        self.count += 1;
        self.distinct.record(x, self.dim(), self.intercept);
        if self.intercept && self.count == 1 {
            // The first sample is the anchor: u = v = 0.
            self.x_ref = x;
            self.y_ref = y;
        }
        let u = (x - self.x_ref) / self.x_scale;
        let v = y - self.y_ref;
        self.sum_y2 = v.fma(v, self.sum_y2);
        let mut u_pow = 1.0;
        for j in 0..=2 * self.degree {
            self.sum_x[j] += u_pow;
            if j <= self.degree {
                self.sum_xy[j] = u_pow.fma(v, self.sum_xy[j]);
            }
            u_pow *= u;
        }
        // PERF: shift only past the threshold. A shift is O(degree²), a plain
        // update O(degree).
        if self.intercept && anchor_drifted(&self.sum_x, &self.sum_xy, self.sum_y2) {
            self.re_anchor(x, y, u, v);
        }
        Ok(())
    }

    /// Moves the anchor to the sample (`x`, `y`), which is at (`u`, `v`)
    /// about the current one: shifts every sum so that it is measured from
    /// there. O(degree²).
    #[cold]
    fn re_anchor(&mut self, x: f64, y: f64, u: f64, v: f64) {
        shift_to(
            &mut self.sum_x,
            &mut self.sum_xy,
            &mut self.sum_y2,
            self.degree,
            -u,
            -v,
        );
        self.x_ref = x;
        self.y_ref = y;
    }

    /// Solve for polynomial coefficients, or `None` if underdetermined.
    ///
    /// The coefficients are on powers of `u` (see [`Coefficients`]), from
    /// the constant term up; without intercept, from `u¹`. `None` until as
    /// many distinct x as coefficients have been seen, and when the normal
    /// equations are singular to working precision.
    #[must_use]
    pub fn coefficients(&self) -> Option<Coefficients> {
        let mut coeffs = self.solve()?;
        // Through the origin y_ref is 0 and values[0] is the u coefficient.
        coeffs.values[0] += self.y_ref;
        Some(coeffs)
    }

    /// Solves the normal equations in the shifted basis, with v = y - y_ref:
    /// the constant term is relative to `y_ref`.
    fn solve(&self) -> Option<Coefficients> {
        let dim = self.dim();
        if !self.distinct.reached(dim) {
            return None;
        }

        let (mut a, mut b) = normal_system(&self.sum_x, &self.sum_xy, dim, self.intercept);
        if !gauss_solve_f64(dim, &mut a, &mut b) {
            return None;
        }

        let mut coeffs = Coefficients {
            values: [0.0; 9],
            len: dim,
            intercept: self.intercept,
            x_ref: self.x_ref,
            x_scale: self.x_scale,
        };
        coeffs.values[..dim].copy_from_slice(&b[..dim]);
        Some(coeffs)
    }

    /// R² of the fit [`coefficients`](Self::coefficients) returns, or
    /// `None`.
    ///
    /// With an intercept, centered: `1 - SS_res / SS_tot`, the total about
    /// the mean of y. Through the origin, uncentered: the total is the sum
    /// of y². `None` until the fit is solvable, when y has no spread beyond
    /// rounding, and when the sums give a value outside `[0, 1]` by more
    /// than evaluating them rounds (they no longer describe the data). A
    /// value within that rounding of the range is trimmed into it.
    #[must_use]
    pub fn r_squared(&self) -> Option<f64> {
        let coeffs = self.solve()?;
        r_squared(
            (&self.sum_x, &self.sum_xy, self.sum_y2),
            self.y_ref,
            coeffs.as_slice(),
            self.intercept,
        )
    }

    /// Predict y for a given x using current coefficients.
    ///
    /// Each call solves the normal equations (O(degree³)); to evaluate many
    /// points take [`coefficients`](Self::coefficients) once and use
    /// [`Coefficients::eval`].
    #[must_use]
    pub fn predict(&self, x: f64) -> Option<f64> {
        Some(self.coefficients()?.eval(x))
    }

    /// Number of observations processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether as many samples as coefficients have been seen. A fit also
    /// needs that many distinct x; see [`coefficients`](Self::coefficients).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        (self.count as usize) >= self.dim()
    }

    /// Resets to empty state. Degree and intercept unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.sum_x = [0.0; 17];
        self.sum_xy = [0.0; 9];
        self.sum_y2 = 0.0;
        self.x_ref = 0.0;
        self.y_ref = 0.0;
        self.distinct = DistinctX::new();
        self.count = 0;
    }
}

impl PolynomialRegressionBuilder {
    /// Polynomial degree (1..=8). Required.
    #[inline]
    #[must_use]
    pub fn degree(mut self, degree: usize) -> Self {
        self.degree = Some(degree);
        self
    }

    /// Whether to include the constant term. Default: `true`.
    ///
    /// `false` forces the fit through the origin.
    #[inline]
    #[must_use]
    pub fn intercept(mut self, intercept: bool) -> Self {
        self.intercept = intercept;
        self
    }

    /// Fixed scale for x: the fit is in `u = (x - x_ref) / x_scale`.
    /// Default: `1`. Keep it near the range of x (a window length, say):
    /// far below it, the solve can call a well-posed fit singular (see
    /// Limits on [`PolynomialRegression`]).
    #[inline]
    #[must_use]
    pub fn x_scale(mut self, x_scale: f64) -> Self {
        self.x_scale = x_scale;
        self
    }

    /// Builds the regression estimator.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Missing` if degree not set.
    /// Returns `ConfigError::Invalid` if degree not in 1..=8.
    #[inline]
    pub fn build(self) -> Result<PolynomialRegression, nexus_stats_core::ConfigError> {
        let degree = self
            .degree
            .ok_or(nexus_stats_core::ConfigError::Missing("degree"))?;
        if degree < 1 || degree > 8 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "degree must be in 1..=8",
            ));
        }

        if !nexus_stats_core::math::positive_finite(self.x_scale) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "x_scale must be positive and finite",
            ));
        }

        Ok(PolynomialRegression {
            sum_x: [0.0; 17],
            sum_xy: [0.0; 9],
            sum_y2: 0.0,
            x_ref: 0.0,
            y_ref: 0.0,
            x_scale: self.x_scale,
            distinct: DistinctX::new(),
            count: 0,
            degree,
            intercept: self.intercept,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn quadratic() -> PolynomialRegression {
        PolynomialRegression::builder().degree(2).build().unwrap()
    }

    fn cubic() -> PolynomialRegression {
        PolynomialRegression::builder().degree(3).build().unwrap()
    }

    // =========================================================================
    // Quadratic regression (y = ax² + bx + c)
    // =========================================================================

    #[test]
    fn quadratic_exact_fit() {
        let mut r = quadratic();
        for x in -50..50 {
            let xf = x as f64;
            r.update(xf, xf.mul_add(xf, -(3.0 * xf)) + 2.0).unwrap();
        }
        let c = r.coefficients().unwrap().to_raw_basis();
        assert!((c[0] - 2.0).abs() < 1e-6, "c0 = {}", c[0]);
        assert!((c[1] - (-3.0)).abs() < 1e-6, "c1 = {}", c[1]);
        assert!((c[2] - 1.0).abs() < 1e-6, "c2 = {}", c[2]);
    }

    #[test]
    fn quadratic_predict() {
        let mut r = quadratic();
        for x in -50..50 {
            let xf = x as f64;
            r.update(xf, xf * xf).unwrap();
        }
        let y = r.predict(10.0).unwrap();
        assert!((y - 100.0).abs() < 1e-4, "predict(10) = {y}");
    }

    // =========================================================================
    // Cubic
    // =========================================================================

    #[test]
    fn cubic_exact_fit() {
        let mut r = cubic();
        for x in -20..20 {
            let xf = x as f64;
            let y = (0.5 * xf * xf).mul_add(xf, -(2.0 * xf * xf)) + xf - 1.0;
            r.update(xf, y).unwrap();
        }
        let c = r.coefficients().unwrap().to_raw_basis();
        assert!((c[0] - (-1.0)).abs() < 1e-4, "c0 = {}", c[0]);
        assert!((c[1] - 1.0).abs() < 1e-4, "c1 = {}", c[1]);
        assert!((c[2] - (-2.0)).abs() < 1e-4, "c2 = {}", c[2]);
        assert!((c[3] - 0.5).abs() < 1e-4, "c3 = {}", c[3]);
    }

    // =========================================================================
    // Builder
    // =========================================================================

    #[test]
    fn builder_degree_4() {
        let mut r = PolynomialRegression::builder().degree(4).build().unwrap();
        for x in -20..20 {
            let xf = x as f64;
            r.update(xf, xf * xf * xf * xf).unwrap();
        }
        assert!(r.is_primed());
        assert_eq!(r.degree(), 4);
        assert!(r.has_intercept());
    }

    #[test]
    fn builder_no_intercept() {
        let mut r = PolynomialRegression::builder()
            .degree(1)
            .intercept(false)
            .build()
            .unwrap();
        for x in 1..100 {
            r.update(x as f64, 5.0 * x as f64).unwrap();
        }
        let c = r.coefficients().unwrap();
        assert_eq!(c.len(), 1);
        assert!((c[0] - 5.0).abs() < 1e-8, "slope = {}", c[0]);
    }

    #[test]
    fn builder_rejects_degree_0() {
        assert!(PolynomialRegression::builder().degree(0).build().is_err());
    }

    #[test]
    fn builder_rejects_degree_9() {
        assert!(PolynomialRegression::builder().degree(9).build().is_err());
    }

    #[test]
    fn builder_rejects_missing_degree() {
        assert!(PolynomialRegression::builder().build().is_err());
    }

    // =========================================================================
    // R²
    // =========================================================================

    #[test]
    fn r_squared_perfect() {
        let mut r = quadratic();
        for x in -50..50 {
            let xf = x as f64;
            r.update(xf, xf.mul_add(xf, -(3.0 * xf)) + 2.0).unwrap();
        }
        let r2 = r.r_squared().unwrap();
        assert!((r2 - 1.0).abs() < 1e-10, "R² = {r2}");
    }

    // =========================================================================
    // Priming / edge cases
    // =========================================================================

    #[test]
    fn quadratic_needs_3_points() {
        let mut r = quadratic();
        r.update(1.0, 1.0).unwrap();
        r.update(2.0, 4.0).unwrap();
        assert!(!r.is_primed());
        r.update(3.0, 9.0).unwrap();
        assert!(r.is_primed());
    }

    // =========================================================================
    // Heterogeneous storage
    // =========================================================================

    #[test]
    fn different_degrees_same_type() {
        let models: [PolynomialRegression; 2] = [
            PolynomialRegression::builder().degree(2).build().unwrap(),
            PolynomialRegression::builder().degree(3).build().unwrap(),
        ];
        assert_eq!(models[0].degree(), 2);
        assert_eq!(models[1].degree(), 3);
    }

    // =========================================================================
    // Reset
    // =========================================================================

    #[test]
    fn reset_clears_state() {
        let mut r = quadratic();
        for x in 0..100 {
            r.update(x as f64, x as f64).unwrap();
        }
        r.reset();
        assert_eq!(r.count(), 0);
        assert!(r.coefficients().is_none());
        assert_eq!(r.degree(), 2);
    }

    // =========================================================================
    // Coefficients struct
    // =========================================================================

    #[test]
    fn coefficients_indexing() {
        let mut r = quadratic();
        for x in -10..10 {
            let xf = x as f64;
            r.update(xf, xf * xf).unwrap();
        }
        let c = r.coefficients().unwrap();
        assert_eq!(c.len(), 3);
        assert!(!c.is_empty());
        assert!(c.get(0).is_some());
        assert!(c.get(3).is_none());
        assert_eq!(c.as_slice().len(), 3);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut r = quadratic();
        assert_eq!(
            r.update(f64::NAN, 1.0),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            r.update(1.0, f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(r.count(), 0);
    }

    /// Constant x is rank-deficient at any scale: the old absolute pivot floor
    /// called it regular at |x| ~ 1e3 and returned garbage coefficients.
    #[test]
    fn constant_x_is_singular_at_any_scale() {
        for x in [1.0e-3, 1.0, 1.0e3, 1.0e6] {
            let mut pr = PolynomialRegression::builder().degree(2).build().unwrap();
            for i in 0..50 {
                pr.update(x, f64::from(i)).unwrap();
            }
            assert!(pr.coefficients().is_none(), "x = {x}");
        }
    }

    /// Well-posed small-x data is regular: the old floor (1e-14) called a
    /// cubic on return-scale x singular.
    #[test]
    fn small_x_cubic_is_regular() {
        let mut pr = PolynomialRegression::builder().degree(3).build().unwrap();
        for i in 0..200 {
            let x = (f64::from(i) - 100.0) * 1.0e-4;
            pr.update(x, (2.0 * x * x).mul_add(x, -x)).unwrap();
        }
        let c = pr.coefficients().unwrap().to_raw_basis();
        assert!((c.values[3] - 2.0).abs() < 1e-6, "{:?}", c.values);
        assert!((c.values[1] + 1.0).abs() < 1e-6, "{:?}", c.values);
    }

    // =========================================================================
    // Anchoring (#794)
    // =========================================================================

    /// A curve on a unix-timestamp x and a price-level y: raw power sums
    /// cancel to nothing here, the anchored ones keep every coefficient.
    #[test]
    fn exact_fit_at_a_timestamp_offset() {
        for degree in 1..=4 {
            let mut r = PolynomialRegression::builder()
                .degree(degree)
                .x_scale(100.0)
                .build()
                .unwrap();
            let curve = |x: f64| {
                let t = (x - 1.7e9) / 100.0;
                (0..=degree).fold(0.0f64, |y, k| y.mul_add(t, 1.0 + k as f64))
            };
            for i in 0..200 {
                let x = 1.7e9 + f64::from(i);
                r.update(x, 5.0e4 + curve(x)).unwrap();
            }
            for x in [1.7e9, 1.7e9 + 99.5, 1.7e9 + 199.0] {
                let got = r.predict(x).unwrap();
                let want = 5.0e4 + curve(x);
                assert!(
                    (got - want).abs() < 1e-6,
                    "degree {degree} at {x}: {got} vs {want}"
                );
            }
            let r2 = r.r_squared().unwrap();
            assert!((r2 - 1.0).abs() < 1e-9, "degree {degree}: r2 {r2}");
        }
    }

    /// The anchor follows the data: x clustered near zero, then far away,
    /// until the new cluster outweighs the old one.
    #[test]
    fn the_anchor_moves_to_a_new_level_and_the_fit_holds() {
        let mut r = PolynomialRegression::builder().degree(1).build().unwrap();
        let line = |x: f64| 3.0f64.mul_add(x, -7.0);
        for i in 0..100 {
            let x = f64::from(i % 10);
            r.update(x, line(x)).unwrap();
        }
        assert_eq!(r.coefficients().unwrap().x_ref(), 0.0);
        for i in 0..1000 {
            let x = 1.0e7 + f64::from(i % 10);
            r.update(x, line(x)).unwrap();
        }
        let c = r.coefficients().unwrap();
        assert!(c.x_ref() >= 1.0e7, "x_ref {}", c.x_ref());
        for x in [0.0, 5.0, 1.0e7 + 5.0] {
            let got = c.eval(x);
            assert!(
                (got - line(x)).abs() < 1e-6 * line(x).abs().max(1.0),
                "at {x}: {got}"
            );
        }
    }

    /// The drift test: true only past two standard deviations, in u or in v.
    #[test]
    fn anchor_drift_is_past_two_standard_deviations() {
        let sums = |values: &[f64]| {
            let n = values.len() as f64;
            let s1: f64 = values.iter().sum();
            let s2: f64 = values.iter().map(|v| v * v).sum();
            (n, s1, s2)
        };
        let at = |values: &[f64], in_v: bool| {
            let (n, s1, s2) = sums(values);
            let mut sum_x = [0.0; 17];
            let mut sum_xy = [0.0; 9];
            sum_x[0] = n;
            // The other variable has mean 0 and variance 1/n: no drift.
            let sum_y2 = if in_v {
                sum_x[2] = 1.0;
                sum_xy[0] = s1;
                s2
            } else {
                sum_x[1] = s1;
                sum_x[2] = s2;
                1.0
            };
            anchor_drifted(&sum_x, &sum_xy, sum_y2)
        };
        for in_v in [false, true] {
            // Mean 2, standard deviation 1: exactly two, not past.
            assert!(!at(&[1.0, 3.0], in_v));
            // Mean 2.5, standard deviation 0.5: five.
            assert!(at(&[2.0, 3.0], in_v));
            // No spread at all: never.
            assert!(!at(&[0.0, 0.0], in_v));
        }
    }

    /// Through the origin there is no anchor: shifting x would change the
    /// model.
    #[test]
    fn through_the_origin_has_no_anchor() {
        let mut r = PolynomialRegression::builder()
            .degree(2)
            .intercept(false)
            .build()
            .unwrap();
        for i in 1..=200 {
            let x = 1.0e3 + f64::from(i);
            r.update(x, (0.5 * x).mul_add(x, -2.0 * x)).unwrap();
        }
        let c = r.coefficients().unwrap();
        assert_eq!(c.x_ref(), 0.0);
        assert!(
            (c[0] + 2.0).abs() < 1e-6 && (c[1] - 0.5).abs() < 1e-9,
            "{:?}",
            c.as_slice()
        );
    }

    #[test]
    fn builder_rejects_a_bad_x_scale() {
        for bad in [0.0, -1.0, f64::NAN, f64::INFINITY] {
            assert!(
                PolynomialRegression::builder()
                    .degree(2)
                    .x_scale(bad)
                    .build()
                    .is_err(),
                "{bad}"
            );
        }
    }

    /// `to_raw_basis` gives the same polynomial on powers of x.
    #[test]
    fn raw_basis_is_the_same_polynomial() {
        for intercept in [true, false] {
            let mut r = PolynomialRegression::builder()
                .degree(3)
                .intercept(intercept)
                .x_scale(4.0)
                .build()
                .unwrap();
            for i in 0..40 {
                let x = f64::from(i).mul_add(0.25, -3.0);
                let y = (x * x).mul_add(x, -x);
                r.update(x, 2.0f64.mul_add(f64::from(i % 3), y)).unwrap();
            }
            let c = r.coefficients().unwrap();
            let raw = c.to_raw_basis();
            assert_eq!((raw.x_ref(), raw.x_scale()), (0.0, 1.0));
            for x in [-3.0, -0.5, 0.0, 1.0, 6.75] {
                assert!(
                    (raw.eval(x) - c.eval(x)).abs() < 1e-9,
                    "intercept {intercept} at {x}"
                );
            }
        }
    }

    // =========================================================================
    // Distinct x (#794)
    // =========================================================================

    /// One distinct x short of the number of coefficients is no fit, however
    /// many samples repeat them; one more and there is.
    #[test]
    fn a_fit_needs_as_many_distinct_x_as_coefficients() {
        for (degree, intercept) in [(2, false), (3, true), (8, true), (8, false)] {
            let dim = degree + usize::from(intercept);
            let mut r = PolynomialRegression::builder()
                .degree(degree)
                .intercept(intercept)
                .build()
                .unwrap();
            for i in 0..500_u32 {
                let x = 0.37f64.mul_add((i as usize % (dim - 1)) as f64, 1.0);
                r.update(x, f64::from(i % 7)).unwrap();
            }
            assert!(
                r.coefficients().is_none(),
                "degree {degree} intercept {intercept}"
            );
            assert!(r.r_squared().is_none());
            r.update(-2.0, 1.0).unwrap();
            assert!(
                r.coefficients().is_some(),
                "degree {degree} intercept {intercept}"
            );
        }
    }

    /// Through the origin an x of zero adds nothing to the fit.
    #[test]
    fn through_the_origin_zero_is_not_a_distinct_x() {
        let mut r = PolynomialRegression::builder()
            .degree(2)
            .intercept(false)
            .build()
            .unwrap();
        // Without this check the solve takes these sums as regular.
        for i in 0..200 {
            let x = if i % 2 == 0 { 0.0 } else { 1.3 };
            r.update(x, f64::from(i % 7)).unwrap();
        }
        assert!(r.coefficients().is_none());
        r.update(-1.0, 1.0).unwrap();
        assert!(r.coefficients().is_some());
    }

    // =========================================================================
    // R² past rounding (#794)
    // =========================================================================

    /// y that differs only in its last bit has no spread past rounding: no R².
    #[test]
    fn r_squared_is_none_when_y_spreads_only_by_rounding() {
        let level = 1.0e9_f64;
        let next = f64::from_bits(level.to_bits() + 1);
        let mut r = quadratic();
        for i in 0..100 {
            r.update(f64::from(i), if i % 3 == 0 { next } else { level })
                .unwrap();
        }
        assert!(r.coefficients().is_some());
        assert_eq!(r.r_squared(), None);
    }

    /// Sums that no longer describe any data (here a sum of squares too
    /// small for the fit) give `None`, not a clamped 1.
    #[test]
    fn r_squared_is_none_past_what_rounding_explains() {
        let mut r = quadratic();
        for i in 0..50 {
            let x = f64::from(i);
            r.update(x, x.mul_add(x, -3.0 * x) + f64::from(i % 4))
                .unwrap();
        }
        let beta = r.solve().unwrap();
        let sums = (&r.sum_x, &r.sum_xy, r.sum_y2);
        let r2 = r_squared(sums, r.y_ref, beta.as_slice(), true).unwrap();
        assert!((0.0..=1.0).contains(&r2));
        // Lower Σ v² by twice the residual: R² comes out above 1 by about
        // the fraction of the variance the fit leaves.
        let ss_tot = r.sum_y2 - r.sum_xy[0] * r.sum_xy[0] / r.sum_x[0];
        let short = (-2.0 * (1.0 - r2)).mul_add(ss_tot, r.sum_y2);
        assert_eq!(
            r_squared((&r.sum_x, &r.sum_xy, short), r.y_ref, beta.as_slice(), true),
            None
        );
    }
}
