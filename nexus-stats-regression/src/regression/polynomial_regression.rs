use nexus_stats_core::math::MulAdd;

// Online Polynomial Regression — Sufficient Statistics + Normal Equations
//
// Accumulates sums of powers of x and cross-products with y.
// Solves normal equations via Gaussian elimination at query time.
// O(degree) per update, O(degree³) per query (bounded, max 9×9).
//
// degree and intercept are runtime-configured via builder.

// Normal equations with sums-of-powers can accumulate large values.

/// Polynomial coefficients returned by regression queries.
///
/// With intercept: `values[0]` = constant (a₀), `values[1]` = x coefficient (a₁), etc.
/// Without intercept: `values[0]` = x¹ coefficient, `values[1]` = x² coefficient, etc.
#[derive(Debug, Clone, Copy)]
pub struct Coefficients {
    pub(crate) values: [f64; 9],
    pub(crate) len: usize,
    /// Whether `values[0]` is the constant term (else the fit has none and
    /// `values[0]` multiplies `x`).
    pub(crate) intercept: bool,
}

impl Coefficients {
    /// Evaluates the fitted polynomial at `x` (O(degree)).
    ///
    /// `coefficients()` solves the normal equations; take it once and call
    /// `eval` per point instead of `predict` when evaluating many points.
    #[inline]
    #[must_use]
    pub fn eval(&self, x: f64) -> f64 {
        // Power form, not Horner: the `y` and `x_pow` chains are independent,
        // so at the degrees this type fits (<= 8) it is about half the
        // latency of Horner's single dependent chain.
        let mut y = 0.0;
        let mut x_pow = if self.intercept { 1.0 } else { x };
        for &c in &self.values[..self.len] {
            y = c.fma(x_pow, y);
            x_pow *= x;
        }
        y
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
/// For best numerical stability with high-degree fits or large x ranges,
/// center and scale your x values: `x_scaled = (x - x_mean) / x_std`.
///
/// # Complexity
/// - O(degree) per update, O(degree³) per coefficient query.
/// - ~216 bytes state. Zero allocation.
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
    sum_x: [f64; 17],
    sum_xy: [f64; 9],
    sum_y2: f64,
    count: u64,
    degree: usize,
    intercept: bool,
}

/// Builder for [`PolynomialRegression`].
#[derive(Debug, Clone)]
pub struct PolynomialRegressionBuilder {
    degree: Option<usize>,
    intercept: bool,
}

impl PolynomialRegression {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> PolynomialRegressionBuilder {
        PolynomialRegressionBuilder {
            degree: None,
            intercept: true,
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
        self.sum_y2 += y * y;
        let mut x_pow = 1.0;
        let max_pow = 2 * self.degree;
        for j in 0..=max_pow {
            self.sum_x[j] += x_pow;
            if j <= self.degree {
                self.sum_xy[j] += x_pow * y;
            }
            x_pow *= x;
        }
        Ok(())
    }

    /// Solve for polynomial coefficients, or `None` if underdetermined.
    ///
    /// Returns coefficients indexed from constant term (a₀) to highest
    /// power (aₖ). Without intercept, the first coefficient corresponds
    /// to x¹.
    #[must_use]
    pub fn coefficients(&self) -> Option<Coefficients> {
        let dim = self.dim();
        if (self.count as usize) < dim {
            return None;
        }

        let mut a = [[0.0; 9]; 9];
        let mut b = [0.0; 9];
        let offset = usize::from(!self.intercept);

        for i in 0..dim {
            for j in 0..dim {
                a[i][j] = self.sum_x[i + j + 2 * offset];
            }
            b[i] = self.sum_xy[i + offset];
        }

        if !gauss_solve_f64(dim, &mut a, &mut b) {
            return None;
        }

        let mut coeffs = Coefficients {
            values: [0.0; 9],
            len: dim,
            intercept: self.intercept,
        };
        coeffs.values[..dim].copy_from_slice(&b[..dim]);
        Some(coeffs)
    }

    /// R² goodness of fit, or `None` if not enough data.
    ///
    /// With intercept: centered R² = 1 - SS_res/SS_tot.
    /// Without intercept: uncentered R² = 1 - SS_res/Σy².
    #[must_use]
    pub fn r_squared(&self) -> Option<f64> {
        let coeffs = self.coefficients()?;
        let n = self.count as f64;
        let dim = self.dim();
        let offset = usize::from(!self.intercept);

        let mut beta_dot_rhs = 0.0;
        for i in 0..dim {
            beta_dot_rhs += coeffs.values[i] * self.sum_xy[i + offset];
        }
        let ss_res = self.sum_y2 - beta_dot_rhs;

        let ss_tot = if self.intercept {
            let sum_y = self.sum_xy[0];
            self.sum_y2 - sum_y * sum_y / n
        } else {
            self.sum_y2
        };

        if ss_tot <= 0.0 {
            return None;
        }

        Some(1.0 - ss_res / ss_tot)
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

    /// Whether enough data has been collected to solve (count >= dim).
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

        Ok(PolynomialRegression {
            sum_x: [0.0; 17],
            sum_xy: [0.0; 9],
            sum_y2: 0.0,
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
        let c = r.coefficients().unwrap();
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
        let c = r.coefficients().unwrap();
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
        let c = pr.coefficients().unwrap();
        assert!((c.values[3] - 2.0).abs() < 1e-6, "{:?}", c.values);
        assert!((c.values[1] + 1.0).abs() < 1e-6, "{:?}", c.values);
    }
}
