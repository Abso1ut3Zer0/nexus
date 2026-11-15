// Exponentially-Weighted Polynomial Regression
//
// Same sufficient-statistics approach as OLS polynomial regression,
// but with exponential decay on accumulators. Recent data dominates.
// Degree and intercept are runtime-configured via builder.

use super::polynomial_regression::Coefficients;
use nexus_stats_core::math::MulAdd;

/// Exponentially-weighted online polynomial regression.
///
/// Same accumulator structure as OLS polynomial regression but with
/// exponential decay. Recent observations are weighted more heavily,
/// making the fit adaptive to trend changes.
///
/// `alpha` is the weight on the new observation (same convention as EMA).
///
/// # Complexity
/// - O(degree) per update, O(degree³) per coefficient query.
/// - ~240 bytes state, zero allocation.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::regression::EwPolynomialRegression;
///
/// let mut r = EwPolynomialRegression::builder().degree(2).alpha(0.05).build().unwrap();
/// for x in 0..200u64 { r.update(x as f64, 2.0 * x as f64); }
/// assert!(r.is_primed());
/// ```
#[derive(Debug, Clone)]
pub struct EwPolynomialRegression {
    sum_x: [f64; 17],
    sum_xy: [f64; 9],
    sum_y2: f64,
    alpha: f64,
    one_minus_alpha: f64,
    effective_n: f64,
    count: u64,
    degree: usize,
    intercept: bool,
}

/// Builder for [`EwPolynomialRegression`].
#[derive(Debug, Clone)]
pub struct EwPolynomialRegressionBuilder {
    degree: Option<usize>,
    intercept: bool,
    alpha: Option<f64>,
}

impl EwPolynomialRegression {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> EwPolynomialRegressionBuilder {
        EwPolynomialRegressionBuilder {
            degree: None,
            intercept: true,
            alpha: None,
        }
    }

    fn dim(&self) -> usize {
        self.degree + self.intercept as usize
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
        self.effective_n = self.one_minus_alpha.fma(self.effective_n, 1.0);
        self.sum_y2 = self.one_minus_alpha.fma(self.sum_y2, y * y);

        let mut x_pow = 1.0;
        let max_pow = 2 * self.degree;
        for j in 0..=max_pow {
            self.sum_x[j] = self.one_minus_alpha.fma(self.sum_x[j], x_pow);
            if j <= self.degree {
                self.sum_xy[j] = self.one_minus_alpha.fma(self.sum_xy[j], x_pow * y);
            }
            x_pow *= x;
        }
        Ok(())
    }

    /// Solve for polynomial coefficients.
    #[must_use]
    pub fn coefficients(&self) -> Option<Coefficients> {
        let dim = self.dim();
        if (self.effective_n as usize) < dim {
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

        if !super::polynomial_regression::gauss_solve_f64(dim, &mut a, &mut b) {
            return None;
        }

        let mut coeffs = Coefficients {
            values: [0.0; 9],
            len: dim,
        };
        coeffs.values[..dim].copy_from_slice(&b[..dim]);
        Some(coeffs)
    }

    /// R² goodness of fit.
    #[must_use]
    pub fn r_squared(&self) -> Option<f64> {
        let coeffs = self.coefficients()?;
        let dim = self.dim();
        let offset = usize::from(!self.intercept);

        let mut beta_dot_rhs = 0.0;
        for i in 0..dim {
            beta_dot_rhs += coeffs.values[i] * self.sum_xy[i + offset];
        }
        let ss_res = self.sum_y2 - beta_dot_rhs;

        let ss_tot = if self.intercept {
            let sum_y = self.sum_xy[0];
            self.sum_y2 - sum_y * sum_y / self.effective_n
        } else {
            self.sum_y2
        };

        if ss_tot <= 0.0 {
            return None;
        }

        Some(1.0 - ss_res / ss_tot)
    }

    /// Predict y for a given x.
    #[must_use]
    pub fn predict(&self, x: f64) -> Option<f64> {
        let coeffs = self.coefficients()?;
        let dim = self.dim();

        let mut y = 0.0;
        let mut x_pow = if self.intercept { 1.0 } else { x };
        for i in 0..dim {
            y += coeffs.values[i] * x_pow;
            x_pow *= x;
        }
        Some(y)
    }

    /// Number of observations processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Effective sample count (converges to 1/alpha as n -> inf).
    #[inline]
    #[must_use]
    pub fn effective_count(&self) -> f64 {
        self.effective_n
    }

    /// Alpha (weight on new observation).
    #[inline]
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.alpha
    }

    /// Configured polynomial degree.
    #[inline]
    #[must_use]
    pub fn degree(&self) -> usize {
        self.degree
    }

    /// Whether primed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        (self.effective_n as usize) >= self.dim()
    }

    /// Resets to empty state. Config unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.sum_x = [0.0; 17];
        self.sum_xy = [0.0; 9];
        self.sum_y2 = 0.0;
        self.effective_n = 0.0;
        self.count = 0;
    }
}

impl EwPolynomialRegressionBuilder {
    /// Polynomial degree (1..=8). Required.
    #[inline]
    #[must_use]
    pub fn degree(mut self, degree: usize) -> Self {
        self.degree = Some(degree);
        self
    }

    /// Whether to include the constant term. Default: `true`.
    #[inline]
    #[must_use]
    pub fn intercept(mut self, intercept: bool) -> Self {
        self.intercept = intercept;
        self
    }

    /// Weight on new observation, in (0, 1). Required.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Builds the regression estimator.
    ///
    /// # Errors
    ///
    /// Returns errors if degree or alpha not set, or values out of range.
    pub fn build(self) -> Result<EwPolynomialRegression, nexus_stats_core::ConfigError> {
        let degree = self
            .degree
            .ok_or(nexus_stats_core::ConfigError::Missing("degree"))?;
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;

        if degree < 1 || degree > 8 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "degree must be in 1..=8",
            ));
        }
        if !(alpha > 0.0 && alpha < 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1) exclusive",
            ));
        }

        Ok(EwPolynomialRegression {
            sum_x: [0.0; 17],
            sum_xy: [0.0; 9],
            sum_y2: 0.0,
            alpha,
            one_minus_alpha: 1.0 - alpha,
            effective_n: 0.0,
            count: 0,
            degree,
            intercept: self.intercept,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ew_linear_basic() {
        let mut r = EwPolynomialRegression::builder()
            .degree(1)
            .alpha(0.05)
            .build()
            .unwrap();
        for x in 0..500 {
            r.update(x as f64, 2.0f64.mul_add(x as f64, 3.0)).unwrap();
        }
        let c = r.coefficients().unwrap();
        assert!(
            (c.as_slice()[1] - 2.0).abs() < 0.5,
            "ew slope = {}",
            c.as_slice()[1]
        );
    }

    #[test]
    fn ew_adapts_to_trend_change() {
        let mut r = EwPolynomialRegression::builder()
            .degree(1)
            .alpha(0.05)
            .build()
            .unwrap();
        for x in 0..200 {
            r.update(x as f64, x as f64).unwrap();
        }
        for x in 200..500 {
            r.update(x as f64, -(x as f64) + 400.0).unwrap();
        }
        let slope = r.coefficients().unwrap().values[1];
        assert!(
            slope < 0.0,
            "slope should be negative after trend change, got {slope}"
        );
    }

    #[test]
    fn ew_rejects_invalid_alpha() {
        assert!(
            EwPolynomialRegression::builder()
                .degree(1)
                .alpha(0.0)
                .build()
                .is_err()
        );
        assert!(
            EwPolynomialRegression::builder()
                .degree(1)
                .alpha(1.0)
                .build()
                .is_err()
        );
    }

    #[test]
    fn ew_rejects_missing() {
        assert!(
            EwPolynomialRegression::builder()
                .alpha(0.05)
                .build()
                .is_err()
        ); // missing degree
        assert!(EwPolynomialRegression::builder().degree(1).build().is_err()); // missing alpha
    }

    #[test]
    fn ew_predict() {
        let mut r = EwPolynomialRegression::builder()
            .degree(1)
            .alpha(0.05)
            .build()
            .unwrap();
        for x in 0..300 {
            r.update(x as f64, 3.0 * x as f64).unwrap();
        }
        let y = r.predict(100.0).unwrap();
        assert!((y - 300.0).abs() < 50.0, "predict(100) = {y}");
    }

    #[test]
    fn ew_reset() {
        let mut r = EwPolynomialRegression::builder()
            .degree(1)
            .alpha(0.05)
            .build()
            .unwrap();
        for x in 0..100 {
            r.update(x as f64, x as f64).unwrap();
        }
        r.reset();
        assert_eq!(r.count(), 0);
        assert!(r.coefficients().is_none());
        assert_eq!(r.degree(), 1);
    }

    #[test]
    fn ew_effective_count() {
        let mut r = EwPolynomialRegression::builder()
            .degree(1)
            .alpha(0.05)
            .build()
            .unwrap();
        for x in 0..1000 {
            r.update(x as f64, x as f64).unwrap();
        }
        assert!(
            (r.effective_count() - 20.0).abs() < 1.0,
            "effective_n = {}",
            r.effective_count()
        );
    }

    #[test]
    fn ew_quadratic() {
        let r = EwPolynomialRegression::builder()
            .degree(2)
            .alpha(0.05)
            .build()
            .unwrap();
        assert_eq!(r.degree(), 2);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut r = EwPolynomialRegression::builder()
            .degree(1)
            .alpha(0.05)
            .build()
            .unwrap();
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
}
