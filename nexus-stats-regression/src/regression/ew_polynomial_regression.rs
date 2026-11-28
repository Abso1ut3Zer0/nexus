// Exponentially-Weighted Polynomial Regression
//
// Same sufficient-statistics approach as OLS polynomial regression,
// but with exponential decay on accumulators. Recent data dominates.
// Degree and intercept are runtime-configured via builder.

use super::polynomial_regression::{
    Coefficients, DistinctX, anchor_drifted, gauss_solve_f64, normal_system, r_squared, shift_to,
};
use nexus_stats_core::math::MulAdd;

/// Exponentially-weighted online polynomial regression.
///
/// Same accumulator structure as OLS polynomial regression but with
/// exponential decay. Recent observations are weighted more heavily,
/// making the fit adaptive to trend changes.
///
/// `alpha` is the weight on the new observation (same convention as EMA).
///
/// The sums are kept about an anchor that follows the data, as in
/// [`PolynomialRegression`](super::PolynomialRegression): see its
/// Anchoring and Limits sections. With forgetting, the mean moves on with
/// the data: on a steadily moving x the anchor moves every `2.6 / alpha`
/// (at alpha 0.2) to `3 / alpha` (at small alpha) updates.
///
/// # Complexity
/// - O(degree) per update. An update that moves the anchor shifts every sum,
///   which is O(degree²).
/// - O(degree³) per coefficient query.
/// - ~368 bytes state, zero allocation.
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
    // Weighted power sums of u = (x - x_ref) / x_scale and v = y - y_ref,
    // about the anchor (x_ref, y_ref) with an intercept (see
    // `PolynomialRegression`).
    sum_x: [f64; 17],
    sum_xy: [f64; 9],
    sum_y2: f64,
    x_ref: f64,
    y_ref: f64,
    x_scale: f64,
    distinct: DistinctX,
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
    x_scale: f64,
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
            x_scale: 1.0,
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
        self.distinct.record(x, self.dim(), self.intercept);
        let decay = self.one_minus_alpha;
        self.effective_n = decay.fma(self.effective_n, 1.0);
        if self.intercept && self.count == 1 {
            // The first sample is the anchor: u = v = 0.
            self.x_ref = x;
            self.y_ref = y;
        }
        let u = (x - self.x_ref) / self.x_scale;
        let v = y - self.y_ref;
        self.sum_y2 = decay.fma(self.sum_y2, v * v);
        let mut u_pow = 1.0;
        for j in 0..=2 * self.degree {
            self.sum_x[j] = decay.fma(self.sum_x[j], u_pow);
            if j <= self.degree {
                self.sum_xy[j] = decay.fma(self.sum_xy[j], u_pow * v);
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

    /// Solve for polynomial coefficients.
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
        if (self.effective_n as usize) < dim || !self.distinct.reached(dim) {
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

    /// Weighted R² of the fit [`coefficients`](Self::coefficients)
    /// returns, or `None`. See [`PolynomialRegression::r_squared`].
    ///
    /// [`PolynomialRegression::r_squared`]: super::PolynomialRegression::r_squared
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

    /// Predict y for a given x.
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

    /// Whether the effective count has reached the number of coefficients.
    /// A fit also needs that many distinct x.
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
        self.x_ref = 0.0;
        self.y_ref = 0.0;
        self.distinct = DistinctX::new();
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

    /// Fixed scale for x: the fit is in `u = (x - x_ref) / x_scale`.
    /// Default: `1`. See [`PolynomialRegressionBuilder::x_scale`].
    ///
    /// [`PolynomialRegressionBuilder::x_scale`]: super::PolynomialRegressionBuilder::x_scale
    #[inline]
    #[must_use]
    pub fn x_scale(mut self, x_scale: f64) -> Self {
        self.x_scale = x_scale;
        self
    }

    /// Sets `alpha` from a half-life in samples: `1 - exp(-ln 2 / halflife)`.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.alpha = Some(nexus_stats_core::math::alpha_from_halflife(halflife));
        self
    }

    /// Builds the regression estimator.
    ///
    /// # Errors
    ///
    /// Returns errors if degree or alpha not set, or values out of range.
    #[inline]
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
        if !nexus_stats_core::math::in_unit_interval(alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1) exclusive",
            ));
        }
        // The effective sample size approaches 1/alpha from below and must
        // reach the number of coefficients for the fit to prime at all.
        let dim = (degree + usize::from(self.intercept)) as f64;
        if alpha >= 1.0 / dim {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be below 1/(number of coefficients) or the fit never primes",
            ));
        }

        if !nexus_stats_core::math::positive_finite(self.x_scale) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "x_scale must be positive and finite",
            ));
        }

        Ok(EwPolynomialRegression {
            sum_x: [0.0; 17],
            sum_xy: [0.0; 9],
            sum_y2: 0.0,
            x_ref: 0.0,
            y_ref: 0.0,
            x_scale: self.x_scale,
            distinct: DistinctX::new(),
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

    // =========================================================================
    // Anchoring (#794)
    // =========================================================================

    /// A quadratic in time on a unix-timestamp x and a price-level y, over
    /// many effective windows: the anchor moves with the data and the fit
    /// stays exact.
    #[test]
    fn tracks_a_curve_on_a_timestamp_over_many_windows() {
        let alpha = 0.01;
        let mut r = EwPolynomialRegression::builder()
            .degree(2)
            .alpha(alpha)
            .x_scale(100.0)
            .build()
            .unwrap();
        let curve = |x: f64| {
            let t = (x - 1.7e9) / 1000.0;
            (-0.25 * t).mul_add(t, 3.0f64.mul_add(t, 5.0e4))
        };
        let mut first_ref = None;
        for i in 0..100_000 {
            let x = 1.7e9 + f64::from(i);
            r.update(x, curve(x)).unwrap();
            if i == 10 {
                first_ref = r.coefficients().map(|c| c.x_ref());
            }
        }
        let c = r.coefficients().unwrap();
        assert!(
            c.x_ref() > first_ref.unwrap() + 9.0e4,
            "x_ref {}",
            c.x_ref()
        );
        for x in [1.7e9 + 99_000.0, 1.7e9 + 99_999.0] {
            let (got, want) = (c.eval(x), curve(x));
            assert!(
                (got - want).abs() < 1e-6 * want.abs(),
                "at {x}: {got} vs {want}"
            );
        }
        let r2 = r.r_squared().unwrap();
        assert!((r2 - 1.0).abs() < 1e-9, "r2 {r2}");
    }

    #[test]
    fn through_the_origin_has_no_anchor() {
        let mut r = EwPolynomialRegression::builder()
            .degree(1)
            .intercept(false)
            .alpha(0.05)
            .build()
            .unwrap();
        for i in 1..=2000 {
            let x = f64::from(i);
            r.update(x, 4.0 * x).unwrap();
        }
        let c = r.coefficients().unwrap();
        assert_eq!(c.x_ref(), 0.0);
        assert!((c[0] - 4.0).abs() < 1e-9, "{}", c[0]);
    }

    #[test]
    fn builder_rejects_a_bad_x_scale() {
        for bad in [0.0, -1.0, f64::NAN, f64::INFINITY] {
            assert!(
                EwPolynomialRegression::builder()
                    .degree(2)
                    .alpha(0.05)
                    .x_scale(bad)
                    .build()
                    .is_err(),
                "{bad}"
            );
        }
    }

    /// Repeating fewer distinct x than coefficients is no fit, however long.
    #[test]
    fn a_fit_needs_as_many_distinct_x_as_coefficients() {
        let mut r = EwPolynomialRegression::builder()
            .degree(3)
            .alpha(0.05)
            .build()
            .unwrap();
        for i in 0..1000_u32 {
            r.update(1.0e6 + f64::from(i % 3), f64::from(i % 5))
                .unwrap();
        }
        assert!(r.is_primed());
        assert!(r.coefficients().is_none());
        r.update(1.0e6 + 7.5, 1.0).unwrap();
        assert!(r.coefficients().is_some());
    }

    /// As many distinct x as coefficients, but an effective count below
    /// it: not primed, no fit.
    #[test]
    fn a_fit_needs_the_effective_count_too() {
        let mut r = EwPolynomialRegression::builder()
            .degree(2)
            .alpha(0.2)
            .build()
            .unwrap();
        for x in [1.0, 2.0, 4.0] {
            r.update(x, x * x).unwrap();
        }
        assert!(!r.is_primed());
        assert!(r.coefficients().is_none());
        // Weights 1, 0.8, 0.64, ... reach 3 at the fifth update.
        r.update(8.0, 64.0).unwrap();
        assert!(r.coefficients().is_none());
        r.update(16.0, 256.0).unwrap();
        assert!(r.is_primed());
        assert!(r.coefficients().is_some());
    }
}
