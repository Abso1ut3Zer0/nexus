// Online Linear Regression — Closed-Form OLS + EW Variant
//
// Minimal state (5 accumulators, ~48 bytes) with direct 2×2 solve.
// No loops, no Gaussian elimination — just arithmetic.

#![allow(clippy::float_cmp)]

use nexus_stats_core::math::MulAdd;

/// Online linear regression with closed-form solve.
///
/// Accumulates 5 sufficient statistics and solves directly —
/// no matrix operations, no loops. With intercept: `y = ax + b`.
/// Without intercept (through origin): `y = ax`.
///
/// # Complexity
/// - O(1) per update (~6 adds, 2 muls), O(1) per query.
/// - 48 bytes state. Zero allocation.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::regression::LinearRegression;
///
/// let mut r = LinearRegression::new();
/// for x in 0..100u64 { r.update(x as f64, 2.0 * x as f64 + 3.0); }
/// let slope = r.slope().unwrap();
/// assert!((slope - 2.0).abs() < 0.001);
/// ```
#[derive(Debug, Clone)]
pub struct LinearRegression {
    sum_x: f64,
    sum_x2: f64,
    sum_y: f64,
    sum_xy: f64,
    sum_y2: f64,
    count: u64,
    intercept: bool,
}

/// Builder for [`LinearRegression`].
#[derive(Debug, Clone)]
pub struct LinearRegressionBuilder {
    intercept: bool,
}

impl LinearRegression {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> LinearRegressionBuilder {
        LinearRegressionBuilder { intercept: true }
    }

    /// Linear regression with intercept: `y = ax + b`.
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self {
            sum_x: 0.0,
            sum_x2: 0.0,
            sum_y: 0.0,
            sum_xy: 0.0,
            sum_y2: 0.0,
            count: 0,
            intercept: true,
        }
    }

    /// Linear regression through the origin: `y = ax`.
    #[inline]
    #[must_use]
    pub fn through_origin() -> Self {
        Self {
            sum_x: 0.0,
            sum_x2: 0.0,
            sum_y: 0.0,
            sum_xy: 0.0,
            sum_y2: 0.0,
            count: 0,
            intercept: false,
        }
    }

    /// System dimension: 2 with intercept, 1 without.
    #[inline]
    fn dim(&self) -> usize {
        1 + self.intercept as usize
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
        self.sum_x += x;
        self.sum_x2 = x.fma(x, self.sum_x2);
        self.sum_y += y;
        self.sum_xy = x.fma(y, self.sum_xy);
        self.sum_y2 = y.fma(y, self.sum_y2);
        Ok(())
    }

    /// Slope of the fit, or `None` if not primed.
    #[must_use]
    pub fn slope(&self) -> Option<f64> {
        if (self.count as usize) < self.dim() {
            return None;
        }
        if self.intercept {
            let n = self.count as f64;
            let denom = n.fma(self.sum_x2, -(self.sum_x * self.sum_x));
            if denom == 0.0 {
                return None;
            }
            Some(n.fma(self.sum_xy, -(self.sum_x * self.sum_y)) / denom)
        } else {
            if self.sum_x2 == 0.0 {
                return None;
            }
            Some(self.sum_xy / self.sum_x2)
        }
    }

    /// Intercept value, or `None` if not primed or no intercept.
    #[must_use]
    pub fn intercept_value(&self) -> Option<f64> {
        if !self.intercept {
            return None;
        }
        let slope = self.slope()?;
        let n = self.count as f64;
        Some(slope.fma(-self.sum_x, self.sum_y) / n)
    }

    /// R² goodness of fit, or `None` if not enough data.
    ///
    /// With intercept: centered R² = 1 - SS_res/SS_tot.
    /// Without intercept: uncentered R² = 1 - SS_res/Σy².
    #[must_use]
    #[allow(clippy::suboptimal_flops)]
    pub fn r_squared(&self) -> Option<f64> {
        let slope = self.slope()?;
        let n = self.count as f64;

        // SS_res = Σy² - 2*slope*Σxy - 2*intercept*Σy + slope²*Σx² + 2*slope*intercept*Σx + n*intercept²
        // Simplified via the closed-form:
        let (ss_res, ss_tot) = if self.intercept {
            let intercept = (self.sum_y - slope * self.sum_x) / n;
            let ss_res = self.sum_y2 - 2.0 * slope * self.sum_xy - 2.0 * intercept * self.sum_y
                + slope * slope * self.sum_x2
                + 2.0 * slope * intercept * self.sum_x
                + n * intercept * intercept;
            let ss_tot = self.sum_y2 - self.sum_y * self.sum_y / n;
            (ss_res, ss_tot)
        } else {
            let ss_res = self.sum_y2 - 2.0 * slope * self.sum_xy + slope * slope * self.sum_x2;
            (ss_res, self.sum_y2)
        };

        if ss_tot <= 0.0 {
            return None;
        }

        Some(1.0 - ss_res / ss_tot)
    }

    /// Predict y for a given x.
    #[must_use]
    pub fn predict(&self, x: f64) -> Option<f64> {
        let slope = self.slope()?;
        if self.intercept {
            let intercept = self.intercept_value()?;
            Some(slope.fma(x, intercept))
        } else {
            Some(slope * x)
        }
    }

    /// Number of observations processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough data to solve (>= 2 with intercept, >= 1 without).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        (self.count as usize) >= self.dim()
    }

    /// Whether the intercept is included.
    #[inline]
    #[must_use]
    pub fn has_intercept(&self) -> bool {
        self.intercept
    }

    /// Resets to empty state. Intercept setting unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.sum_x = 0.0;
        self.sum_x2 = 0.0;
        self.sum_y = 0.0;
        self.sum_xy = 0.0;
        self.sum_y2 = 0.0;
        self.count = 0;
    }
}

impl Default for LinearRegression {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl LinearRegressionBuilder {
    /// Whether to include the constant term. Default: `true`.
    #[inline]
    #[must_use]
    pub fn intercept(mut self, intercept: bool) -> Self {
        self.intercept = intercept;
        self
    }

    /// Builds the regression.
    pub fn build(self) -> Result<LinearRegression, nexus_stats_core::ConfigError> {
        Ok(LinearRegression {
            sum_x: 0.0,
            sum_x2: 0.0,
            sum_y: 0.0,
            sum_xy: 0.0,
            sum_y2: 0.0,
            count: 0,
            intercept: self.intercept,
        })
    }
}

// ============================================================================
// EW Linear Regression
// ============================================================================

/// Exponentially-weighted online linear regression.
///
/// Same closed-form solve as the non-EW linear regression types
/// but with exponential decay on accumulators. Recent data
/// dominates, making the fit adaptive to trend changes.
///
/// # Complexity
/// - O(1) per update, O(1) per query.
/// - ~64 bytes state. Zero allocation.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::regression::EwLinearRegression;
///
/// let mut r = EwLinearRegression::builder()
///     .alpha(0.05)
///     .build()
///     .unwrap();
/// for x in 0..200u64 { r.update(x as f64, 2.0 * x as f64); }
/// assert!(r.slope().is_some());
/// ```
#[derive(Debug, Clone)]
pub struct EwLinearRegression {
    sum_x: f64,
    sum_x2: f64,
    sum_y: f64,
    sum_xy: f64,
    sum_y2: f64,
    alpha: f64,
    one_minus_alpha: f64,
    effective_n: f64,
    count: u64,
    intercept: bool,
}

/// Builder for [`EwLinearRegression`].
#[derive(Debug, Clone)]
pub struct EwLinearRegressionBuilder {
    alpha: Option<f64>,
    intercept: bool,
}

impl EwLinearRegression {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> EwLinearRegressionBuilder {
        EwLinearRegressionBuilder {
            alpha: None,
            intercept: true,
        }
    }

    fn dim(&self) -> usize {
        1 + self.intercept as usize
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
        self.sum_x = self.one_minus_alpha.fma(self.sum_x, x);
        self.sum_x2 = self.one_minus_alpha.fma(self.sum_x2, x * x);
        self.sum_y = self.one_minus_alpha.fma(self.sum_y, y);
        self.sum_xy = self.one_minus_alpha.fma(self.sum_xy, x * y);
        self.sum_y2 = self.one_minus_alpha.fma(self.sum_y2, y * y);
        Ok(())
    }

    /// Slope, or `None` if not primed.
    #[must_use]
    pub fn slope(&self) -> Option<f64> {
        if (self.effective_n as usize) < self.dim() {
            return None;
        }
        if self.intercept {
            let n = self.effective_n;
            let denom = n.fma(self.sum_x2, -(self.sum_x * self.sum_x));
            if denom == 0.0 {
                return None;
            }
            Some(n.fma(self.sum_xy, -(self.sum_x * self.sum_y)) / denom)
        } else {
            if self.sum_x2 == 0.0 {
                return None;
            }
            Some(self.sum_xy / self.sum_x2)
        }
    }

    /// Intercept value, or `None` if not primed or no intercept.
    #[must_use]
    pub fn intercept_value(&self) -> Option<f64> {
        if !self.intercept {
            return None;
        }
        let slope = self.slope()?;
        Some(slope.fma(-self.sum_x, self.sum_y) / self.effective_n)
    }

    /// R² goodness of fit.
    #[must_use]
    #[allow(clippy::suboptimal_flops)]
    pub fn r_squared(&self) -> Option<f64> {
        let slope = self.slope()?;
        let n = self.effective_n;

        let (ss_res, ss_tot) = if self.intercept {
            let intercept = (self.sum_y - slope * self.sum_x) / n;
            let ss_res = self.sum_y2 - 2.0 * slope * self.sum_xy - 2.0 * intercept * self.sum_y
                + slope * slope * self.sum_x2
                + 2.0 * slope * intercept * self.sum_x
                + n * intercept * intercept;
            let ss_tot = self.sum_y2 - self.sum_y * self.sum_y / n;
            (ss_res, ss_tot)
        } else {
            let ss_res = self.sum_y2 - 2.0 * slope * self.sum_xy + slope * slope * self.sum_x2;
            (ss_res, self.sum_y2)
        };

        if ss_tot <= 0.0 {
            return None;
        }

        Some(1.0 - ss_res / ss_tot)
    }

    /// Predict y.
    #[must_use]
    pub fn predict(&self, x: f64) -> Option<f64> {
        let slope = self.slope()?;
        if self.intercept {
            let intercept = self.intercept_value()?;
            Some(slope.fma(x, intercept))
        } else {
            Some(slope * x)
        }
    }

    /// Number of observations.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Effective sample count.
    #[inline]
    #[must_use]
    pub fn effective_count(&self) -> f64 {
        self.effective_n
    }

    /// Alpha.
    #[inline]
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.alpha
    }

    /// Whether primed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        (self.effective_n as usize) >= self.dim()
    }

    /// Whether intercept is included.
    #[inline]
    #[must_use]
    pub fn has_intercept(&self) -> bool {
        self.intercept
    }

    /// Reset. Config unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.sum_x = 0.0;
        self.sum_x2 = 0.0;
        self.sum_y = 0.0;
        self.sum_xy = 0.0;
        self.sum_y2 = 0.0;
        self.effective_n = 0.0;
        self.count = 0;
    }
}

impl EwLinearRegressionBuilder {
    /// Weight on new observation, in (0, 1). Required.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Whether to include the constant term. Default: `true`.
    #[inline]
    #[must_use]
    pub fn intercept(mut self, intercept: bool) -> Self {
        self.intercept = intercept;
        self
    }

    /// Builds the regression.
    pub fn build(self) -> Result<EwLinearRegression, nexus_stats_core::ConfigError> {
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        if !(alpha > 0.0 && alpha < 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1) exclusive",
            ));
        }

        Ok(EwLinearRegression {
            sum_x: 0.0,
            sum_x2: 0.0,
            sum_y: 0.0,
            sum_xy: 0.0,
            sum_y2: 0.0,
            alpha,
            one_minus_alpha: 1.0 - alpha,
            effective_n: 0.0,
            count: 0,
            intercept: self.intercept,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // OLS Linear
    // =========================================================================

    #[test]
    fn linear_exact_fit() {
        let mut r = LinearRegression::new();
        for x in 0..100 {
            r.update(x as f64, 2.0f64.mul_add(x as f64, 3.0)).unwrap();
        }
        assert!((r.slope().unwrap() - 2.0).abs() < 1e-8);
        assert!((r.intercept_value().unwrap() - 3.0).abs() < 1e-8);
        assert!((r.r_squared().unwrap() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn through_origin() {
        let mut r = LinearRegression::through_origin();
        for x in 1..100 {
            r.update(x as f64, 5.0 * x as f64).unwrap();
        }
        assert!((r.slope().unwrap() - 5.0).abs() < 1e-8);
        assert!(r.intercept_value().is_none());
        assert!(!r.has_intercept());
    }

    #[test]
    fn predict_linear() {
        let mut r = LinearRegression::new();
        for x in 0..100 {
            r.update(x as f64, 2.0f64.mul_add(x as f64, 3.0)).unwrap();
        }
        let y = r.predict(50.0).unwrap();
        assert!((y - 103.0).abs() < 1e-6, "predict(50) = {y}");
    }

    #[test]
    fn r_squared_noisy() {
        let mut r = LinearRegression::new();
        let mut rng = 12345u64;
        for x in 0..1000 {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            let noise = (rng % 100) as f64 - 50.0;
            r.update(x as f64, 2.0f64.mul_add(x as f64, noise)).unwrap();
        }
        let r2 = r.r_squared().unwrap();
        assert!(r2 > 0.9 && r2 < 1.0, "R² with noise = {r2}");
    }

    #[test]
    fn constant_y_r_squared_none() {
        let mut r = LinearRegression::new();
        for x in 0..100 {
            r.update(x as f64, 42.0).unwrap();
        }
        assert!(r.r_squared().is_none());
    }

    #[test]
    fn not_primed_returns_none() {
        let mut r = LinearRegression::new();
        assert!(r.slope().is_none());
        r.update(1.0, 2.0).unwrap();
        assert!(r.slope().is_none()); // need 2 with intercept
        r.update(2.0, 4.0).unwrap();
        assert!(r.slope().is_some());
    }

    #[test]
    fn through_origin_primes_at_1() {
        let mut r = LinearRegression::through_origin();
        assert!(!r.is_primed());
        r.update(1.0, 5.0).unwrap();
        assert!(r.is_primed());
        assert!((r.slope().unwrap() - 5.0).abs() < 1e-10);
    }

    #[test]
    fn reset_clears_state() {
        let mut r = LinearRegression::new();
        for x in 0..100 {
            r.update(x as f64, x as f64).unwrap();
        }
        r.reset();
        assert_eq!(r.count(), 0);
        assert!(r.slope().is_none());
        assert!(r.has_intercept());
    }

    #[test]
    fn builder_no_intercept() {
        let r = LinearRegression::builder()
            .intercept(false)
            .build()
            .unwrap();
        assert!(!r.has_intercept());
    }

    #[test]
    fn empty_returns_none() {
        let r = LinearRegression::new();
        assert!(r.slope().is_none());
        assert!(r.intercept_value().is_none());
        assert!(r.predict(1.0).is_none());
        assert!(r.r_squared().is_none());
    }

    #[test]
    fn default_is_new() {
        let r = LinearRegression::default();
        assert_eq!(r.count(), 0);
        assert!(r.has_intercept());
    }

    // =========================================================================
    // EW Linear
    // =========================================================================

    #[test]
    fn ew_basic() {
        let mut r = EwLinearRegression::builder().alpha(0.05).build().unwrap();
        for x in 0..500 {
            r.update(x as f64, 2.0f64.mul_add(x as f64, 3.0)).unwrap();
        }
        let slope = r.slope().unwrap();
        assert!((slope - 2.0).abs() < 0.5, "ew slope = {slope}");
    }

    #[test]
    fn ew_adapts_to_trend_change() {
        let mut r = EwLinearRegression::builder().alpha(0.05).build().unwrap();
        for x in 0..200 {
            r.update(x as f64, x as f64).unwrap();
        }
        for x in 200..500 {
            r.update(x as f64, -(x as f64) + 400.0).unwrap();
        }
        let slope = r.slope().unwrap();
        assert!(slope < 0.0, "slope should be negative, got {slope}");
    }

    #[test]
    fn ew_rejects_invalid_alpha() {
        assert!(EwLinearRegression::builder().alpha(0.0).build().is_err());
        assert!(EwLinearRegression::builder().alpha(1.0).build().is_err());
    }

    #[test]
    fn ew_rejects_missing_alpha() {
        assert!(EwLinearRegression::builder().build().is_err());
    }

    #[test]
    fn ew_reset() {
        let mut r = EwLinearRegression::builder().alpha(0.05).build().unwrap();
        for x in 0..100 {
            r.update(x as f64, x as f64).unwrap();
        }
        r.reset();
        assert_eq!(r.count(), 0);
        assert!(r.slope().is_none());
    }

    #[test]
    fn ols_rejects_nan_and_inf() {
        let mut r = LinearRegression::new();
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

    #[test]
    fn ew_rejects_nan_and_inf() {
        let mut r = EwLinearRegression::builder().alpha(0.05).build().unwrap();
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
