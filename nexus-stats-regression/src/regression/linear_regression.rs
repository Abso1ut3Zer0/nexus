// Online Linear Regression — Closed-Form OLS + EW Variant
//
// Minimal state (5 accumulators, ~48 bytes) with direct 2×2 solve.
// No loops, no Gaussian elimination — just arithmetic.

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
    // With an intercept: running means and co-moments about them (Welford),
    // so a large offset in x or y never cancels. The means are kept relative
    // to the latest sample (`anchor_*`), so every quantity the update rounds
    // is on the scale of the data's spread, not its offset. Through the
    // origin: raw sums of squares and cross products, which carry no
    // subtraction.
    anchor_x: f64,
    anchor_y: f64,
    mean_x: f64,
    mean_y: f64,
    sxx: f64,
    sxy: f64,
    syy: f64,
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
            anchor_x: 0.0,
            anchor_y: 0.0,
            mean_x: 0.0,
            mean_y: 0.0,
            sxx: 0.0,
            sxy: 0.0,
            syy: 0.0,
            count: 0,
            intercept: true,
        }
    }

    /// Linear regression through the origin: `y = ax`.
    #[inline]
    #[must_use]
    pub fn through_origin() -> Self {
        Self {
            anchor_x: 0.0,
            anchor_y: 0.0,
            mean_x: 0.0,
            mean_y: 0.0,
            sxx: 0.0,
            sxy: 0.0,
            syy: 0.0,
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
        if self.intercept {
            let w = 1.0 / self.count as f64;
            // Offsets from the previous anchor; exact for nearby values.
            let sx = x - self.anchor_x;
            let sy = y - self.anchor_y;
            let dx = sx - self.mean_x; // x minus the old mean
            let dy = sy - self.mean_y;
            let ex = w.fma(-dx, dx); // x minus the new mean: dx * (1 - w)
            let ey = w.fma(-dy, dy);
            self.sxx = dx.fma(ex, self.sxx);
            self.sxy = dx.fma(ey, self.sxy);
            self.syy = dy.fma(ey, self.syy);
            // Re-anchor on this sample: the new mean sits at -e from it.
            self.anchor_x = x;
            self.anchor_y = y;
            self.mean_x = -ex;
            self.mean_y = -ey;
        } else {
            self.sxx = x.fma(x, self.sxx);
            self.sxy = x.fma(y, self.sxy);
            self.syy = y.fma(y, self.syy);
        }
        Ok(())
    }

    /// Slope of the fit, or `None` if not primed.
    #[must_use]
    pub fn slope(&self) -> Option<f64> {
        if !self.is_primed() {
            return None;
        }
        // `sxx` is zero only when every x is the same (exactly: the anchored
        // update rounds nothing for equal inputs), and never negative. Any
        // representable spread, even one tick at a large offset, is real.
        if self.sxx <= 0.0 {
            return None;
        }
        Some(self.sxy / self.sxx)
    }

    /// Intercept value, or `None` if not primed or no intercept.
    #[must_use]
    pub fn intercept(&self) -> Option<f64> {
        if !self.intercept {
            return None;
        }
        let slope = self.slope()?;
        Some(slope.fma(-(self.anchor_x + self.mean_x), self.anchor_y + self.mean_y))
    }

    /// R² goodness of fit, or `None` if not enough data.
    ///
    /// With intercept: centered R² = 1 - SS_res/SS_tot.
    /// Without intercept: uncentered R² = 1 - SS_res/Σy².
    #[must_use]
    pub fn r_squared(&self) -> Option<f64> {
        // Both modes reduce to sxy^2 / (sxx * syy): centered sums with an
        // intercept, raw sums through the origin.
        let slope = self.slope()?;
        if self.syy <= 0.0 {
            return None;
        }
        Some((slope * self.sxy / self.syy).clamp(0.0, 1.0))
    }

    /// Predict y for a given x.
    #[must_use]
    pub fn predict(&self, x: f64) -> Option<f64> {
        let slope = self.slope()?;
        if self.intercept {
            // About the mean, so a large x offset cancels before it multiplies.
            Some(slope.fma(
                (x - self.anchor_x) - self.mean_x,
                self.anchor_y + self.mean_y,
            ))
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
        self.anchor_x = 0.0;
        self.anchor_y = 0.0;
        self.mean_x = 0.0;
        self.mean_y = 0.0;
        self.sxx = 0.0;
        self.sxy = 0.0;
        self.syy = 0.0;
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
    #[inline]
    pub fn build(self) -> Result<LinearRegression, nexus_stats_core::ConfigError> {
        Ok(LinearRegression {
            anchor_x: 0.0,
            anchor_y: 0.0,
            mean_x: 0.0,
            mean_y: 0.0,
            sxx: 0.0,
            sxy: 0.0,
            syy: 0.0,
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
    // Exponentially weighted Welford (West), anchored: the means are kept
    // relative to the latest sample (`anchor_*`), so every quantity the
    // update rounds is on the scale of the data's spread, not its offset.
    // Unanchored, the rounding of a mean near 1e15 does not decay away
    // under exponential weights and swamps a spread of a few hundred.
    anchor_x: f64,
    anchor_y: f64,
    mean_x: f64,
    mean_y: f64,
    sxx: f64,
    sxy: f64,
    syy: f64,
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
        let decay = self.one_minus_alpha;
        self.effective_n = decay.fma(self.effective_n, 1.0);
        if self.intercept {
            let w = 1.0 / self.effective_n;
            // Offsets from the previous anchor; exact for nearby values.
            let sx = x - self.anchor_x;
            let sy = y - self.anchor_y;
            let dx = sx - self.mean_x; // x minus the old mean
            let dy = sy - self.mean_y;
            let ex = w.fma(-dx, dx); // x minus the new mean: dx * (1 - w)
            let ey = w.fma(-dy, dy);
            self.sxx = decay.fma(self.sxx, dx * ex);
            self.sxy = decay.fma(self.sxy, dx * ey);
            self.syy = decay.fma(self.syy, dy * ey);
            // Re-anchor on this sample: the new mean sits at -e from it.
            self.anchor_x = x;
            self.anchor_y = y;
            self.mean_x = -ex;
            self.mean_y = -ey;
        } else {
            self.sxx = decay.fma(self.sxx, x * x);
            self.sxy = decay.fma(self.sxy, x * y);
            self.syy = decay.fma(self.syy, y * y);
        }
        Ok(())
    }

    /// Slope, or `None` if not primed.
    #[must_use]
    pub fn slope(&self) -> Option<f64> {
        if !self.is_primed() {
            return None;
        }
        // `sxx` is zero only when every x is the same (exactly: the anchored
        // update rounds nothing for equal inputs), and never negative. Any
        // representable spread, even one tick at a large offset, is real.
        if self.sxx <= 0.0 {
            return None;
        }
        Some(self.sxy / self.sxx)
    }

    /// Intercept value, or `None` if not primed or no intercept.
    #[must_use]
    pub fn intercept(&self) -> Option<f64> {
        if !self.intercept {
            return None;
        }
        let slope = self.slope()?;
        Some(slope.fma(-(self.anchor_x + self.mean_x), self.anchor_y + self.mean_y))
    }

    /// R² goodness of fit.
    #[must_use]
    pub fn r_squared(&self) -> Option<f64> {
        // Both modes reduce to sxy^2 / (sxx * syy): centered sums with an
        // intercept, raw sums through the origin.
        let slope = self.slope()?;
        if self.syy <= 0.0 {
            return None;
        }
        Some((slope * self.sxy / self.syy).clamp(0.0, 1.0))
    }

    /// Predict y.
    #[must_use]
    pub fn predict(&self, x: f64) -> Option<f64> {
        let slope = self.slope()?;
        if self.intercept {
            // About the mean, so a large x offset cancels before it multiplies.
            Some(slope.fma(
                (x - self.anchor_x) - self.mean_x,
                self.anchor_y + self.mean_y,
            ))
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
        self.anchor_x = 0.0;
        self.anchor_y = 0.0;
        self.mean_x = 0.0;
        self.mean_y = 0.0;
        self.sxx = 0.0;
        self.sxy = 0.0;
        self.syy = 0.0;
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

    /// Sets `alpha` from a half-life in samples: `1 - exp(-ln 2 / halflife)`.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.alpha = Some(nexus_stats_core::math::alpha_from_halflife(halflife));
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
    #[inline]
    pub fn build(self) -> Result<EwLinearRegression, nexus_stats_core::ConfigError> {
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        if !nexus_stats_core::math::in_unit_interval(alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1) exclusive",
            ));
        }
        // The effective sample size approaches 1/alpha from below and must
        // reach the number of coefficients for the fit to prime at all.
        let dim = if self.intercept { 2.0 } else { 1.0 };
        if alpha >= 1.0 / dim {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be below 1/(number of coefficients) or the fit never primes",
            ));
        }

        Ok(EwLinearRegression {
            anchor_x: 0.0,
            anchor_y: 0.0,
            mean_x: 0.0,
            mean_y: 0.0,
            sxx: 0.0,
            sxy: 0.0,
            syy: 0.0,
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
        assert!((r.intercept().unwrap() - 3.0).abs() < 1e-8);
        assert!((r.r_squared().unwrap() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn through_origin() {
        let mut r = LinearRegression::through_origin();
        for x in 1..100 {
            r.update(x as f64, 5.0 * x as f64).unwrap();
        }
        assert!((r.slope().unwrap() - 5.0).abs() < 1e-8);
        assert!(r.intercept().is_none());
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
        assert!(r.intercept().is_none());
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

    /// Constant x leaves the denominator at rounding scale, not exactly zero.
    #[test]
    fn constant_x_has_no_slope() {
        let mut lr = LinearRegression::new();
        for i in 0..100 {
            lr.update(0.1, f64::from(i)).unwrap();
        }
        assert!(lr.slope().is_none());
        assert!(lr.predict(0.1).is_none());
        let mut ew = EwLinearRegression::builder().alpha(0.1).build().unwrap();
        for i in 0..100 {
            ew.update(0.1, f64::from(i)).unwrap();
        }
        assert!(ew.slope().is_none());
    }

    #[test]
    fn ew_alpha_that_can_never_prime_is_rejected() {
        assert!(EwLinearRegression::builder().alpha(0.5).build().is_err());
        assert!(EwLinearRegression::builder().alpha(0.49).build().is_ok());
    }

    // Offsets typical of real inputs: unix timestamps in x, prices in y. Raw
    // power sums cancel to nothing here; the centered, anchored update must
    // stay at f64 precision.
    const TIME_BASES: [f64; 3] = [1.7e9, 1.7e12, 1.7e15];

    /// Increasing integer ticks with uneven gaps, so the running mean is not
    /// a round number and rounding it at a large offset would show.
    fn irregular_tick(i: u32) -> f64 {
        f64::from(7 * i + (i * i) % 7)
    }

    #[test]
    fn timestamp_x_fits_a_line() {
        for base in TIME_BASES {
            let mut r = LinearRegression::new();
            for i in 0..3000 {
                let d = irregular_tick(i);
                r.update(base + d, 2.0f64.mul_add(d, 1.0)).unwrap();
            }
            let slope = r.slope().unwrap();
            assert!((slope - 2.0).abs() < 1e-12, "base {base}: slope {slope}");
            let p = r.predict(base + 30_000.0).unwrap();
            assert!((p - 60_001.0).abs() < 1e-6, "base {base}: predict {p}");
            let r2 = r.r_squared().unwrap();
            assert!((r2 - 1.0).abs() < 1e-12, "base {base}: r2 {r2}");
        }
    }

    #[test]
    fn ew_timestamp_x_fits_a_line() {
        for base in TIME_BASES {
            let mut r = EwLinearRegression::builder().alpha(0.01).build().unwrap();
            for i in 0..3000 {
                let d = irregular_tick(i);
                r.update(base + d, 2.0f64.mul_add(d, 1.0)).unwrap();
            }
            let slope = r.slope().unwrap();
            assert!((slope - 2.0).abs() < 1e-12, "base {base}: slope {slope}");
            let p = r.predict(base + 30_000.0).unwrap();
            assert!((p - 60_001.0).abs() < 1e-6, "base {base}: predict {p}");
        }
    }

    #[test]
    fn price_level_y_keeps_a_small_slope() {
        let mut r = LinearRegression::new();
        let mut ew = EwLinearRegression::builder().alpha(0.01).build().unwrap();
        for i in 0..3000 {
            let d = f64::from(i);
            let y = 0.002f64.mul_add(d, 50_000.0);
            r.update(d, y).unwrap();
            ew.update(d, y).unwrap();
        }
        for slope in [r.slope().unwrap(), ew.slope().unwrap()] {
            assert!((slope / 0.002 - 1.0).abs() < 1e-9, "slope {slope}");
        }
    }

    #[test]
    fn one_tick_spread_at_a_large_offset_has_a_slope() {
        let mut r = LinearRegression::new();
        let mut ew = EwLinearRegression::builder().alpha(0.01).build().unwrap();
        for i in 0..1000 {
            let tick = f64::from(i % 2);
            r.update(1.7e15 + tick, 3.0 * tick).unwrap();
            ew.update(1.7e15 + tick, 3.0 * tick).unwrap();
        }
        for slope in [r.slope(), ew.slope()] {
            let slope = slope.unwrap();
            assert!((slope - 3.0).abs() < 1e-12, "slope {slope}");
        }
    }

    #[test]
    fn constant_timestamp_x_has_no_slope() {
        for base in TIME_BASES {
            let mut r = LinearRegression::new();
            let mut ew = EwLinearRegression::builder().alpha(0.01).build().unwrap();
            for i in 0..100 {
                r.update(base, f64::from(i)).unwrap();
                ew.update(base, f64::from(i)).unwrap();
            }
            assert_eq!(r.slope(), None, "base {base}");
            assert_eq!(ew.slope(), None, "base {base}");
        }
    }

    /// Small deterministic generator for the noisy-data test.
    struct Lcg(u64);

    impl Lcg {
        /// Uniform in [-0.5, 0.5).
        fn next_centered(&mut self) -> f64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (self.0 >> 11) as f64 / (1u64 << 53) as f64 - 0.5
        }
    }

    /// Weighted two-pass least squares: (mean x, mean y, slope).
    fn two_pass_fit(xs: &[f64], ys: &[f64], ws: &[f64]) -> (f64, f64, f64) {
        let sw: f64 = ws.iter().sum();
        let mx = xs.iter().zip(ws).map(|(x, w)| w * x).sum::<f64>() / sw;
        let my = ys.iter().zip(ws).map(|(y, w)| w * y).sum::<f64>() / sw;
        let mut sxx = 0.0;
        let mut sxy = 0.0;
        for i in 0..xs.len() {
            let dx = xs[i] - mx;
            sxx = (ws[i] * dx).mul_add(dx, sxx);
            sxy = (ws[i] * dx).mul_add(ys[i] - my, sxy);
        }
        (mx, my, sxy / sxx)
    }

    // Exact lines cannot tell a wrong weight or a wrong reference point from
    // the right one: every point is on the fit. Noisy data can.
    #[test]
    fn noisy_fit_matches_a_two_pass_reference() {
        use alloc::vec;
        use alloc::vec::Vec;

        let n = 2000;
        let alpha = 0.01;
        for base in [0.0, 1.7e9] {
            let mut rng = Lcg(12_345);
            let mut r = LinearRegression::new();
            let mut ew = EwLinearRegression::builder().alpha(alpha).build().unwrap();
            let mut xs = Vec::new();
            let mut ys = Vec::new();
            for i in 0..n {
                let x = 3.0f64.mul_add(rng.next_centered(), 0.7 * f64::from(i));
                let y = 5.0f64.mul_add(rng.next_centered(), 1.5f64.mul_add(x, -4.0));
                r.update(base + x, y).unwrap();
                ew.update(base + x, y).unwrap();
                // The offset the regression actually saw, exact after rounding.
                xs.push((base + x) - base);
                ys.push(y);
            }
            let flat = vec![1.0; n as usize];
            let decayed: Vec<f64> = (0..n).map(|i| (1.0 - alpha).powi(n - 1 - i)).collect();
            let at = 500.0;
            for (name, fit, (mx, my, slope)) in [
                (
                    "plain",
                    r.slope().zip(r.predict(base + at)),
                    two_pass_fit(&xs, &ys, &flat),
                ),
                (
                    "ew",
                    ew.slope().zip(ew.predict(base + at)),
                    two_pass_fit(&xs, &ys, &decayed),
                ),
            ] {
                let (got_slope, got_pred) = fit.unwrap();
                let want_pred = slope.mul_add(at - mx, my);
                assert!(
                    (got_slope - slope).abs() < 1e-12,
                    "{name} base {base}: slope {got_slope} vs {slope}"
                );
                assert!(
                    (got_pred - want_pred).abs() < 1e-9,
                    "{name} base {base}: predict {got_pred} vs {want_pred}"
                );
                if base == 0.0 {
                    let got_icpt = if name == "plain" {
                        r.intercept()
                    } else {
                        ew.intercept()
                    }
                    .unwrap();
                    let want_icpt = slope.mul_add(-mx, my);
                    assert!(
                        (got_icpt - want_icpt).abs() < 1e-9,
                        "{name}: intercept {got_icpt} vs {want_icpt}"
                    );
                }
            }
        }
    }
}
