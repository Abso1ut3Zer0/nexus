/// Estimates mean-reversion half-life from lag-1 autocorrelation.
///
/// Computes AC(1) using Welford-style online covariance between
/// consecutive values x_t and x_{t-1}, and online variance of x_t.
/// The half-life is derived as `-ln(2) / ln(AC(1))`, which is only
/// meaningful when AC(1) is in (0, 1).
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::HalfLife;
///
/// let mut hl = HalfLife::new();
///
/// // Feed a trending series (monotonically increasing)
/// for i in 0..100 {
///     hl.update(i as f64).unwrap();
/// }
///
/// // Trending data has high positive AC(1)
/// if let Some(ac) = hl.autocorrelation() {
///     assert!(ac > 0.9);
/// }
/// ```
#[derive(Debug, Clone)]
pub struct HalfLife {
    // Welford-style accumulators for Cov(x_t, x_{t-1}) and Var(x_t).
    // Using the standard online algorithm from Covariance.
    n: u64,
    mean_x: f64,    // running mean of x_t (current value)
    mean_prev: f64, // running mean of x_{t-1} (previous value)
    m2_x: f64,      // sum of (x_t - mean_x)² for variance
    co_moment: f64, // sum of (x_t - mean_x)(x_{t-1} - mean_prev) for covariance
    prev: f64,
    count: u64, // total observations including first (which has no pair)
}

impl Default for HalfLife {
    fn default() -> Self {
        Self::new()
    }
}

impl HalfLife {
    /// Creates a new estimator.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            n: 0,
            mean_x: 0.0,
            mean_prev: 0.0,
            m2_x: 0.0,
            co_moment: 0.0,
            prev: 0.0,
            count: 0,
        }
    }

    /// Creates a builder (for consistency with other types, but this type
    /// has no configuration parameters).
    #[inline]
    #[must_use]
    pub fn builder() -> HalfLifeBuilder {
        HalfLifeBuilder { _private: () }
    }

    /// Feed a value from the time series.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if the value is NaN or infinite.
    #[inline]
    pub fn update(&mut self, value: f64) -> Result<(), crate::DataError> {
        check_finite!(value);

        self.count += 1;

        if self.count >= 2 {
            // We have a pair (prev, value). Update Welford-style covariance.
            // x = current value (x_t), y = previous value (x_{t-1})
            self.n += 1;
            let n = self.n as f64;

            let dx = value - self.mean_x;
            let dy = self.prev - self.mean_prev;

            self.mean_x += dx / n;
            self.mean_prev += dy / n;

            // Welford co-moment: OLD dx (before mean update) × (prev - NEW mean_prev).
            // mean_prev was already updated on line 89, so this uses the new mean.
            // Same pattern as Covariance::update.
            let dx2 = value - self.mean_x;
            self.co_moment += dx * (self.prev - self.mean_prev);

            // Variance of x_t only
            self.m2_x += dx * dx2;
        }

        self.prev = value;
        Ok(())
    }

    /// Estimated lag-1 autocorrelation, or `None` if not primed.
    ///
    /// AC(1) = Cov(x_t, x_{t-1}) / Var(x_t)
    ///
    /// Returns `None` if variance is zero or insufficient data.
    #[inline]
    #[must_use]
    pub fn autocorrelation(&self) -> Option<f64> {
        if self.n < 2 {
            return None;
        }
        if self.m2_x <= 0.0 {
            return None;
        }
        // Both use N-1 denominator, which cancels in the ratio
        Some(self.co_moment / self.m2_x)
    }

    /// Estimated half-life in number of observations.
    ///
    /// Only meaningful when AC(1) is in (0, 1). Returns `None` if
    /// AC(1) is non-positive (not mean-reverting) or data is insufficient.
    #[inline]
    #[must_use]
    pub fn half_life(&self) -> Option<f64> {
        let ac1 = self.autocorrelation()?;
        if ac1 <= 0.0 || ac1 >= 1.0 {
            return None;
        }
        Some(-core::f64::consts::LN_2 / crate::math::ln(ac1))
    }

    /// Number of observations fed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough observations have been fed for estimates.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.n >= 2
    }

    /// Reset all state.
    pub fn reset(&mut self) {
        self.n = 0;
        self.mean_x = 0.0;
        self.mean_prev = 0.0;
        self.m2_x = 0.0;
        self.co_moment = 0.0;
        self.prev = 0.0;
        self.count = 0;
    }
}

/// Builder for [`HalfLife`].
#[derive(Debug, Clone)]
pub struct HalfLifeBuilder {
    _private: (),
}

impl HalfLifeBuilder {
    /// Build the estimator.
    pub fn build(self) -> HalfLife {
        HalfLife::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Simple xorshift64 for deterministic pseudo-random noise.
    fn xorshift64(state: &mut u64) -> f64 {
        let mut s = *state;
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        *state = s;
        // Map to [-1, 1]
        (s as f64 / u64::MAX as f64).mul_add(2.0, -1.0)
    }

    #[test]
    fn ar1_process_half_life() {
        let mut hl = HalfLife::new();

        // AR(1) with phi=0.9: half-life = -ln(2)/ln(0.9) ≈ 6.58
        let phi = 0.9;
        let mut x = 0.0;
        let mut rng = 12345u64;
        for _ in 0..20_000 {
            let eps = xorshift64(&mut rng) * 0.1;
            x = phi * x + eps;
            hl.update(x).unwrap();
        }

        let ac = hl.autocorrelation().unwrap();
        assert!(ac > 0.8 && ac < 0.95, "AC(1) should be ~0.9, got {ac}");

        let h = hl.half_life().unwrap();
        assert!(h > 4.0 && h < 12.0, "half-life should be ~6.58, got {h}");
    }

    #[test]
    fn not_primed_before_3() {
        let mut hl = HalfLife::new();
        hl.update(1.0).unwrap();
        hl.update(2.0).unwrap();
        // n=1 pair, need at least 2 pairs
        assert!(!hl.is_primed());
        assert!(hl.half_life().is_none());
    }

    #[test]
    fn primed_at_3() {
        let mut hl = HalfLife::new();
        hl.update(1.0).unwrap();
        hl.update(2.0).unwrap();
        hl.update(3.0).unwrap();
        assert!(hl.is_primed());
    }

    #[test]
    fn reset_clears_state() {
        let mut hl = HalfLife::new();
        for i in 0..100 {
            hl.update(i as f64).unwrap();
        }
        hl.reset();
        assert_eq!(hl.count(), 0);
        assert!(!hl.is_primed());
    }

    #[test]
    fn nan_rejected() {
        let mut hl = HalfLife::new();
        assert!(hl.update(f64::NAN).is_err());
    }

    #[test]
    fn inf_rejected() {
        let mut hl = HalfLife::new();
        assert!(hl.update(f64::INFINITY).is_err());
    }

    #[test]
    fn constant_series_no_half_life() {
        let mut hl = HalfLife::new();
        for _ in 0..100 {
            hl.update(5.0).unwrap();
        }
        assert!(hl.half_life().is_none());
    }

    #[test]
    fn alternating_series_no_half_life() {
        let mut hl = HalfLife::new();
        // Alternating: AC(1) should be negative → no half-life
        for i in 0..1000 {
            let val = if i % 2 == 0 { 10.0 } else { -10.0 };
            hl.update(val).unwrap();
        }
        let ac = hl.autocorrelation().unwrap();
        assert!(ac < 0.0, "alternating should have negative AC(1), got {ac}");
        assert!(hl.half_life().is_none());
    }
}
