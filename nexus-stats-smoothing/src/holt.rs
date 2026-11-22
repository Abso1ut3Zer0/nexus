use nexus_stats_core::math::MulAdd;

/// Holt's Double Exponential Smoothing — level + trend tracking.
///
/// Separates the signal into level (current smoothed value) and trend
/// (rate of change). Detects not just "value is high" but "value is
/// getting worse over time."
///
/// # Use Cases
/// - Trend detection ("latency is increasing linearly")
/// - Capacity planning and degradation forecasting
/// - Adaptive baselines that track drift
///
/// # Choosing parameters
///
/// Start `alpha` where a plain EMA on the same data would have it, and
/// `beta` several times smaller: a trend that adapts as fast as the level
/// oscillates. If forecasts overshoot, lower `beta`. If the level lags,
/// raise `alpha`.
#[derive(Debug, Clone)]
pub struct Holt {
    alpha: f64,
    beta: f64,
    one_minus_alpha: f64,
    one_minus_beta: f64,
    level: f64,
    trend: f64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`Holt`].
#[derive(Debug, Clone)]
pub struct HoltBuilder {
    alpha: Option<f64>,
    beta: Option<f64>,
    min_samples: u64,
    seed_level: Option<f64>,
    seed_trend: Option<f64>,
}

impl Holt {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> HoltBuilder {
        HoltBuilder {
            alpha: None,
            beta: None,
            min_samples: 2,
            seed_level: None,
            seed_trend: None,
        }
    }

    /// Feeds a sample. Returns `(level, trend)` once primed.
    ///
    /// First sample sets the level. Second sample initializes the trend.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(
        &mut self,
        sample: f64,
    ) -> Result<Option<(f64, f64)>, nexus_stats_core::DataError> {
        check_finite!(sample);
        self.count += 1;

        if self.count == 1 {
            self.level = sample;
            self.trend = 0.0;
        } else if self.count == 2 {
            let prev_level = self.level;
            self.level = sample;
            self.trend = sample - prev_level;
        } else {
            let prev_level = self.level;
            // Level: alpha * sample + (1 - alpha) * (prev_level + prev_trend)
            self.level = self
                .alpha
                .fma(sample, self.one_minus_alpha * (prev_level + self.trend));
            // Trend: beta * (level - prev_level) + (1 - beta) * prev_trend
            self.trend = self
                .beta
                .fma(self.level - prev_level, self.one_minus_beta * self.trend);
        }

        if self.count >= self.min_samples {
            Ok(Some((self.level, self.trend)))
        } else {
            Ok(None)
        }
    }

    /// Current smoothed level, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn level(&self) -> Option<f64> {
        if self.count >= self.min_samples {
            Some(self.level)
        } else {
            None
        }
    }

    /// Current trend (rate of change), or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn trend(&self) -> Option<f64> {
        if self.count >= self.min_samples {
            Some(self.trend)
        } else {
            None
        }
    }

    /// Forecast: `level + steps * trend`. Or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn forecast(&self, steps: u64) -> Option<f64> {
        if self.count >= self.min_samples {
            Some(self.trend.fma(steps as f64, self.level))
        } else {
            None
        }
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether Holt's has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.level = 0.0;
        self.trend = 0.0;
        self.count = 0;
    }
}

impl HoltBuilder {
    /// Level smoothing factor. Must be in (0, 1) exclusive.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Trend smoothing factor. Must be in (0, 1) exclusive.
    #[inline]
    #[must_use]
    pub fn beta(mut self, beta: f64) -> Self {
        self.beta = Some(beta);
        self
    }

    /// Minimum samples before values are valid. Default: 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Pre-loads the level and trend from calibration data.
    ///
    /// When seeded, `is_primed()` returns true immediately.
    #[inline]
    #[must_use]
    pub fn seed(mut self, level: f64, trend: f64) -> Self {
        self.seed_level = Some(level);
        self.seed_trend = Some(trend);
        self
    }

    /// Builds the Holt's smoother.
    ///
    /// # Errors
    ///
    /// - Alpha and beta must have been set.
    /// - Both must be in (0, 1) exclusive.
    #[inline]
    pub fn build(self) -> Result<Holt, nexus_stats_core::ConfigError> {
        if self.min_samples == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "min_samples must be >= 1",
            ));
        }
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        let beta = self
            .beta
            .ok_or(nexus_stats_core::ConfigError::Missing("beta"))?;
        if !nexus_stats_core::math::in_unit_interval(alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "Holt alpha must be in (0, 1)",
            ));
        }
        if !(beta > 0.0 && beta < 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "Holt beta must be in (0, 1)",
            ));
        }

        let (level, trend, count) = match (self.seed_level, self.seed_trend) {
            (Some(l), Some(t)) => (l, t, self.min_samples),
            _ => (0.0, 0.0, 0),
        };

        Ok(Holt {
            alpha,
            beta,
            one_minus_alpha: 1.0 - alpha,
            one_minus_beta: 1.0 - beta,
            level,
            trend,
            count,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_input_zero_trend() {
        let mut h = Holt::builder().alpha(0.3).beta(0.1).build().unwrap();

        for _ in 0..100 {
            h.update(50.0).unwrap();
        }

        let trend = h.trend().unwrap();
        assert!(
            trend.abs() < 0.01,
            "constant input should have ~zero trend, got {trend}"
        );
    }

    #[test]
    fn linear_input_correct_trend() {
        let mut h = Holt::builder().alpha(0.5).beta(0.5).build().unwrap();

        // Feed linear data: 0, 10, 20, 30, ...
        for i in 0..100 {
            h.update(i as f64 * 10.0).unwrap();
        }

        let trend = h.trend().unwrap();
        // Should converge to ~10.0 (the slope)
        assert!(
            (trend - 10.0).abs() < 1.0,
            "linear trend should be ~10, got {trend}"
        );
    }

    #[test]
    fn forecast_accuracy() {
        let mut h = Holt::builder().alpha(0.5).beta(0.5).build().unwrap();

        for i in 0..50 {
            h.update(i as f64 * 10.0).unwrap();
        }

        let forecast_5 = h.forecast(5).unwrap();
        let level = h.level().unwrap();
        let trend = h.trend().unwrap();

        // forecast(5) = level + 5 * trend
        let expected = 5.0f64.fma(trend, level);
        assert!((forecast_5 - expected).abs() < 1e-10);
    }

    #[test]
    fn priming_needs_two_samples() {
        let mut h = Holt::builder().alpha(0.3).beta(0.1).build().unwrap();

        assert!(h.update(10.0).unwrap().is_none()); // first sample — not primed
        assert!(h.update(20.0).unwrap().is_some()); // second sample — primed
    }

    #[test]
    fn reset_clears() {
        let mut h = Holt::builder().alpha(0.3).beta(0.1).build().unwrap();
        h.update(10.0).unwrap();
        h.update(20.0).unwrap();

        h.reset();
        assert_eq!(h.count(), 0);
        assert!(h.level().is_none());
        assert!(h.trend().is_none());
    }

    #[test]
    fn seeded_is_primed() {
        let h = Holt::builder()
            .alpha(0.3)
            .beta(0.1)
            .seed(100.0, 5.0)
            .build()
            .unwrap();

        assert!(h.is_primed());
        assert!((h.level().unwrap() - 100.0).abs() < 1e-10);
        assert!((h.trend().unwrap() - 5.0).abs() < 1e-10);
    }

    #[test]
    fn errors_without_alpha() {
        let result = Holt::builder().beta(0.1).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("alpha"))
        ));
    }

    #[test]
    fn errors_without_beta() {
        let result = Holt::builder().alpha(0.3).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("beta"))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut h = Holt::builder().alpha(0.3).beta(0.1).build().unwrap();
        assert!(matches!(
            h.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        assert!(matches!(
            h.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert!(matches!(
            h.update(f64::NEG_INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert_eq!(h.count(), 0);
    }
}
