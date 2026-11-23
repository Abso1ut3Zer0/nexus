use nexus_stats_core::Direction;
use nexus_stats_core::statistics::Welford;
use nexus_stats_smoothing::Ema;

/// Adaptive threshold — z-score anomaly detection using EMA baseline + Welford std dev.
///
/// Internally composes an EMA (for the moving baseline) with Welford's
/// algorithm (for standard deviation). Signals anomaly when the z-score
/// of a sample exceeds the configured threshold.
///
/// # Use Cases
/// - Latency anomaly detection with adaptive baseline
/// - Price spike detection relative to recent volatility
/// - Any signal where "abnormal" depends on recent context
#[derive(Debug, Clone)]
pub struct AdaptiveThreshold {
    ema: Ema,
    welford: Welford,
    z_threshold: f64,
    last_z: f64,
    min_samples: u64,
}
/// Builder for [`
#[doc = stringify!(AdaptiveThreshold)]
/// `].
#[derive(Debug, Clone)]
pub struct AdaptiveThresholdBuilder {
    alpha: Option<f64>,
    z_threshold: f64,
    min_samples: u64,
    seed_mean: Option<f64>,
    seed_std_dev: Option<f64>,
}
impl AdaptiveThreshold {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> AdaptiveThresholdBuilder {
        AdaptiveThresholdBuilder {
            alpha: None,
            z_threshold: 3.0,
            min_samples: 20,
            seed_mean: None,
            seed_std_dev: None,
        }
    }
    /// Feeds a sample. Returns anomaly direction once primed.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(
        &mut self,
        sample: f64,
    ) -> Result<Option<Direction>, nexus_stats_core::DataError> {
        check_finite!(sample);
        self.ema.update(sample);
        self.welford.update(sample);
        if self.welford.count() < self.min_samples {
            return Ok(None);
        }
        let Some(baseline) = self.ema.value() else {
            return Ok(None);
        };
        let sd = match self.welford.std_dev() {
            Some(v) if v > 0.0 => v,
            _ => {
                self.last_z = 0.0;
                return Ok(Some(Direction::Neutral));
            }
        };
        self.last_z = (sample - baseline) / sd;
        Ok(if self.last_z > self.z_threshold {
            Some(Direction::Rising)
        } else if self.last_z < -self.z_threshold {
            Some(Direction::Falling)
        } else {
            Some(Direction::Neutral)
        })
    }
    /// Current EMA baseline, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn baseline(&self) -> Option<f64> {
        if self.welford.count() >= self.min_samples {
            self.ema.value()
        } else {
            None
        }
    }
    /// Current standard deviation from Welford, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn std_dev(&self) -> Option<f64> {
        if self.welford.count() >= self.min_samples {
            self.welford.std_dev()
        } else {
            None
        }
    }
    /// Last computed z-score, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn z_score(&self) -> Option<f64> {
        if self.welford.count() >= self.min_samples {
            Some(self.last_z)
        } else {
            None
        }
    }
    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.welford.count()
    }
    /// Whether enough data has been collected.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.welford.count() >= self.min_samples
    }
    /// Resets to empty state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.ema.reset();
        self.welford.reset();
        self.last_z = 0.0;
    }
    /// Updates the z-score threshold without resetting state.
    ///
    /// # Errors
    ///
    /// z must be positive.
    #[inline]
    pub fn reconfigure_z_threshold(&mut self, z: f64) -> Result<(), nexus_stats_core::ConfigError> {
        if !nexus_stats_core::math::positive_finite(z) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "z_threshold must be positive",
            ));
        }
        self.z_threshold = z;
        Ok(())
    }
}
impl AdaptiveThresholdBuilder {
    /// EMA smoothing factor for the baseline.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }
    /// Halflife for baseline smoothing.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.alpha = Some(nexus_stats_core::math::alpha_from_halflife(halflife));
        self
    }
    /// Span for baseline smoothing.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.alpha = Some(2.0 / (n as f64 + 1.0));
        self
    }
    /// Z-score threshold for anomaly detection. Default: 3.0.
    #[inline]
    #[must_use]
    pub fn z_threshold(mut self, z: f64) -> Self {
        self.z_threshold = z;
        self
    }
    /// Minimum samples before detection activates. Default: 20.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }
    /// Pre-load the baseline from calibration data: the mean seeds the
    /// EMA and `std_dev` seeds the spread estimate as two samples, so the
    /// detector is primed after at most two updates (`min_samples` is
    /// capped at 2 when seeded).
    #[inline]
    #[must_use]
    pub fn seed(mut self, mean: f64, std_dev: f64) -> Self {
        self.seed_mean = Some(mean);
        self.seed_std_dev = Some(std_dev);
        self
    }
    /// Builds the adaptive threshold detector.
    ///
    /// # Errors
    ///
    /// - Alpha must have been set.
    /// - Alpha must be in (0, 1) exclusive.
    /// - z_threshold must be positive.
    #[inline]
    pub fn build(self) -> Result<AdaptiveThreshold, nexus_stats_core::ConfigError> {
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        if !nexus_stats_core::math::in_unit_interval(alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1)",
            ));
        }
        if !nexus_stats_core::math::positive_finite(self.z_threshold) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "z_threshold must be positive",
            ));
        }
        let ema = if let Some(seed_mean) = self.seed_mean {
            Ema::builder()
                .alpha(alpha)
                .seed(seed_mean)
                .min_samples(1)
                .build()?
        } else {
            Ema::builder().alpha(alpha).min_samples(1).build()?
        };
        // A seed stands in for two calibration samples with the given
        // spread: the Welford starts at count 2 with m2 = std_dev², so
        // std_dev() reproduces it, and priming comes at the smaller of
        // 2 and min_samples.
        let (welford, min_samples) = match (self.seed_mean, self.seed_std_dev) {
            (Some(mean), Some(std_dev)) => {
                if !nexus_stats_core::math::nonnegative_finite(std_dev) {
                    return Err(nexus_stats_core::ConfigError::Invalid(
                        "seed std_dev must be non-negative and finite",
                    ));
                }
                let sd = std_dev;
                (
                    Welford::from_parts(2, mean, sd * sd)?,
                    self.min_samples.min(2),
                )
            }
            _ => (Welford::new(), self.min_samples),
        };
        Ok(AdaptiveThreshold {
            ema,
            welford,
            z_threshold: self.z_threshold,
            last_z: 0.0,
            min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_high_anomaly() {
        let mut at = AdaptiveThreshold::builder()
            .alpha(0.1)
            .z_threshold(2.0)
            .min_samples(20)
            .build()
            .unwrap();

        // Feed normal samples around 100
        for _ in 0..50 {
            let _ = at.update(100.0);
        }

        // Spike — should be anomalous
        let result = at.update(200.0).unwrap();
        assert_eq!(result, Some(Direction::Rising));
    }

    #[test]
    fn detects_low_anomaly() {
        let mut at = AdaptiveThreshold::builder()
            .alpha(0.1)
            .z_threshold(2.0)
            .min_samples(20)
            .build()
            .unwrap();

        for _ in 0..50 {
            let _ = at.update(100.0);
        }

        // Drop — need some variance first
        // Feed varying input to build std_dev
        let mut at2 = AdaptiveThreshold::builder()
            .alpha(0.1)
            .z_threshold(2.0)
            .min_samples(20)
            .build()
            .unwrap();

        for i in 0..50 {
            let _ = at2.update(100.0 + (i % 5) as f64);
        }

        let result = at2.update(50.0).unwrap();
        assert_eq!(result, Some(Direction::Falling));
    }

    #[test]
    fn no_false_positive_at_normal() {
        let mut at = AdaptiveThreshold::builder()
            .alpha(0.1)
            .z_threshold(3.0)
            .min_samples(20)
            .build()
            .unwrap();

        for i in 0..100 {
            let sample = 100.0 + (i % 3) as f64;
            let result = at.update(sample).unwrap();
            if let Some(anomaly) = result {
                assert_eq!(anomaly, Direction::Neutral, "false positive at sample {i}");
            }
        }
    }

    #[test]
    fn priming() {
        let mut at = AdaptiveThreshold::builder()
            .alpha(0.1)
            .min_samples(10)
            .build()
            .unwrap();

        for _ in 0..9 {
            assert!(at.update(100.0).unwrap().is_none());
        }
        assert!(!at.is_primed());
        assert!(at.update(100.0).unwrap().is_some());
        assert!(at.is_primed());
    }

    #[test]
    fn seeded_startup() {
        let mut at = AdaptiveThreshold::builder()
            .alpha(0.1)
            .z_threshold(3.0)
            .seed(100.0, 5.0)
            .build()
            .unwrap();

        // Should be primed quickly since seeded
        let _ = at.update(100.0);
        let _ = at.update(100.0);
        assert!(at.is_primed());
        assert!(at.baseline().is_some());
    }

    #[test]
    fn reset() {
        let mut at = AdaptiveThreshold::builder()
            .alpha(0.1)
            .min_samples(5)
            .build()
            .unwrap();

        for _ in 0..20 {
            let _ = at.update(100.0);
        }
        at.reset();
        assert_eq!(at.count(), 0);
        assert!(!at.is_primed());
    }

    #[test]
    fn reconfigure_z_threshold_preserves_state() {
        let mut at = AdaptiveThreshold::builder()
            .alpha(0.1)
            .z_threshold(3.0)
            .min_samples(10)
            .build()
            .unwrap();

        for i in 0..20 {
            let _ = at.update(100.0 + (i % 5) as f64);
        }
        let count_before = at.count();

        at.reconfigure_z_threshold(1.0).unwrap();

        // State preserved
        assert_eq!(at.count(), count_before);
        assert!(at.is_primed());
    }

    #[test]
    fn errors_without_alpha() {
        let result = AdaptiveThreshold::builder().build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("alpha"))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut at = AdaptiveThreshold::builder()
            .alpha(0.1)
            .z_threshold(3.0)
            .min_samples(5)
            .build()
            .unwrap();

        assert_eq!(
            at.update(f64::NAN).unwrap_err(),
            nexus_stats_core::DataError::NotANumber
        );
        assert_eq!(
            at.update(f64::INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(
            at.update(f64::NEG_INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(at.count(), 0);
    }
}
