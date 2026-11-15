use crate::Condition;
use crate::math::MulAdd;

/// Smoothed error rate tracker.
///
/// Internally uses an EMA where success = 0.0 and failure = 1.0 (or
/// weighted). The smoothed value approximates the recent error rate.
///
/// # Use Cases
/// - API error rate monitoring
/// - Exchange rejection rate tracking
/// - Weighted severity tracking (critical failures count more)
///
/// # Weighted outcomes
///
/// `update_weighted(false, 2.0)` feeds 2.0 to the EMA (a failure that
/// counts double). With weights > 1.0, the smoothed "rate" can exceed
/// 1.0 — it becomes a severity-weighted signal rather than a pure rate.
///
/// # Weighting clock
///
/// Per `update` call: every sample counts the same. Correct when samples
/// are evenly spaced, or one per event where per-event weighting is wanted.
/// Never feed it from a loop whose iteration time depends on the quantity
/// being measured.
#[derive(Debug, Clone)]
pub struct ErrorRate {
    alpha: f64,
    one_minus_alpha: f64,
    value: f64,
    threshold: f64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`ErrorRate`].
#[derive(Debug, Clone)]
pub struct ErrorRateBuilder {
    alpha: Option<f64>,
    threshold: Option<f64>,
    min_samples: u64,
}

impl ErrorRate {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> ErrorRateBuilder {
        ErrorRateBuilder {
            alpha: None,
            threshold: None,
            min_samples: 1,
        }
    }

    /// Updates with an outcome with default weight 1.0.
    #[inline]
    #[must_use]
    pub fn update(&mut self, success: bool) -> Option<Condition> {
        // Weight 1.0 is always finite — bypass validation.
        self.update_weighted(success, 1.0).unwrap()
    }

    /// Updates with an outcome with a severity weight.
    ///
    /// Success feeds `0.0`, failure feeds `weight`. The EMA smooths
    /// this signal. With `weight=1.0`, the smoothed value is the
    /// recent error rate in [0, 1]. With `weight > 1.0`, it can exceed 1.0.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the weight is NaN, or
    /// `DataError::Infinite` if the weight is infinite.
    #[inline]
    pub fn update_weighted(
        &mut self,
        success: bool,
        weight: f64,
    ) -> Result<Option<Condition>, crate::DataError> {
        check_finite!(weight);
        self.count += 1;

        let sample = if success { 0.0 } else { weight };

        if self.count == 1 {
            self.value = sample;
        } else {
            self.value = self.alpha.fma(sample, self.one_minus_alpha * self.value);
        }

        if self.count < self.min_samples {
            return Ok(None);
        }

        Ok(if self.value > self.threshold {
            Some(Condition::Degraded)
        } else {
            Some(Condition::Normal)
        })
    }

    /// Current smoothed error rate, or `None` if not primed.
    ///
    /// With unweighted `update()`, this is in [0.0, 1.0].
    /// With weighted outcomes, it may exceed 1.0.
    #[inline]
    #[must_use]
    pub fn error_rate(&self) -> Option<f64> {
        if self.count >= self.min_samples {
            Some(self.value)
        } else {
            None
        }
    }

    /// Number of outcomes recorded.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough data has been collected.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to empty state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.value = 0.0;
        self.count = 0;
    }

    /// Updates the error rate threshold without resetting state.
    ///
    /// # Errors
    ///
    /// Threshold must be >= 0.
    #[inline]
    pub fn reconfigure_threshold(&mut self, threshold: f64) -> Result<(), crate::ConfigError> {
        if threshold < 0.0 {
            return Err(crate::ConfigError::Invalid(
                "threshold must be non-negative",
            ));
        }
        self.threshold = threshold;
        Ok(())
    }
}

impl ErrorRateBuilder {
    /// Smoothing factor.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Halflife for smoothing.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        let ln2 = core::f64::consts::LN_2;
        self.alpha = Some(1.0 - crate::math::exp(-ln2 / halflife));
        self
    }

    /// Span for smoothing.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.alpha = Some(2.0 / (n as f64 + 1.0));
        self
    }

    /// Error rate threshold. Degraded when smoothed rate exceeds this.
    #[inline]
    #[must_use]
    pub fn threshold(mut self, threshold: f64) -> Self {
        self.threshold = Some(threshold);
        self
    }

    /// Minimum outcomes before detection activates. Default: 1.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the error rate tracker.
    ///
    /// # Errors
    ///
    /// - Alpha and threshold must have been set.
    /// - Alpha must be in (0, 1) exclusive.
    /// - Threshold must be non-negative.
    #[inline]
    pub fn build(self) -> Result<ErrorRate, crate::ConfigError> {
        let alpha = self.alpha.ok_or(crate::ConfigError::Missing("alpha"))?;
        let threshold = self
            .threshold
            .ok_or(crate::ConfigError::Missing("threshold"))?;
        if !(alpha > 0.0 && alpha < 1.0) {
            return Err(crate::ConfigError::Invalid("alpha must be in (0, 1)"));
        }
        if threshold < 0.0 {
            return Err(crate::ConfigError::Invalid(
                "threshold must be non-negative",
            ));
        }

        Ok(ErrorRate {
            alpha,
            one_minus_alpha: 1.0 - alpha,
            value: 0.0,
            threshold,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_success_is_healthy() {
        let mut er = ErrorRate::builder()
            .alpha(0.3)
            .threshold(0.05)
            .build()
            .unwrap();

        for _ in 0..100 {
            assert_eq!(er.update(true), Some(Condition::Normal));
        }
    }

    #[test]
    fn all_failure_is_degraded() {
        let mut er = ErrorRate::builder()
            .alpha(0.3)
            .threshold(0.05)
            .build()
            .unwrap();

        for _ in 0..50 {
            let _ = er.update(false);
        }
        assert_eq!(er.update(false), Some(Condition::Degraded));
    }

    #[test]
    fn threshold_crossing() {
        let mut er = ErrorRate::builder()
            .alpha(0.3)
            .threshold(0.5)
            .build()
            .unwrap();

        // All success — should be healthy
        for _ in 0..20 {
            let _ = er.update(true);
        }
        assert_eq!(er.update(true), Some(Condition::Normal));

        // All failure — should become degraded
        for _ in 0..50 {
            let _ = er.update(false);
        }
        assert_eq!(er.update(false), Some(Condition::Degraded));
    }

    #[test]
    fn weighted_failure_triggers_faster() {
        let mut light = ErrorRate::builder()
            .alpha(0.5)
            .threshold(0.5)
            .build()
            .unwrap();
        let mut heavy = ErrorRate::builder()
            .alpha(0.5)
            .threshold(0.5)
            .build()
            .unwrap();

        // Both start healthy
        for _ in 0..10 {
            let _ = light.update(true);
            let _ = heavy.update(true);
        }

        // One weighted failure
        let _ = light.update_weighted(false, 1.0).unwrap();
        let _ = heavy.update_weighted(false, 5.0).unwrap();

        let light_rate = light.error_rate().unwrap();
        let heavy_rate = heavy.error_rate().unwrap();

        assert!(
            heavy_rate > light_rate,
            "heavy ({heavy_rate}) should exceed light ({light_rate})"
        );
    }

    #[test]
    fn priming() {
        let mut er = ErrorRate::builder()
            .alpha(0.3)
            .threshold(0.05)
            .min_samples(5)
            .build()
            .unwrap();

        for _ in 0..4 {
            assert!(er.update(false).is_none());
        }
        assert!(er.update(false).is_some());
    }

    #[test]
    fn reset() {
        let mut er = ErrorRate::builder()
            .alpha(0.3)
            .threshold(0.05)
            .build()
            .unwrap();

        for _ in 0..10 {
            let _ = er.update(false);
        }
        er.reset();
        assert_eq!(er.count(), 0);
        assert!(er.error_rate().is_none());
    }

    #[test]
    fn reconfigure_threshold_changes_behavior() {
        let mut er = ErrorRate::builder()
            .alpha(0.1)
            .threshold(0.5)
            .build()
            .unwrap();

        // Drive to low error rate with all successes
        for _ in 0..50 {
            let _ = er.update(true);
        }
        let rate = er.error_rate().unwrap();
        assert!(
            rate < 0.5,
            "rate should be low after all successes, got {rate}"
        );
        assert_eq!(er.update(true), Some(Condition::Normal));

        // Lower threshold below the current rate
        er.reconfigure_threshold(0.0).unwrap();
        // Rate > 0.0 threshold now means degraded (any non-zero rate)
        // Feed a failure to push rate above 0
        assert_eq!(er.update(false), Some(Condition::Degraded));
    }

    #[test]
    fn errors_without_threshold() {
        let result = ErrorRate::builder().alpha(0.3).build();
        assert!(matches!(
            result,
            Err(crate::ConfigError::Missing("threshold"))
        ));
    }

    #[test]
    fn allows_zero_threshold() {
        let er = ErrorRate::builder().alpha(0.3).threshold(0.0).build();
        assert!(er.is_ok());
    }

    #[test]
    fn rejects_negative_threshold() {
        let result = ErrorRate::builder().alpha(0.3).threshold(-0.1).build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    #[test]
    fn reconfigure_rejects_negative_threshold() {
        let mut er = ErrorRate::builder()
            .alpha(0.3)
            .threshold(0.5)
            .build()
            .unwrap();
        assert!(er.reconfigure_threshold(-0.1).is_err());
        assert!(er.reconfigure_threshold(0.0).is_ok());
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut er = ErrorRate::builder()
            .alpha(0.3)
            .threshold(0.5)
            .build()
            .unwrap();

        assert_eq!(
            er.update_weighted(false, f64::NAN).unwrap_err(),
            crate::DataError::NotANumber
        );
        assert_eq!(
            er.update_weighted(false, f64::INFINITY).unwrap_err(),
            crate::DataError::Infinite
        );
        assert_eq!(
            er.update_weighted(false, f64::NEG_INFINITY).unwrap_err(),
            crate::DataError::Infinite
        );
        assert_eq!(er.count(), 0);
    }
}
