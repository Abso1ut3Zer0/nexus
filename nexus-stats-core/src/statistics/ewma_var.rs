use crate::math::MulAdd;
/// EWMA Variance — Exponentially Weighted Moving Average with variance tracking.
///
/// Tracks both the exponentially smoothed mean and variance of a streaming
/// signal. Based on the RiskMetrics (JP Morgan, 1996) pattern.
///
/// # Use Cases
/// - Volatility tracking
/// - Adaptive thresholds (mean ± k * std_dev)
/// - Regime detection (variance spike = regime change)
#[derive(Debug, Clone)]
pub struct EwmaVar {
    alpha: f64,
    one_minus_alpha: f64,
    mean: f64,
    variance: f64,
    count: u64,
    min_samples: u64,
}
/// Builder for [`
#[doc = stringify!(EwmaVar)]
/// `].
#[derive(Debug, Clone)]
pub struct EwmaVarBuilder {
    alpha: Option<f64>,
    min_samples: u64,
    seed_mean: Option<f64>,
    seed_variance: Option<f64>,
}
impl EwmaVar {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> EwmaVarBuilder {
        EwmaVarBuilder {
            alpha: None,
            min_samples: 2,
            seed_mean: None,
            seed_variance: None,
        }
    }
    /// Feeds a sample. Returns `(mean, variance)` once primed.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<(f64, f64)>, crate::DataError> {
        check_finite!(sample);
        self.count += 1;
        if self.count == 1 {
            self.mean = sample;
            self.variance = 0.0;
        } else {
            let diff = sample - self.mean;
            self.mean = self.alpha.fma(sample, self.one_minus_alpha * self.mean);
            let diff2 = sample - self.mean;
            self.variance = self
                .alpha
                .fma(diff * diff2, self.one_minus_alpha * self.variance);
        }
        if self.count >= self.min_samples {
            Ok(Some((self.mean, self.variance)))
        } else {
            Ok(None)
        }
    }
    /// Current smoothed mean, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn mean(&self) -> Option<f64> {
        if self.count >= self.min_samples {
            Some(self.mean)
        } else {
            None
        }
    }
    /// Current exponentially weighted variance, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> Option<f64> {
        if self.count >= self.min_samples {
            Some(self.variance)
        } else {
            None
        }
    }
    /// Current exponentially weighted standard deviation, or `None` if not primed.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn std_dev(&self) -> Option<f64> {
        self.variance().map(|v| {
            #[allow(clippy::cast_possible_truncation)]
            {
                crate::math::sqrt(v)
            }
        })
    }
    /// The smoothing factor alpha.
    #[inline]
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.alpha
    }
    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }
    /// Whether the EWMA has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }
    /// Resets to uninitialized state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.mean = 0.0;
        self.variance = 0.0;
        self.count = 0;
    }
}
impl EwmaVarBuilder {
    /// Direct smoothing factor. Must be in (0, 1) exclusive.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }
    /// Samples for weight to decay by half.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        let alpha = crate::math::alpha_from_halflife(halflife);
        self.alpha = Some(alpha);
        self
    }
    /// Number of samples for center of mass (pandas convention).
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        let alpha = 2.0 / (n as f64 + 1.0);
        self.alpha = Some(alpha);
        self
    }
    /// Minimum samples before values are valid. Default: 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }
    /// Pre-loads the mean and variance from calibration data.
    ///
    /// When seeded, `is_primed()` returns true immediately.
    #[inline]
    #[must_use]
    pub fn seed(mut self, mean: f64, variance: f64) -> Self {
        self.seed_mean = Some(mean);
        self.seed_variance = Some(variance);
        self
    }
    /// Builds the EWMA variance tracker.
    ///
    /// # Errors
    ///
    /// - Alpha must have been set.
    /// - Alpha must be in (0, 1) exclusive.
    #[inline]
    pub fn build(self) -> Result<EwmaVar, crate::ConfigError> {
        let alpha = self.alpha.ok_or(crate::ConfigError::Missing("alpha"))?;
        if !crate::math::in_unit_interval(alpha) {
            return Err(crate::ConfigError::Invalid(
                "EWMA variance alpha must be in (0, 1)",
            ));
        }
        if self.min_samples == 0 {
            return Err(crate::ConfigError::Invalid(
                "EWMA variance min_samples must be >= 1",
            ));
        }
        if let (Some(m), Some(v)) = (self.seed_mean, self.seed_variance)
            && (!m.is_finite() || !crate::math::nonnegative_finite(v))
        {
            return Err(crate::ConfigError::Invalid(
                "EWMA variance seed needs a finite mean and a non-negative finite variance",
            ));
        }
        let (mean, variance, count) = match (self.seed_mean, self.seed_variance) {
            (Some(m), Some(v)) => (m, v, self.min_samples),
            _ => (0.0, 0.0, 0),
        };
        Ok(EwmaVar {
            alpha,
            one_minus_alpha: 1.0 - alpha,
            mean,
            variance,
            count,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_input_zero_variance() {
        let mut ev = EwmaVar::builder().alpha(0.1).build().unwrap();

        for _ in 0..100 {
            let _ = ev.update(100.0).unwrap();
        }

        let var = ev.variance().unwrap();
        assert!(
            var.abs() < 1e-10,
            "constant input should have ~zero variance, got {var}"
        );
    }

    #[test]
    fn variance_positive_for_varying_input() {
        let mut ev = EwmaVar::builder().alpha(0.1).build().unwrap();

        for i in 0..100 {
            let _ = ev.update(if i % 2 == 0 { 100.0 } else { 110.0 }).unwrap();
        }

        let var = ev.variance().unwrap();
        assert!(
            var > 0.0,
            "varying input should have positive variance, got {var}"
        );
    }

    #[test]
    fn priming_behavior() {
        let mut ev = EwmaVar::builder()
            .alpha(0.1)
            .min_samples(5)
            .build()
            .unwrap();

        for _ in 0..4 {
            assert!(ev.update(100.0).unwrap().is_none());
        }
        assert!(ev.update(100.0).unwrap().is_some());
        assert!(ev.is_primed());
    }

    #[test]
    fn reset_clears_state() {
        let mut ev = EwmaVar::builder().alpha(0.1).build().unwrap();
        for i in 0..50 {
            let _ = ev.update(i as f64).unwrap();
        }

        ev.reset();
        assert_eq!(ev.count(), 0);
        assert!(ev.mean().is_none());
        assert!(ev.variance().is_none());
    }

    #[test]
    fn std_dev_is_sqrt_of_variance() {
        let mut ev = EwmaVar::builder().alpha(0.3).build().unwrap();
        for i in 0..50 {
            let _ = ev.update(100.0 + (i % 10) as f64).unwrap();
        }

        let var = ev.variance().unwrap();
        let sd = ev.std_dev().unwrap();
        let expected = crate::math::sqrt(var);
        assert!((sd - expected).abs() < 1e-10);
    }

    #[test]
    fn seeded_is_primed() {
        let ev = EwmaVar::builder()
            .alpha(0.1)
            .seed(100.0, 25.0)
            .build()
            .unwrap();

        assert!(ev.is_primed());
        assert!((ev.mean().unwrap() - 100.0).abs() < 1e-10);
        assert!((ev.variance().unwrap() - 25.0).abs() < 1e-10);
    }

    #[test]
    fn errors_without_alpha() {
        let result = EwmaVar::builder().build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("alpha"))));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut ev = EwmaVar::builder().alpha(0.1).build().unwrap();
        assert_eq!(ev.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(ev.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(
            ev.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(ev.count(), 0);
    }
}
