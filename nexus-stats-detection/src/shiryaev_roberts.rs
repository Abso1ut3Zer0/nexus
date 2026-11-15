/// Shiryaev-Roberts — Quasi-Bayesian change detection procedure.
///
/// Theoretically optimal for detecting unknown change times. Assumes
/// normal distribution for the likelihood ratio computation.
///
/// The statistic R evolves as: `R = (1 + R) * likelihood_ratio(x)`
/// where the likelihood ratio compares pre-change and post-change
/// normal distributions.
///
/// # Use Cases
/// - Same as CUSUM but with better average detection delay
/// - When CUSUM's sensitivity vs false alarm tradeoff isn't good enough
#[derive(Debug, Clone)]
pub struct ShiryaevRoberts {
    pre_mean: f64,
    post_mean: f64,
    variance: f64,
    threshold: f64,
    r: f64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`ShiryaevRoberts`].
#[derive(Debug, Clone)]
pub struct ShiryaevRobertsBuilder {
    pre_mean: Option<f64>,
    post_mean: Option<f64>,
    variance: Option<f64>,
    threshold: Option<f64>,
    min_samples: u64,
}

impl ShiryaevRoberts {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> ShiryaevRobertsBuilder {
        ShiryaevRobertsBuilder {
            pre_mean: None,
            post_mean: None,
            variance: None,
            threshold: None,
            min_samples: 0,
        }
    }

    /// Feeds a sample. Returns `Ok(Some(true))` if change detected, `Ok(Some(false))`
    /// if not, or `Ok(None)` if not yet primed.
    ///
    /// The likelihood ratio for normal distributions is:
    /// ```text
    /// LR = exp((x - μ₀)(μ₁ - μ₀) / σ² - (μ₁² - μ₀²) / (2σ²))
    ///    = exp((μ₁ - μ₀) * (x - (μ₀ + μ₁) / 2) / σ²)
    /// ```
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<bool>, nexus_stats_core::DataError> {
        check_finite!(sample);
        self.count += 1;

        // Log-likelihood ratio for normal distribution
        let delta_mean = self.post_mean - self.pre_mean;
        let midpoint = f64::midpoint(self.pre_mean, self.post_mean);
        let log_lr = delta_mean * (sample - midpoint) / self.variance;

        // R = (1 + R) * exp(log_lr)
        self.r = (1.0 + self.r) * nexus_stats_core::math::exp(log_lr);

        if self.count < self.min_samples {
            return Ok(None);
        }

        Ok(Some(self.r > self.threshold))
    }

    /// Current R statistic value.
    #[inline]
    #[must_use]
    pub fn statistic(&self) -> f64 {
        self.r
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the detector has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets R statistic and count. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.r = 0.0;
        self.count = 0;
    }
}

impl ShiryaevRobertsBuilder {
    /// Pre-change (null hypothesis) mean.
    #[inline]
    #[must_use]
    pub fn pre_change_mean(mut self, mean: f64) -> Self {
        self.pre_mean = Some(mean);
        self
    }

    /// Post-change (alternative hypothesis) mean.
    #[inline]
    #[must_use]
    pub fn post_change_mean(mut self, mean: f64) -> Self {
        self.post_mean = Some(mean);
        self
    }

    /// Known variance of the process.
    #[inline]
    #[must_use]
    pub fn variance(mut self, variance: f64) -> Self {
        self.variance = Some(variance);
        self
    }

    /// Decision threshold for the R statistic.
    #[inline]
    #[must_use]
    pub fn threshold(mut self, threshold: f64) -> Self {
        self.threshold = Some(threshold);
        self
    }

    /// Minimum samples before detection activates. Default: 0.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the detector.
    ///
    /// # Errors
    ///
    /// - All of `pre_change_mean`, `post_change_mean`, `variance`, and `threshold`
    ///   must be set.
    /// - Variance must be positive.
    /// - Threshold must be positive.
    /// - Pre-change and post-change means must differ.
    #[inline]
    pub fn build(self) -> Result<ShiryaevRoberts, nexus_stats_core::ConfigError> {
        let pre_mean = self
            .pre_mean
            .ok_or(nexus_stats_core::ConfigError::Missing("pre_change_mean"))?;
        let post_mean = self
            .post_mean
            .ok_or(nexus_stats_core::ConfigError::Missing("post_change_mean"))?;
        let variance = self
            .variance
            .ok_or(nexus_stats_core::ConfigError::Missing("variance"))?;
        let threshold = self
            .threshold
            .ok_or(nexus_stats_core::ConfigError::Missing("threshold"))?;

        if variance <= 0.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "variance must be positive",
            ));
        }
        if threshold <= 0.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "threshold must be positive",
            ));
        }
        if (post_mean - pre_mean).abs() <= f64::EPSILON {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "pre and post change means must differ",
            ));
        }

        Ok(ShiryaevRoberts {
            pre_mean,
            post_mean,
            variance,
            threshold,
            r: 0.0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_detection_at_pre_change_mean() {
        let mut sr = ShiryaevRoberts::builder()
            .pre_change_mean(100.0)
            .post_change_mean(110.0)
            .variance(25.0)
            .threshold(100.0)
            .build()
            .unwrap();

        for _ in 0..100 {
            let result = sr.update(100.0).unwrap();
            assert_eq!(result, Some(false), "should not detect at pre-change mean");
        }
    }

    #[test]
    fn detects_shift_to_post_change_mean() {
        let mut sr = ShiryaevRoberts::builder()
            .pre_change_mean(100.0)
            .post_change_mean(110.0)
            .variance(25.0)
            .threshold(100.0)
            .build()
            .unwrap();

        let mut detected = false;
        for _ in 0..100 {
            if sr.update(110.0).unwrap() == Some(true) {
                detected = true;
                break;
            }
        }
        assert!(detected, "should detect shift to post-change mean");
    }

    #[test]
    fn statistic_grows_under_alternative() {
        let mut sr = ShiryaevRoberts::builder()
            .pre_change_mean(0.0)
            .post_change_mean(5.0)
            .variance(1.0)
            .threshold(1000.0)
            .build()
            .unwrap();

        let _ = sr.update(5.0);
        let r1 = sr.statistic();
        let _ = sr.update(5.0);
        let r2 = sr.statistic();

        assert!(r2 > r1, "R should grow under alternative hypothesis");
    }

    #[test]
    fn reset_clears_statistic() {
        let mut sr = ShiryaevRoberts::builder()
            .pre_change_mean(0.0)
            .post_change_mean(5.0)
            .variance(1.0)
            .threshold(100.0)
            .build()
            .unwrap();

        let _ = sr.update(5.0);
        assert!(sr.statistic() > 0.0);

        sr.reset();
        #[allow(clippy::float_cmp)]
        {
            assert_eq!(sr.statistic(), 0.0);
        }
        assert_eq!(sr.count(), 0);
    }

    #[test]
    fn priming() {
        let mut sr = ShiryaevRoberts::builder()
            .pre_change_mean(0.0)
            .post_change_mean(5.0)
            .variance(1.0)
            .threshold(100.0)
            .min_samples(5)
            .build()
            .unwrap();

        for _ in 0..4 {
            assert_eq!(sr.update(5.0).unwrap(), None);
        }
        assert!(sr.update(5.0).unwrap().is_some());
    }

    #[test]
    fn errors_without_variance() {
        let result = ShiryaevRoberts::builder()
            .pre_change_mean(0.0)
            .post_change_mean(5.0)
            .threshold(100.0)
            .build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("variance"))
        ));
    }

    #[test]
    fn errors_on_equal_means() {
        let result = ShiryaevRoberts::builder()
            .pre_change_mean(5.0)
            .post_change_mean(5.0)
            .variance(1.0)
            .threshold(100.0)
            .build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut sr = ShiryaevRoberts::builder()
            .pre_change_mean(100.0)
            .post_change_mean(110.0)
            .variance(25.0)
            .threshold(100.0)
            .build()
            .unwrap();

        assert_eq!(
            sr.update(f64::NAN).unwrap_err(),
            nexus_stats_core::DataError::NotANumber
        );
        assert_eq!(
            sr.update(f64::INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(
            sr.update(f64::NEG_INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(sr.count(), 0);
    }
}
