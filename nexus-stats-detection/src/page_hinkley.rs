use nexus_stats_core::DataError;

/// Page-Hinkley — sequential test for mean drift.
///
/// Accumulates deviations from the running mean. Fires when the
/// difference between the cumulative sum and its running minimum
/// (or maximum) exceeds the threshold. O(1) per update.
///
/// Two-sided: detects both upward and downward mean shifts.
///
/// # Parameters
///
/// - `threshold` (lambda) — detection sensitivity. Larger values
///   reduce false positives but increase detection delay.
/// - `alpha` (delta) — magnitude tolerance. The minimum shift size
///   worth detecting. Deviations smaller than `alpha` are absorbed.
///
/// # Examples
///
/// ```
/// use nexus_stats_detection::detection::PageHinkley;
///
/// let mut ph = PageHinkley::builder()
///     .threshold(50.0)
///     .alpha(0.5)
///     .build()
///     .unwrap();
///
/// // Stable signal — no detection
/// for _ in 0..100 {
///     assert!(ph.update(10.0).unwrap() != Some(true));
/// }
/// ```
#[derive(Debug, Clone)]
pub struct PageHinkley {
    threshold: f64,
    alpha: f64,
    mean: f64,
    sum_pos: f64,
    sum_neg: f64,
    min_pos: f64,
    max_neg: f64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`PageHinkley`].
#[derive(Debug, Clone)]
pub struct PageHinkleyBuilder {
    threshold: Option<f64>,
    alpha: Option<f64>,
    min_samples: u64,
}

impl PageHinkley {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> PageHinkleyBuilder {
        PageHinkleyBuilder {
            threshold: None,
            alpha: None,
            min_samples: 30,
        }
    }

    /// Feeds a sample. Returns `Ok(true)` if mean drift detected.
    ///
    /// Detection is two-sided: fires on upward or downward shifts.
    /// Returns `Ok(false)` while priming or when no drift detected.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    ///
    /// `None` until `min_samples` samples have been seen (no verdict yet), then
    /// `Some(true)` when a change is detected on this sample.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<bool>, DataError> {
        check_finite!(sample);
        self.count += 1;

        self.mean += (sample - self.mean) / self.count as f64;

        self.sum_pos += sample - self.mean - self.alpha;
        self.sum_neg += sample - self.mean + self.alpha;

        // Selects, not branches: these extrema move often while the mean drifts.
        self.min_pos = if self.sum_pos < self.min_pos {
            self.sum_pos
        } else {
            self.min_pos
        };
        self.max_neg = if self.sum_neg > self.max_neg {
            self.sum_neg
        } else {
            self.max_neg
        };

        if !self.is_primed() {
            return Ok(None);
        }

        Ok(Some(
            self.sum_pos - self.min_pos > self.threshold
                || self.max_neg - self.sum_neg > self.threshold,
        ))
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the tracker has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.mean = 0.0;
        self.sum_pos = 0.0;
        self.sum_neg = 0.0;
        self.min_pos = 0.0;
        self.max_neg = 0.0;
        self.count = 0;
    }
}

impl PageHinkleyBuilder {
    /// Detection threshold (lambda). Required, must be positive.
    ///
    /// Larger values reduce false positives but increase detection delay.
    #[inline]
    #[must_use]
    pub fn threshold(mut self, threshold: f64) -> Self {
        self.threshold = Some(threshold);
        self
    }

    /// Magnitude tolerance (delta). Required, must be non-negative.
    ///
    /// The minimum shift size worth detecting. Set to 0 to detect
    /// any shift.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Minimum samples before detection activates. Default: 30.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the Page-Hinkley detector.
    ///
    /// # Errors
    ///
    /// - Threshold must have been set and be positive.
    /// - Alpha must have been set and be non-negative.
    #[inline]
    pub fn build(self) -> Result<PageHinkley, nexus_stats_core::ConfigError> {
        let threshold = self
            .threshold
            .ok_or(nexus_stats_core::ConfigError::Missing("threshold"))?;
        if !threshold.is_finite() || threshold <= 0.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "PageHinkley threshold must be finite and positive",
            ));
        }

        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        if !alpha.is_finite() || alpha < 0.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "PageHinkley alpha must be finite and non-negative",
            ));
        }

        Ok(PageHinkley {
            threshold,
            alpha,
            mean: 0.0,
            sum_pos: 0.0,
            sum_neg: 0.0,
            min_pos: 0.0,
            max_neg: 0.0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_drift() {
        let mut ph = PageHinkley::builder()
            .threshold(50.0)
            .alpha(0.5)
            .build()
            .unwrap();

        for _ in 0..200 {
            assert!(ph.update(10.0).unwrap() != Some(true));
        }
    }

    #[test]
    fn upward_drift() {
        let mut ph = PageHinkley::builder()
            .threshold(50.0)
            .alpha(0.5)
            .min_samples(20)
            .build()
            .unwrap();

        for _ in 0..50 {
            let _ = ph.update(10.0);
        }

        let mut detected = false;
        for _ in 0..200 {
            if ph.update(20.0).unwrap() == Some(true) {
                detected = true;
                break;
            }
        }
        assert!(detected, "should detect upward mean shift");
    }

    #[test]
    fn downward_drift() {
        let mut ph = PageHinkley::builder()
            .threshold(50.0)
            .alpha(0.5)
            .min_samples(20)
            .build()
            .unwrap();

        for _ in 0..50 {
            let _ = ph.update(20.0);
        }

        let mut detected = false;
        for _ in 0..200 {
            if ph.update(10.0).unwrap() == Some(true) {
                detected = true;
                break;
            }
        }
        assert!(detected, "should detect downward mean shift");
    }

    #[test]
    fn sensitivity_vs_alpha() {
        let mut sensitive = PageHinkley::builder()
            .threshold(50.0)
            .alpha(0.0)
            .min_samples(20)
            .build()
            .unwrap();

        let mut tolerant = PageHinkley::builder()
            .threshold(50.0)
            .alpha(5.0)
            .min_samples(20)
            .build()
            .unwrap();

        for _ in 0..50 {
            let _ = sensitive.update(10.0);
            let _ = tolerant.update(10.0);
        }

        let mut sensitive_count = 0u64;
        let mut tolerant_count = 0u64;
        for _ in 0..100 {
            if sensitive.update(12.0).unwrap() == Some(true) && sensitive_count == 0 {
                sensitive_count = sensitive.count();
            }
            if tolerant.update(12.0).unwrap() == Some(true) && tolerant_count == 0 {
                tolerant_count = tolerant.count();
            }
        }

        assert!(
            sensitive_count > 0,
            "sensitive detector should fire on small shift"
        );
        assert_eq!(
            tolerant_count, 0,
            "tolerant detector should not fire on shift smaller than alpha"
        );
    }

    #[test]
    fn reset_clears() {
        let mut ph = PageHinkley::builder()
            .threshold(50.0)
            .alpha(0.5)
            .min_samples(20)
            .build()
            .unwrap();

        for _ in 0..50 {
            let _ = ph.update(10.0);
        }
        for _ in 0..200 {
            let _ = ph.update(20.0);
        }

        ph.reset();
        assert_eq!(ph.count(), 0);
        assert!(!ph.is_primed());

        for _ in 0..19 {
            assert!(ph.update(10.0).unwrap() != Some(true));
        }
    }

    #[test]
    fn nan_rejected() {
        let mut ph = PageHinkley::builder()
            .threshold(50.0)
            .alpha(0.5)
            .build()
            .unwrap();
        assert!(matches!(ph.update(f64::NAN), Err(DataError::NotANumber)));
    }

    #[test]
    fn inf_rejected() {
        let mut ph = PageHinkley::builder()
            .threshold(50.0)
            .alpha(0.5)
            .build()
            .unwrap();
        assert!(matches!(ph.update(f64::INFINITY), Err(DataError::Infinite)));
    }

    #[test]
    fn builder_missing_threshold() {
        let result = PageHinkley::builder().alpha(0.5).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("threshold"))
        ));
    }

    #[test]
    fn builder_negative_threshold() {
        let result = PageHinkley::builder().threshold(-1.0).alpha(0.5).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }
}
