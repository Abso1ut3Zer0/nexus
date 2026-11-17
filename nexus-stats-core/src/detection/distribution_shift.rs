use crate::statistics::Moments;

/// Detects distribution shape changes by comparing fast and slow moment estimates.
///
/// Maintains two `Moments` accumulators — a short-window "fast" tracker
/// and a long-window "slow" baseline. Shifts in kurtosis or skewness between
/// the two indicate regime changes (e.g., fat-tail events, asymmetry shifts).
///
/// The fast tracker is periodically reset after `fast_window` observations
/// to keep it responsive. The slow tracker accumulates continuously.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::detection::DistributionShift;
///
/// let mut det = DistributionShift::builder()
///     .fast_window(50)
///     .build()
///     .unwrap();
///
/// // Feed normal-looking data
/// for i in 0..200 {
///     det.update(i as f64 * 0.01).unwrap();
/// }
/// ```
#[derive(Debug, Clone)]
pub struct DistributionShift {
    fast: Moments,
    slow: Moments,
    fast_window: u64,
    fast_count: u64,
    count: u64,
}

/// Builder for [`DistributionShift`].
#[derive(Debug, Clone)]
pub struct DistributionShiftBuilder {
    fast_window: Option<u64>,
}

impl DistributionShift {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> DistributionShiftBuilder {
        DistributionShiftBuilder { fast_window: None }
    }

    /// Feed an observation.
    ///
    /// Both fast and slow trackers receive the value. The fast tracker
    /// resets every `fast_window` observations.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if the value is NaN or infinite.
    #[inline]
    pub fn update(&mut self, value: f64) -> Result<(), crate::DataError> {
        check_finite!(value);

        self.count += 1;
        self.fast_count += 1;

        self.fast.update(value)?;
        self.slow.update(value)?;

        // Reset fast tracker when window is full to keep it responsive.
        if self.fast_count >= self.fast_window {
            self.fast = Moments::new();
            self.fast_count = 0;
        }

        Ok(())
    }

    /// Kurtosis shift: fast excess kurtosis minus slow excess kurtosis.
    ///
    /// Positive values indicate the recent window has heavier tails than
    /// the baseline. Returns `None` if either tracker has insufficient data.
    #[inline]
    #[must_use]
    pub fn kurtosis_shift(&self) -> Option<f64> {
        let fast_k = self.fast.excess_kurtosis()?;
        let slow_k = self.slow.excess_kurtosis()?;
        Some(fast_k - slow_k)
    }

    /// Skewness shift: fast skewness minus slow skewness.
    ///
    /// Positive shift means recent data is more right-skewed than baseline.
    /// Returns `None` if either tracker has insufficient data.
    #[inline]
    #[must_use]
    pub fn skewness_shift(&self) -> Option<f64> {
        let fast_s = self.fast.skewness()?;
        let slow_s = self.slow.skewness()?;
        Some(fast_s - slow_s)
    }

    /// Whether either shift exceeds the given threshold (absolute value).
    #[inline]
    #[must_use]
    pub fn is_shifted(&self, threshold: f64) -> bool {
        if let Some(ks) = self.kurtosis_shift()
            && ks.abs() > threshold
        {
            return true;
        }
        if let Some(ss) = self.skewness_shift()
            && ss.abs() > threshold
        {
            return true;
        }
        false
    }

    /// Total number of observations fed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough observations have been fed for both trackers.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        // Need at least 4 samples in both for kurtosis to be defined.
        self.slow.count() >= 4 && self.fast.count() >= 4
    }

    /// Reset all state.
    pub fn reset(&mut self) {
        self.fast = Moments::new();
        self.slow = Moments::new();
        self.fast_count = 0;
        self.count = 0;
    }
}

impl DistributionShiftBuilder {
    /// Number of observations for the fast (short) window before reset.
    ///
    /// Default: 50.
    #[inline]
    #[must_use]
    pub fn fast_window(mut self, window: u64) -> Self {
        self.fast_window = Some(window);
        self
    }

    /// Build the detector.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `fast_window` is 0.
    #[inline]
    pub fn build(self) -> Result<DistributionShift, crate::ConfigError> {
        let fast_window = self.fast_window.unwrap_or(50);
        if fast_window == 0 {
            return Err(crate::ConfigError::Invalid("fast_window must be > 0"));
        }
        Ok(DistributionShift {
            fast: Moments::new(),
            slow: Moments::new(),
            fast_window,
            fast_count: 0,
            count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stable_distribution_no_shift() {
        let mut det = DistributionShift::builder()
            .fast_window(100)
            .build()
            .unwrap();
        // 537 samples: the fast window is mid-fill at the end, so the shift
        // is defined (a multiple of the window would leave it just reset).
        for i in 0..537 {
            det.update((i % 100) as f64).unwrap();
        }
        let ks = det.kurtosis_shift().expect("fast window holds 37 samples");
        assert!(
            ks.abs() < 2.0,
            "kurtosis shift should be small for stable data, got {ks}"
        );
    }

    #[test]
    fn fat_tail_shift_detected() {
        let mut det = DistributionShift::builder()
            .fast_window(50)
            .build()
            .unwrap();
        // Mild baseline, then a fast window of outliers plus a partial one so
        // the fast tracker is populated when queried.
        for i in 0..200 {
            det.update((i as f64) * 0.01).unwrap();
        }
        for i in 0..80 {
            let val = if i % 5 == 0 { 1000.0 } else { 1.0 };
            det.update(val).unwrap();
        }
        assert_eq!(det.count(), 280);
        // The fast window holds 30 samples with one outlier in five; the slow
        // baseline holds all 280 with one in eighteen. Rarer extremes mean a
        // heavier tail, so the slow kurtosis is the larger one and the shift
        // is large and negative: what matters is that it is large.
        let ks = det.kurtosis_shift().expect("fast window holds 30 samples");
        assert!(
            ks.abs() > 1.0,
            "expected a large kurtosis shift between the two windows, got {ks}"
        );
        let ss = det.skewness_shift().expect("fast window holds 30 samples");
        assert!(
            ss.abs() > 0.1,
            "expected measurable skewness shift from outliers, got {ss}"
        );
    }

    #[test]
    fn is_shifted_threshold() {
        let mut det = DistributionShift::builder()
            .fast_window(100)
            .build()
            .unwrap();
        // Same distribution everywhere, fast window mid-fill: not shifted.
        for i in 0..537 {
            det.update((i % 50) as f64).unwrap();
        }
        assert!(
            det.kurtosis_shift().is_some(),
            "the verdict must be a real reading"
        );
        assert!(!det.is_shifted(100.0));
        // A burst of outliers in the fast window is a shift at a sane threshold.
        for i in 0..40 {
            det.update(if i % 5 == 0 { 1000.0 } else { 1.0 }).unwrap();
        }
        assert!(
            det.is_shifted(1.0),
            "outlier burst must register as a shift"
        );
    }

    #[test]
    fn not_primed_before_4() {
        let mut det = DistributionShift::builder()
            .fast_window(100)
            .build()
            .unwrap();
        det.update(1.0).unwrap();
        det.update(2.0).unwrap();
        det.update(3.0).unwrap();
        assert!(!det.is_primed());
    }

    #[test]
    fn primed_after_4() {
        let mut det = DistributionShift::builder()
            .fast_window(100)
            .build()
            .unwrap();
        for i in 0..5 {
            det.update(i as f64).unwrap();
        }
        // slow has 5, fast has 5 → both >= 4
        assert!(det.is_primed());
    }

    #[test]
    fn reset_clears_state() {
        let mut det = DistributionShift::builder()
            .fast_window(50)
            .build()
            .unwrap();
        for i in 0..100 {
            det.update(i as f64).unwrap();
        }
        det.reset();
        assert_eq!(det.count(), 0);
        assert!(!det.is_primed());
    }

    #[test]
    fn nan_rejected() {
        let mut det = DistributionShift::builder()
            .fast_window(50)
            .build()
            .unwrap();
        assert!(det.update(f64::NAN).is_err());
    }

    #[test]
    fn inf_rejected() {
        let mut det = DistributionShift::builder()
            .fast_window(50)
            .build()
            .unwrap();
        assert!(det.update(f64::INFINITY).is_err());
    }
}
