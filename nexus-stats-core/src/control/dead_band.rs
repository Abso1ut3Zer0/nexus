use crate::Sample;

/// Dead band filter — suppresses small changes, reports significant ones.
///
/// Only emits a new value when the sample deviates from the last reported
/// value by more than the threshold. Prevents noisy oscillation around
/// a stable value from generating unnecessary updates.
/// `DeadBand<f64>` rejects NaN and infinity and returns `Result`;
/// `DeadBand<i64>` cannot fail.
///
/// # Use Cases
/// - Reducing update frequency for slowly-changing metrics
/// - Hysteresis-free change suppression
/// - Quote update throttling (only republish on meaningful moves)
#[derive(Debug, Clone)]
pub struct DeadBand<T: Sample> {
    threshold: T,
    last_reported: T,
    /// Samples processed; the first one seeds the state.
    count: u64,
}

impl<T: Sample> DeadBand<T> {
    /// Creates a dead band. A change is reported when it exceeds `threshold`.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `threshold` is negative or not finite.
    #[inline]
    pub fn new(threshold: T) -> Result<Self, crate::ConfigError> {
        if !threshold.is_finite() || threshold < T::ZERO {
            return Err(crate::ConfigError::Invalid(
                "dead band threshold must be finite and non-negative",
            ));
        }
        Ok(Self {
            threshold,
            last_reported: T::ZERO,
            count: 0,
        })
    }

    /// Last reported value, or `None` before the first sample.
    #[inline]
    #[must_use]
    pub fn last_reported(&self) -> Option<T> {
        if self.count > 0 {
            Some(self.last_reported)
        } else {
            None
        }
    }

    /// Samples processed since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one sample has been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets to uninitialized state. The threshold is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.last_reported = T::ZERO;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> Option<T> {
        self.count += 1;
        if self.count == 1 || sample.further_than(self.last_reported, self.threshold) {
            self.last_reported = sample;
            Some(sample)
        } else {
            None
        }
    }
}

impl DeadBand<f64> {
    /// Feeds a sample. Returns it if it moved more than the threshold from
    /// the last reported value (always on the first sample), else `None`.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<f64>, crate::DataError> {
        check_finite!(sample);
        Ok(self.fold(sample))
    }
}

impl DeadBand<i64> {
    /// Feeds a sample. Returns it if it moved more than the threshold from
    /// the last reported value (always on the first sample), else `None`.
    #[inline]
    pub fn update(&mut self, sample: i64) -> Option<i64> {
        self.fold(sample)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::float_cmp)]
    fn first_sample_always_reported() {
        let mut db = DeadBand::<f64>::new(5.0).unwrap();
        assert_eq!(db.update(100.0).unwrap(), Some(100.0));
    }

    #[test]
    fn small_changes_suppressed() {
        let mut db = DeadBand::<f64>::new(5.0).unwrap();
        let _ = db.update(100.0).unwrap();
        assert_eq!(db.update(103.0).unwrap(), None); // within threshold
        assert_eq!(db.update(99.0).unwrap(), None); // within threshold
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn large_changes_reported() {
        let mut db = DeadBand::<f64>::new(5.0).unwrap();
        let _ = db.update(100.0).unwrap();
        assert_eq!(db.update(110.0).unwrap(), Some(110.0)); // exceeds threshold
    }

    #[test]
    fn i64_basic() {
        let mut db = DeadBand::<i64>::new(10).unwrap();
        assert_eq!(db.update(100), Some(100));
        assert_eq!(db.update(105), None);
        assert_eq!(db.update(115), Some(115));
    }

    #[test]
    fn reset() {
        let mut db = DeadBand::<f64>::new(5.0).unwrap();
        let _ = db.update(100.0).unwrap();
        db.reset();
        assert!(db.last_reported().is_none());
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut db = DeadBand::<f64>::new(5.0).unwrap();
        assert_eq!(db.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(db.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(
            db.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        );
    }
}
