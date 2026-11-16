use crate::Sample;

/// Level crossing detector — signals when a value crosses a threshold.
///
/// Returns `true` on the sample where the signal crosses the threshold
/// in either direction. Tracks total crossing count.
/// `LevelCrossing<f64>` rejects NaN and infinity and returns `Result`;
/// `LevelCrossing<i64>` cannot fail.
///
/// # Use Cases
/// - Zero-crossing detection
/// - Alert when metric crosses a boundary
/// - Counting threshold breaches
#[derive(Debug, Clone)]
pub struct LevelCrossing<T: Sample> {
    threshold: T,
    was_above: bool,
    crossings: u64,
    initialized: bool,
}

impl<T: Sample> LevelCrossing<T> {
    /// Creates a detector for the given threshold.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if the threshold is NaN or infinite (a NaN
    /// threshold would never be crossed).
    #[inline]
    pub fn new(threshold: T) -> Result<Self, crate::ConfigError> {
        if !threshold.is_finite() {
            return Err(crate::ConfigError::Invalid("threshold must be finite"));
        }
        Ok(Self {
            threshold,
            was_above: false,
            crossings: 0,
            initialized: false,
        })
    }

    /// Total number of crossings seen.
    #[inline]
    #[must_use]
    pub fn crossing_count(&self) -> u64 {
        self.crossings
    }

    /// Resets to uninitialized state. The threshold is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.was_above = false;
        self.crossings = 0;
        self.initialized = false;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> bool {
        let is_above = sample >= self.threshold;
        if !self.initialized {
            self.was_above = is_above;
            self.initialized = true;
            return false;
        }
        if is_above == self.was_above {
            false
        } else {
            self.was_above = is_above;
            self.crossings += 1;
            true
        }
    }
}

impl LevelCrossing<f64> {
    /// Feeds a sample. Returns `true` if it crossed the threshold.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<bool, crate::DataError> {
        check_finite!(sample);
        Ok(self.fold(sample))
    }
}

impl LevelCrossing<i64> {
    /// Feeds a sample. Returns `true` if it crossed the threshold.
    #[inline]
    pub fn update(&mut self, sample: i64) -> bool {
        self.fold(sample)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_sample_no_crossing() {
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        assert!(!lc.update(30.0).unwrap());
    }

    #[test]
    fn upward_crossing() {
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        assert!(!lc.update(30.0).unwrap());
        assert!(lc.update(60.0).unwrap()); // crossed upward
        assert_eq!(lc.crossing_count(), 1);
    }

    #[test]
    fn downward_crossing() {
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        assert!(!lc.update(60.0).unwrap());
        assert!(lc.update(40.0).unwrap()); // crossed downward
        assert_eq!(lc.crossing_count(), 1);
    }

    #[test]
    fn multiple_crossings() {
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        let _ = lc.update(30.0).unwrap();
        let _ = lc.update(60.0).unwrap(); // cross 1
        let _ = lc.update(40.0).unwrap(); // cross 2
        let _ = lc.update(70.0).unwrap(); // cross 3
        assert_eq!(lc.crossing_count(), 3);
    }

    #[test]
    fn no_crossing_same_side() {
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        let _ = lc.update(30.0).unwrap();
        assert!(!lc.update(40.0).unwrap()); // same side
        assert!(!lc.update(20.0).unwrap()); // same side
    }

    #[test]
    fn i64_basic() {
        let mut lc = LevelCrossing::<i64>::new(100).unwrap();
        assert!(!lc.update(50));
        assert!(lc.update(150)); // crossed
    }

    #[test]
    fn reset() {
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        let _ = lc.update(30.0).unwrap();
        let _ = lc.update(60.0).unwrap();
        lc.reset();
        assert_eq!(lc.crossing_count(), 0);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        assert_eq!(lc.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(lc.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(
            lc.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        );
    }
}
