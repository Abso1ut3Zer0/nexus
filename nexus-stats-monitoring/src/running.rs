use nexus_stats_core::Sample;

/// All-time minimum tracker.
///
/// Tracks the smallest value ever seen. One comparison per update.
/// `RunningMin<f64>` rejects NaN and infinity and returns `Result`;
/// `RunningMin<i64>` cannot fail.
///
/// # Use Cases
/// - Best-case latency tracking (all-time min RTT)
/// - Low-water mark for prices or levels
/// - Input to range calculations (max - min)
///
/// # Weighting clock
///
/// None: an order statistic over whatever is fed, at any call rate.
#[derive(Debug, Clone)]
pub struct RunningMin<T: Sample> {
    min: T,
    count: u64,
}

impl<T: Sample> RunningMin<T> {
    /// Creates a new empty tracker.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            min: T::MAX,
            count: 0,
        }
    }

    /// Smallest value seen, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn min(&self) -> Option<T> {
        if self.count == 0 {
            None
        } else {
            Some(self.min)
        }
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one sample has been fed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets to empty state.
    #[inline]
    pub fn reset(&mut self) {
        self.min = T::MAX;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> T {
        self.count += 1;
        // A select, not a branch: a new extremum is unpredictable.
        self.min = if sample < self.min { sample } else { self.min };
        self.min
    }
}

impl RunningMin<f64> {
    /// Feeds a sample. Returns the running minimum.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<f64, nexus_stats_core::DataError> {
        check_finite!(sample);
        Ok(self.fold(sample))
    }
}

impl RunningMin<i64> {
    /// Feeds a sample. Returns the running minimum.
    #[inline]
    pub fn update(&mut self, sample: i64) -> i64 {
        self.fold(sample)
    }
}

impl<T: Sample> Default for RunningMin<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

/// All-time maximum tracker.
///
/// Tracks the largest value ever seen. One comparison per update.
/// `RunningMax<f64>` rejects NaN and infinity and returns `Result`;
/// `RunningMax<i64>` cannot fail.
///
/// # Use Cases
/// - High-water mark tracking (peak throughput, max latency)
/// - Capacity planning (peak resource usage)
/// - Input to range calculations (max - min)
///
/// # Weighting clock
///
/// None: an order statistic over whatever is fed, at any call rate.
#[derive(Debug, Clone)]
pub struct RunningMax<T: Sample> {
    max: T,
    count: u64,
}

impl<T: Sample> RunningMax<T> {
    /// Creates a new empty tracker.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            max: T::MIN,
            count: 0,
        }
    }

    /// Largest value seen, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn max(&self) -> Option<T> {
        if self.count == 0 {
            None
        } else {
            Some(self.max)
        }
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one sample has been fed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets to empty state.
    #[inline]
    pub fn reset(&mut self) {
        self.max = T::MIN;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> T {
        self.count += 1;
        // A select, not a branch: a new extremum is unpredictable.
        self.max = if sample > self.max { sample } else { self.max };
        self.max
    }
}

impl RunningMax<f64> {
    /// Feeds a sample. Returns the running maximum.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<f64, nexus_stats_core::DataError> {
        check_finite!(sample);
        Ok(self.fold(sample))
    }
}

impl RunningMax<i64> {
    /// Feeds a sample. Returns the running maximum.
    #[inline]
    pub fn update(&mut self, sample: i64) -> i64 {
        self.fold(sample)
    }
}

impl<T: Sample> Default for RunningMax<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn min_empty() {
        let rm: RunningMin<f64> = RunningMin::new();
        assert!(rm.min().is_none());
        assert!(!rm.is_primed());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn min_tracks() {
        let mut rm = RunningMin::<f64>::new();
        assert_eq!(rm.update(50.0).unwrap(), 50.0);
        assert_eq!(rm.update(30.0).unwrap(), 30.0);
        assert_eq!(rm.update(40.0).unwrap(), 30.0); // still 30
        assert_eq!(rm.update(10.0).unwrap(), 10.0);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn min_reset() {
        let mut rm = RunningMin::<f64>::new();
        let _ = rm.update(10.0).unwrap();
        rm.reset();
        assert!(rm.min().is_none());
        assert_eq!(rm.update(50.0).unwrap(), 50.0);
    }

    #[test]
    fn min_i64() {
        let mut rm = RunningMin::<i64>::new();
        assert_eq!(rm.update(100), 100);
        assert_eq!(rm.update(50), 50);
        assert_eq!(rm.update(75), 50);
        assert_eq!(rm.min(), Some(50));
    }

    #[test]
    fn min_default() {
        let rm: RunningMin<f64> = RunningMin::default();
        assert_eq!(rm.count(), 0);
    }

    #[test]
    fn max_empty() {
        let rm: RunningMax<f64> = RunningMax::new();
        assert!(rm.max().is_none());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn max_tracks() {
        let mut rm = RunningMax::<f64>::new();
        assert_eq!(rm.update(30.0).unwrap(), 30.0);
        assert_eq!(rm.update(50.0).unwrap(), 50.0);
        assert_eq!(rm.update(40.0).unwrap(), 50.0); // still 50
        assert_eq!(rm.update(90.0).unwrap(), 90.0);
    }

    #[test]
    fn max_i64() {
        let mut rm = RunningMax::<i64>::new();
        assert_eq!(rm.update(50), 50);
        assert_eq!(rm.update(100), 100);
        assert_eq!(rm.update(75), 100);
        assert_eq!(rm.max(), Some(100));
    }

    // The sentinels are the identities: a first sample always replaces them.
    #[test]
    fn extremes_replace_the_sentinels() {
        let mut min = RunningMin::<i64>::new();
        assert_eq!(min.update(i64::MAX), i64::MAX);
        let mut max = RunningMax::<i64>::new();
        assert_eq!(max.update(i64::MIN), i64::MIN);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut min64 = RunningMin::<f64>::new();
        assert!(matches!(
            min64.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        assert!(matches!(
            min64.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert!(matches!(
            min64.update(f64::NEG_INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        let mut max64 = RunningMax::<f64>::new();
        assert!(matches!(
            max64.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        assert!(matches!(
            max64.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert_eq!(max64.count(), 0);
    }
}
