use crate::Sample;

/// First difference — `x[n] - x[n-1]`.
///
/// Returns the change between consecutive samples.
/// `None` on the first sample (no previous value to diff against).
/// `FirstDiff<f64>` rejects NaN and infinity and returns `Result`;
/// `FirstDiff<i64>` cannot fail.
///
/// # Use Cases
/// - Computing returns from prices
/// - Velocity from position
/// - Detecting step changes
#[derive(Debug, Clone)]
pub struct FirstDiff<T: Sample> {
    prev: T,
    /// Samples processed; the first one seeds the state.
    count: u64,
}

impl<T: Sample> FirstDiff<T> {
    /// Creates a new differencer.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            prev: T::ZERO,
            count: 0,
        }
    }

    /// Samples processed since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether a difference is available (two samples seen).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= 2
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.prev = T::ZERO;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> Option<T> {
        self.count += 1;
        if self.count == 1 {
            self.prev = sample;
            return None;
        }
        let diff = sample - self.prev;
        self.prev = sample;
        Some(diff)
    }
}

impl FirstDiff<f64> {
    /// Feeds a sample. Returns `x[n] - x[n-1]`, or `None` on the first sample.
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

impl FirstDiff<i64> {
    /// Feeds a sample. Returns `x[n] - x[n-1]`, or `None` on the first sample.
    #[inline]
    pub fn update(&mut self, sample: i64) -> Option<i64> {
        self.fold(sample)
    }
}

impl<T: Sample> Default for FirstDiff<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

/// Second difference — `x[n] - 2*x[n-1] + x[n-2]`.
///
/// Returns the acceleration (change in change) of a signal.
/// `None` until the third sample.
/// `SecondDiff<f64>` rejects NaN and infinity and returns `Result`;
/// `SecondDiff<i64>` cannot fail.
///
/// # Use Cases
/// - Acceleration from position
/// - Curvature detection
/// - "Is the rate of change itself changing?"
#[derive(Debug, Clone)]
pub struct SecondDiff<T: Sample> {
    prev2: T,
    prev1: T,
    count: u64,
}

impl<T: Sample> SecondDiff<T> {
    /// Creates a new second differencer.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            prev2: T::ZERO,
            prev1: T::ZERO,
            count: 0,
        }
    }

    /// Whether a second difference is available (three samples seen).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= 3
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.prev2 = T::ZERO;
        self.prev1 = T::ZERO;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> Option<T> {
        self.count += 1;
        if self.count == 1 {
            self.prev1 = sample;
            return None;
        }
        if self.count == 2 {
            self.prev2 = self.prev1;
            self.prev1 = sample;
            return None;
        }
        let diff2 = sample - (self.prev1 + self.prev1) + self.prev2;
        self.prev2 = self.prev1;
        self.prev1 = sample;
        Some(diff2)
    }
}

impl SecondDiff<f64> {
    /// Feeds a sample. Returns the second difference, or `None` on the
    /// first two samples.
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

impl SecondDiff<i64> {
    /// Feeds a sample. Returns the second difference, or `None` on the
    /// first two samples.
    #[inline]
    pub fn update(&mut self, sample: i64) -> Option<i64> {
        self.fold(sample)
    }
}

impl<T: Sample> Default for SecondDiff<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // First diff
    #[test]
    fn first_diff_none_on_first() {
        let mut fd = FirstDiff::<f64>::new();
        assert!(fd.update(100.0).unwrap().is_none());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn first_diff_computes() {
        let mut fd = FirstDiff::<f64>::new();
        let _ = fd.update(100.0).unwrap();
        assert_eq!(fd.update(110.0).unwrap(), Some(10.0));
        assert_eq!(fd.update(105.0).unwrap(), Some(-5.0));
    }

    #[test]
    fn first_diff_i64() {
        let mut fd = FirstDiff::<i64>::new();
        let _ = fd.update(100);
        assert_eq!(fd.update(130), Some(30));
    }

    #[test]
    fn first_diff_reset() {
        let mut fd = FirstDiff::<f64>::new();
        let _ = fd.update(100.0).unwrap();
        fd.reset();
        assert!(fd.update(50.0).unwrap().is_none()); // re-initialized
    }

    // Second diff
    #[test]
    fn second_diff_none_until_third() {
        let mut sd = SecondDiff::<f64>::new();
        assert!(sd.update(1.0).unwrap().is_none());
        assert!(sd.update(2.0).unwrap().is_none());
        assert!(sd.update(3.0).unwrap().is_some());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn second_diff_linear_is_zero() {
        let mut sd = SecondDiff::<f64>::new();
        let _ = sd.update(10.0).unwrap();
        let _ = sd.update(20.0).unwrap();
        // Linear: 10, 20, 30 → second diff = 30 - 2*20 + 10 = 0
        assert_eq!(sd.update(30.0).unwrap(), Some(0.0));
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn second_diff_quadratic() {
        let mut sd = SecondDiff::<f64>::new();
        // x^2: 1, 4, 9 → 9 - 2*4 + 1 = 2
        let _ = sd.update(1.0).unwrap();
        let _ = sd.update(4.0).unwrap();
        assert_eq!(sd.update(9.0).unwrap(), Some(2.0));
    }

    #[test]
    fn second_diff_i64() {
        let mut sd = SecondDiff::<i64>::new();
        let _ = sd.update(10);
        let _ = sd.update(20);
        assert_eq!(sd.update(30), Some(0)); // linear
        assert_eq!(sd.update(50), Some(10)); // acceleration
    }

    #[test]
    fn second_diff_reset() {
        let mut sd = SecondDiff::<f64>::new();
        let _ = sd.update(1.0).unwrap();
        let _ = sd.update(2.0).unwrap();
        sd.reset();
        assert!(sd.update(5.0).unwrap().is_none());
    }

    #[test]
    fn first_diff_rejects_nan_and_inf() {
        let mut fd = FirstDiff::<f64>::new();
        assert_eq!(fd.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(fd.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(
            fd.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        );
    }

    #[test]
    fn second_diff_rejects_nan_and_inf() {
        let mut sd = SecondDiff::<f64>::new();
        assert_eq!(sd.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(sd.update(f64::INFINITY), Err(crate::DataError::Infinite));
    }
}
