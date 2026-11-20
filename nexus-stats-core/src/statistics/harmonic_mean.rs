/// Online harmonic mean.
///
/// Tracks the sum of reciprocals for computing the harmonic mean
/// incrementally. Useful for averaging rates (e.g., throughput in
/// requests/second across multiple servers).
///
/// # Use Cases
/// - Average throughput across heterogeneous servers
/// - Mean speed over equal-distance segments
/// - Any rate where arithmetic mean would be misleading
#[derive(Debug, Clone)]
pub struct HarmonicMean {
    reciprocal_sum: f64,
    count: u64,
}

impl HarmonicMean {
    /// Creates a new empty accumulator.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            reciprocal_sum: 0.0,
            count: 0,
        }
    }

    /// Feeds a sample. Must be positive and non-zero.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in. A
    /// NaN or an infinity makes the readings NaN from then on, until
    /// [`reset`](Self::reset); a finite value above
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT) in magnitude can overflow them. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, sample: f64) {
        self.count += 1;
        self.reciprocal_sum += 1.0 / sample;
    }

    /// [`update`](Self::update) with the sample validated first: refuses a
    /// NaN, an infinity, a zero or a negative (the harmonic mean is defined
    /// for positive values only), and a sample outside
    /// `[1 / INPUT_LIMIT, INPUT_LIMIT]`, whose reciprocal or whose own size
    /// could take the sum of reciprocals out of range. Leaves the state
    /// untouched. Fed only through this method the mean is always a finite
    /// positive number.
    ///
    /// # Errors
    ///
    /// `DataError::NotANumber`, `DataError::Infinite`, or
    /// `DataError::OutOfRange` for a sample outside that range. See
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT).
    #[inline]
    pub fn checked_update(&mut self, sample: f64) -> Result<(), crate::DataError> {
        check_magnitude!(sample, crate::INPUT_LIMIT);
        // Also covers zero and negatives.
        if sample < 1.0 / crate::INPUT_LIMIT {
            return Err(crate::DataError::OutOfRange);
        }
        self.update(sample);
        Ok(())
    }

    /// Harmonic mean, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn mean(&self) -> Option<f64> {
        if self.count == 0 {
            None
        } else {
            Some(self.count as f64 / self.reciprocal_sum)
        }
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one sample has been recorded.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets to empty state.
    #[inline]
    pub fn reset(&mut self) {
        self.reciprocal_sum = 0.0;
        self.count = 0;
    }
}

impl Default for HarmonicMean {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let hm = HarmonicMean::new();
        assert!(hm.mean().is_none());
    }

    #[test]
    fn known_values() {
        let mut hm = HarmonicMean::new();
        // HM(1, 4) = 2 / (1/1 + 1/4) = 2 / 1.25 = 1.6
        hm.update(1.0);
        hm.update(4.0);
        let m = hm.mean().unwrap();
        assert!((m - 1.6).abs() < 1e-10, "expected 1.6, got {m}");
    }

    #[test]
    fn harmonic_leq_arithmetic() {
        let mut hm = HarmonicMean::new();
        let vals = [2.0, 4.0, 8.0];
        let mut sum = 0.0;
        for &v in &vals {
            hm.update(v);
            sum += v;
        }
        let arithmetic = sum / vals.len() as f64;
        let harmonic = hm.mean().unwrap();
        assert!(
            harmonic <= arithmetic,
            "HM ({harmonic}) should be <= AM ({arithmetic})"
        );
    }

    #[test]
    fn equal_values() {
        let mut hm = HarmonicMean::new();
        for _ in 0..100 {
            hm.update(5.0);
        }
        let m = hm.mean().unwrap();
        assert!(
            (m - 5.0).abs() < 1e-10,
            "HM of equal values should equal that value"
        );
    }

    #[test]
    fn reset() {
        let mut hm = HarmonicMean::new();
        hm.update(1.0);
        hm.reset();
        assert_eq!(hm.count(), 0);
        assert!(hm.mean().is_none());
    }

    #[test]
    fn default_is_empty() {
        let hm = HarmonicMean::default();
        assert_eq!(hm.count(), 0);
    }

    #[test]
    fn rejects_zero_and_negative_without_touching_state() {
        let mut hm = HarmonicMean::new();
        hm.update(2.0);
        assert_eq!(hm.checked_update(0.0), Err(crate::DataError::OutOfRange));
        assert_eq!(hm.checked_update(-1.0), Err(crate::DataError::OutOfRange));
        assert_eq!(hm.count(), 1);
        assert_eq!(hm.mean(), Some(2.0));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut hm = HarmonicMean::new();
        assert_eq!(
            hm.checked_update(f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        assert_eq!(
            hm.checked_update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(
            hm.checked_update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(hm.count(), 0);
    }
}
