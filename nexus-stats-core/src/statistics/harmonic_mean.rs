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
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    ///
    /// Returns `DataError::OutOfRange` if the sample is zero or negative: the
    /// harmonic mean is defined for positive values only.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<(), crate::DataError> {
        check_finite!(sample);
        if sample <= 0.0 {
            return Err(crate::DataError::OutOfRange);
        }
        self.count += 1;
        self.reciprocal_sum += 1.0 / sample;
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
        hm.update(1.0).unwrap();
        hm.update(4.0).unwrap();
        let m = hm.mean().unwrap();
        assert!((m - 1.6).abs() < 1e-10, "expected 1.6, got {m}");
    }

    #[test]
    fn harmonic_leq_arithmetic() {
        let mut hm = HarmonicMean::new();
        let vals = [2.0, 4.0, 8.0];
        let mut sum = 0.0;
        for &v in &vals {
            hm.update(v).unwrap();
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
            hm.update(5.0).unwrap();
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
        hm.update(1.0).unwrap();
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
        hm.update(2.0).unwrap();
        assert_eq!(hm.update(0.0), Err(crate::DataError::OutOfRange));
        assert_eq!(hm.update(-1.0), Err(crate::DataError::OutOfRange));
        assert_eq!(hm.count(), 1);
        assert_eq!(hm.mean(), Some(2.0));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut hm = HarmonicMean::new();
        assert_eq!(hm.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(hm.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(
            hm.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(hm.count(), 0);
    }
}
