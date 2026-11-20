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

    /// Feeds a sample.
    ///
    /// Does not validate `sample`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::statistics::HarmonicMean;
    ///
    /// let mut hm = HarmonicMean::new();
    /// hm.update(60.0);
    /// hm.update(30.0);
    /// assert_eq!(hm.mean(), Some(40.0));
    /// ```
    #[inline]
    pub fn update(&mut self, sample: f64) {
        self.count += 1;
        self.reciprocal_sum += 1.0 / sample;
    }

    /// Checked update. Feeds `sample`, or returns an error and leaves the
    /// accumulator unchanged if `sample` is NaN, infinite, or outside
    /// `[1 / INPUT_LIMIT, INPUT_LIMIT]` (see
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT)).
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `sample`
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if `sample` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if `sample`
    ///   is outside that range, which includes zero and every negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::{DataError, statistics::HarmonicMean};
    ///
    /// let mut hm = HarmonicMean::new();
    /// assert_eq!(hm.checked_update(60.0), Ok(()));
    /// assert_eq!(hm.checked_update(0.0), Err(DataError::OutOfRange));
    /// assert_eq!(hm.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(&mut self, sample: f64) -> Result<(), crate::DataError> {
        crate::math::check_input(sample, crate::INPUT_LIMIT)?;
        // A smaller sample's reciprocal could overflow the sum.
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
            return None;
        }

        Some(self.count as f64 / self.reciprocal_sum)
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
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let mut hm = HarmonicMean::new();
        hm.checked_update(2.0).unwrap();

        assert_eq!(hm.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(hm.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(hm.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(hm.checked_update(0.0), Err(OutOfRange));
        assert_eq!(hm.checked_update(-1.0), Err(OutOfRange));
        assert_eq!(hm.checked_update(1e-121), Err(OutOfRange));
        assert_eq!(hm.checked_update(1e121), Err(OutOfRange));

        assert_eq!((hm.count(), hm.mean()), (1, Some(2.0)));
    }

    #[test]
    fn checked_update_accepts_both_ends_of_the_range_without_overflow() {
        let smallest = 1.0 / crate::INPUT_LIMIT;
        let mut hm = HarmonicMean::new();
        for _ in 0..100_000 {
            hm.checked_update(smallest).unwrap();
            hm.checked_update(crate::INPUT_LIMIT).unwrap();
        }
        let mean = hm.mean().unwrap();
        assert!(mean.is_finite() && mean > 0.0, "mean = {mean}");
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = HarmonicMean::new();
        let mut unchecked = HarmonicMean::new();
        for x in [2.0, 0.5, 1e9, 3.25] {
            checked.checked_update(x).unwrap();
            unchecked.update(x);
        }
        assert_eq!(checked.count(), unchecked.count());
        assert_eq!(checked.mean(), unchecked.mean());
    }

    #[test]
    fn update_does_not_validate() {
        // A negative sample is folded in as its reciprocal, as the
        // arithmetic has it.
        let mut hm = HarmonicMean::new();
        hm.update(-4.0);
        assert_eq!(hm.mean(), Some(-4.0));
    }
}
