use nexus_stats_core::Sample;

/// Max gauge — tracks the maximum since last take.
///
/// `take()` returns the maximum and resets the gauge. Useful for
/// periodic reporting ("what was the peak since last report?").
/// `MaxGauge<f64>` rejects NaN and infinity and returns `Result`;
/// `MaxGauge<i64>` cannot fail.
///
/// # Use Cases
/// - Peak latency per reporting interval
/// - High-water mark gauges (Prometheus-style)
/// - Periodic max collection
///
/// # Weighting clock
///
/// None: an order statistic over whatever is fed, at any call rate.
#[derive(Debug, Clone)]
pub struct MaxGauge<T: Sample> {
    max: T,
    has_value: bool,
    count: u64,
}

impl<T: Sample> MaxGauge<T> {
    /// Creates a new empty gauge.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            max: T::MIN,
            has_value: false,
            count: 0,
        }
    }

    /// Returns the max since last take/reset, and resets the gauge.
    #[inline]
    pub fn take(&mut self) -> Option<T> {
        if self.has_value {
            let val = self.max;
            self.max = T::MIN;
            self.has_value = false;
            Some(val)
        } else {
            None
        }
    }

    /// Peeks at the current max without resetting.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<T> {
        if self.has_value { Some(self.max) } else { None }
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
        self.has_value
    }

    /// Resets the gauge.
    #[inline]
    pub fn reset(&mut self) {
        self.max = T::MIN;
        self.has_value = false;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) {
        self.count += 1;
        if !self.has_value || sample > self.max {
            self.max = sample;
        }
        self.has_value = true;
    }
}

impl MaxGauge<f64> {
    /// Records a sample.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(sample);
        self.fold(sample);
        Ok(())
    }
}

impl MaxGauge<i64> {
    /// Records a sample.
    #[inline]
    pub fn update(&mut self, sample: i64) {
        self.fold(sample);
    }
}

impl<T: Sample> Default for MaxGauge<T> {
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
        let mut g: MaxGauge<f64> = MaxGauge::new();
        assert!(g.peek().is_none());
        assert!(g.take().is_none());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn tracks_max() {
        let mut g = MaxGauge::<f64>::new();
        g.update(10.0).unwrap();
        g.update(50.0).unwrap();
        g.update(30.0).unwrap();
        assert_eq!(g.peek(), Some(50.0));
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn take_returns_and_resets() {
        let mut g = MaxGauge::<f64>::new();
        g.update(50.0).unwrap();
        assert_eq!(g.take(), Some(50.0));
        assert!(g.take().is_none()); // already taken

        g.update(20.0).unwrap();
        assert_eq!(g.take(), Some(20.0));
    }

    #[test]
    fn i64_basic() {
        let mut g = MaxGauge::<i64>::new();
        g.update(100);
        g.update(200);
        assert_eq!(g.take(), Some(200));
        g.update(i64::MIN);
        assert_eq!(
            g.take(),
            Some(i64::MIN),
            "the sentinel is replaced by the first sample"
        );
    }

    #[test]
    fn reset() {
        let mut g = MaxGauge::<f64>::new();
        g.update(100.0).unwrap();
        g.reset();
        assert!(g.peek().is_none());
    }

    #[test]
    fn default_is_empty() {
        let g: MaxGauge<i64> = MaxGauge::default();
        assert!(g.peek().is_none());
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut g = MaxGauge::<f64>::new();
        assert!(matches!(
            g.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        assert!(matches!(
            g.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert!(matches!(
            g.update(f64::NEG_INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert!(g.peek().is_none(), "rejected samples are not recorded");
    }
}
