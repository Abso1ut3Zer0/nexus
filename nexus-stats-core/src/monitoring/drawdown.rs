use crate::Sample;

/// Drawdown monitor — tracks peak value and current/maximum drawdown.
///
/// Drawdown is the decline from peak to current value. Useful for risk
/// monitoring and circuit breakers ("if PnL drops $X from peak, halt").
///
/// `Drawdown<f64>` rejects NaN and infinity and returns `Result`;
/// `Drawdown<i64>` (fixed-point P&L, counts) cannot fail.
///
/// # Use Cases
/// - PnL circuit breaker
/// - Position risk monitoring
/// - Performance tracking (max drawdown as a risk metric)
///
/// # Weighting clock
///
/// Per `update` call: every sample counts the same. Correct when samples
/// are evenly spaced, or one per event where per-event weighting is wanted.
/// Never feed it from a loop whose iteration time depends on the quantity
/// being measured.
#[derive(Debug, Clone)]
pub struct Drawdown<T: Sample> {
    peak: T,
    current: T,
    worst: T,
    count: u64,
}

impl<T: Sample> Drawdown<T> {
    /// Creates a new empty drawdown monitor.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            peak: T::ZERO,
            current: T::ZERO,
            worst: T::ZERO,
            count: 0,
        }
    }

    /// Highest value seen, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn peak(&self) -> Option<T> {
        if self.count == 0 {
            None
        } else {
            Some(self.peak)
        }
    }

    /// Current drawdown (peak - last sample). Zero if empty.
    #[inline]
    #[must_use]
    pub fn drawdown(&self) -> T {
        if self.count == 0 {
            T::ZERO
        } else {
            self.peak - self.current
        }
    }

    /// Worst drawdown ever observed. Zero if empty.
    #[inline]
    #[must_use]
    pub fn max_drawdown(&self) -> T {
        self.worst
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
        self.peak = T::ZERO;
        self.current = T::ZERO;
        self.worst = T::ZERO;
        self.count = 0;
    }

    /// The algorithm, shared by every instantiation.
    #[inline]
    fn fold(&mut self, sample: T) -> T {
        self.count += 1;
        self.current = sample;
        if self.count == 1 || sample > self.peak {
            self.peak = sample;
        }
        let dd = self.peak - self.current;
        if dd > self.worst {
            self.worst = dd;
        }
        dd
    }
}

impl Drawdown<f64> {
    /// Feeds a sample. Returns the current drawdown (peak - current).
    /// Returns 0 at new peaks.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<f64, crate::DataError> {
        check_finite!(sample);
        Ok(self.fold(sample))
    }
}

impl Drawdown<i64> {
    /// Feeds a sample. Returns the current drawdown (peak - current).
    /// Returns 0 at new peaks.
    #[inline]
    pub fn update(&mut self, sample: i64) -> i64 {
        self.fold(sample)
    }
}

impl<T: Sample> Default for Drawdown<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_state() {
        let dd: Drawdown<f64> = Drawdown::new();
        assert!(dd.peak().is_none());
        assert_eq!(dd.drawdown(), 0.0);
        assert_eq!(dd.max_drawdown(), 0.0);
        assert_eq!(dd.count(), 0);
        assert!(!dd.is_primed());
    }

    #[test]
    fn first_sample_sets_peak() {
        let mut dd = Drawdown::<f64>::new();
        assert_eq!(dd.update(100.0).unwrap(), 0.0);
        assert_eq!(dd.peak(), Some(100.0));
        assert!(dd.is_primed());
    }

    #[test]
    fn drawdown_from_peak() {
        let mut dd = Drawdown::<f64>::new();
        dd.update(100.0).unwrap();
        assert_eq!(dd.update(90.0).unwrap(), 10.0);
        assert_eq!(dd.update(80.0).unwrap(), 20.0);
        assert_eq!(dd.drawdown(), 20.0);
        assert_eq!(dd.max_drawdown(), 20.0);
    }

    #[test]
    fn new_peak_resets_drawdown() {
        let mut dd = Drawdown::<f64>::new();
        dd.update(100.0).unwrap();
        dd.update(80.0).unwrap();
        assert_eq!(dd.update(120.0).unwrap(), 0.0);
        assert_eq!(dd.peak(), Some(120.0));
        assert_eq!(dd.drawdown(), 0.0);
        assert_eq!(dd.max_drawdown(), 20.0, "worst is remembered");
    }

    #[test]
    fn max_drawdown_tracks_worst() {
        let mut dd = Drawdown::<f64>::new();
        dd.update(100.0).unwrap();
        dd.update(70.0).unwrap(); // 30
        dd.update(110.0).unwrap(); // new peak
        dd.update(100.0).unwrap(); // 10
        assert_eq!(dd.max_drawdown(), 30.0);
    }

    #[test]
    fn reset_clears_all() {
        let mut dd = Drawdown::<f64>::new();
        dd.update(100.0).unwrap();
        dd.update(50.0).unwrap();
        dd.reset();
        assert!(dd.peak().is_none());
        assert_eq!(dd.max_drawdown(), 0.0);
        assert_eq!(dd.count(), 0);
    }

    #[test]
    fn default_is_empty() {
        let dd: Drawdown<f64> = Drawdown::default();
        assert!(!dd.is_primed());
    }

    #[test]
    fn i64_basic() {
        let mut dd = Drawdown::<i64>::new();
        assert_eq!(dd.update(1_000), 0);
        assert_eq!(dd.update(700), 300);
        assert_eq!(dd.update(1_200), 0);
        assert_eq!(dd.max_drawdown(), 300);
        assert_eq!(dd.peak(), Some(1_200));
    }

    #[test]
    fn monotonic_increasing_no_drawdown() {
        let mut dd = Drawdown::<f64>::new();
        for i in 1..=10 {
            assert_eq!(dd.update(f64::from(i)).unwrap(), 0.0);
        }
        assert_eq!(dd.max_drawdown(), 0.0);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut dd = Drawdown::<f64>::new();
        assert!(matches!(
            dd.update(f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
        assert!(matches!(
            dd.update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        ));
        assert!(matches!(
            dd.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        ));
        assert_eq!(dd.count(), 0, "rejected samples are not counted");
    }
}

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// `peak()` and `max_drawdown()` must be monotonically
        /// non-decreasing across updates, and `drawdown()` must never go
        /// negative -- the monotonicity invariant a drawdown/circuit-breaker
        /// monitor depends on.
        #[test]
        fn fuzz_peak_and_max_drawdown_are_monotonic(
            samples in proptest::collection::vec(-1e6f64..1e6, 1..300),
        ) {
            let mut dd = Drawdown::<f64>::new();
            let mut prev_peak = f64::NEG_INFINITY;
            let mut prev_max_dd = 0.0f64;
            let mut running_max_dd = 0.0f64;

            for &s in &samples {
                let current_dd = dd.update(s).unwrap();
                prop_assert!(current_dd >= 0.0, "drawdown went negative: {current_dd}");

                let peak = dd.peak().unwrap();
                prop_assert!(peak >= prev_peak, "peak decreased: {prev_peak} -> {peak}");
                prev_peak = peak;

                running_max_dd = running_max_dd.max(current_dd);
                let max_dd = dd.max_drawdown();
                prop_assert!(max_dd >= prev_max_dd, "max_drawdown decreased: {prev_max_dd} -> {max_dd}");
                prop_assert!((max_dd - running_max_dd).abs() < 1e-9, "max_drawdown {max_dd} != running max {running_max_dd}");
                prev_max_dd = max_dd;
            }
        }
    }
}
