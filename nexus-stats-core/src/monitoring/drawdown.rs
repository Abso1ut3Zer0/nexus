/// Drawdown monitor — tracks peak value and current/maximum drawdown.
///
/// Drawdown is the decline from peak to current value. Useful for risk
/// monitoring and circuit breakers ("if PnL drops $X from peak, halt").
///
/// # Use Cases
/// - PnL circuit breaker
/// - Position risk monitoring
/// - Performance tracking (max drawdown as a risk metric)
#[derive(Debug, Clone)]
pub struct DrawdownF64 {
    peak: f64,
    current: f64,
    max_drawdown: f64,
    count: u64,
}

impl DrawdownF64 {
    /// Creates a new empty drawdown monitor.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            peak: 0.0,
            current: 0.0,
            max_drawdown: 0.0,
            count: 0,
        }
    }

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
        self.count += 1;
        self.current = sample;

        if self.count == 1 || sample > self.peak {
            self.peak = sample;
        }

        let dd = self.peak - self.current;
        if dd > self.max_drawdown {
            self.max_drawdown = dd;
        }

        Ok(dd)
    }

    /// Highest value seen, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn peak(&self) -> Option<f64> {
        if self.count == 0 {
            None
        } else {
            Some(self.peak)
        }
    }

    /// Current drawdown (peak - last sample). Zero if empty.
    #[inline]
    #[must_use]
    pub fn drawdown(&self) -> f64 {
        if self.count == 0 {
            0.0
        } else {
            self.peak - self.current
        }
    }

    /// Worst drawdown ever observed. Zero if empty.
    #[inline]
    #[must_use]
    pub fn max_drawdown(&self) -> f64 {
        self.max_drawdown
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
        self.peak = 0.0;
        self.current = 0.0;
        self.max_drawdown = 0.0;
        self.count = 0;
    }
}

impl Default for DrawdownF64 {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

/// Drawdown monitor — tracks peak value and current/maximum drawdown.
///
/// Drawdown is the decline from peak to current value. Useful for risk
/// monitoring and circuit breakers ("if PnL drops $X from peak, halt").
///
/// # Use Cases
/// - PnL circuit breaker
/// - Position risk monitoring
/// - Performance tracking (max drawdown as a risk metric)
#[derive(Debug, Clone)]
pub struct DrawdownI64 {
    peak: i64,
    current: i64,
    max_drawdown: i64,
    count: u64,
}

impl DrawdownI64 {
    /// Creates a new empty drawdown monitor.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            peak: 0,
            current: 0,
            max_drawdown: 0,
            count: 0,
        }
    }

    /// Feeds a sample. Returns the current drawdown (peak - current).
    /// Returns 0 at new peaks.
    #[inline]
    #[must_use]
    pub fn update(&mut self, sample: i64) -> i64 {
        self.count += 1;
        self.current = sample;

        if self.count == 1 || sample > self.peak {
            self.peak = sample;
        }

        let dd = self.peak - self.current;
        if dd > self.max_drawdown {
            self.max_drawdown = dd;
        }

        dd
    }

    /// Highest value seen, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn peak(&self) -> Option<i64> {
        if self.count == 0 {
            None
        } else {
            Some(self.peak)
        }
    }

    /// Current drawdown (peak - last sample). Zero if empty.
    #[inline]
    #[must_use]
    pub fn drawdown(&self) -> i64 {
        if self.count == 0 {
            0
        } else {
            self.peak - self.current
        }
    }

    /// Worst drawdown ever observed. Zero if empty.
    #[inline]
    #[must_use]
    pub fn max_drawdown(&self) -> i64 {
        self.max_drawdown
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
        self.peak = 0;
        self.current = 0;
        self.max_drawdown = 0;
        self.count = 0;
    }
}

impl Default for DrawdownI64 {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::float_cmp)]
    fn empty_state() {
        let dd = DrawdownF64::new();
        assert_eq!(dd.count(), 0);
        assert!(!dd.is_primed());
        assert!(dd.peak().is_none());
        assert_eq!(dd.drawdown(), 0.0);
        assert_eq!(dd.max_drawdown(), 0.0);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn first_sample_sets_peak() {
        let mut dd = DrawdownF64::new();
        let result = dd.update(100.0).unwrap();
        assert_eq!(result, 0.0); // no drawdown at first sample
        assert_eq!(dd.peak(), Some(100.0));
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn drawdown_from_peak() {
        let mut dd = DrawdownF64::new();
        let _ = dd.update(100.0).unwrap();
        let result = dd.update(90.0).unwrap();
        assert_eq!(result, 10.0);
        assert_eq!(dd.drawdown(), 10.0);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn new_peak_resets_drawdown() {
        let mut dd = DrawdownF64::new();
        let _ = dd.update(100.0).unwrap();
        let _ = dd.update(90.0).unwrap();
        assert_eq!(dd.drawdown(), 10.0);

        let result = dd.update(110.0).unwrap(); // new peak
        assert_eq!(result, 0.0);
        assert_eq!(dd.peak(), Some(110.0));
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn max_drawdown_tracks_worst() {
        let mut dd = DrawdownF64::new();
        let _ = dd.update(100.0).unwrap();
        let _ = dd.update(80.0).unwrap(); // drawdown = 20
        let _ = dd.update(110.0).unwrap(); // new peak, drawdown = 0
        let _ = dd.update(100.0).unwrap(); // drawdown = 10

        assert_eq!(dd.max_drawdown(), 20.0); // worst was 20
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn reset_clears_all() {
        let mut dd = DrawdownF64::new();
        let _ = dd.update(100.0).unwrap();
        let _ = dd.update(80.0).unwrap();

        dd.reset();
        assert_eq!(dd.count(), 0);
        assert!(dd.peak().is_none());
        assert_eq!(dd.max_drawdown(), 0.0);
    }

    #[test]
    fn default_is_empty() {
        let dd = DrawdownF64::default();
        assert_eq!(dd.count(), 0);
    }

    #[test]
    fn i64_basic() {
        let mut dd = DrawdownI64::new();
        let _ = dd.update(1000);
        let _ = dd.update(800);
        assert_eq!(dd.drawdown(), 200);
        assert_eq!(dd.max_drawdown(), 200);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn monotonic_increasing_no_drawdown() {
        let mut dd = DrawdownF64::new();
        for i in 0..100 {
            let result = dd.update(i as f64).unwrap();
            assert_eq!(result, 0.0);
        }
        assert_eq!(dd.max_drawdown(), 0.0);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut dd = DrawdownF64::new();
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
    }
}

// =============================================================================
// Proptests
// =============================================================================

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
            let mut dd = DrawdownF64::new();
            let mut prev_peak = f64::NEG_INFINITY;
            let mut prev_max_dd = 0.0f64;
            let mut running_max_dd = 0.0f64;

            for &s in &samples {
                let current_dd = dd.update(s).unwrap();
                prop_assert!(current_dd >= 0.0, "drawdown went negative: {current_dd}");

                let peak = dd.peak().unwrap();
                prop_assert!(peak >= prev_peak, "peak decreased: {prev_peak} -> {peak}");
                prev_peak = peak;

                let max_dd = dd.max_drawdown();
                prop_assert!(
                    max_dd >= prev_max_dd,
                    "max_drawdown decreased: {prev_max_dd} -> {max_dd}"
                );
                prev_max_dd = max_dd;

                running_max_dd = running_max_dd.max(current_dd);
            }

            // max_drawdown must equal the largest drawdown() ever observed.
            prop_assert_eq!(dd.max_drawdown(), running_max_dd);
        }
    }
}
