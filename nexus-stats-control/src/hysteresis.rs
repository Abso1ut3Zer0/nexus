use nexus_stats_core::Sample;

/// Hysteresis filter — Schmitt trigger with separate high/low thresholds.
///
/// Transitions to `true` when a sample reaches the high threshold
/// (`sample >= high`) and to `false` when one reaches the low threshold
/// (`sample <= low`). Both bounds are inclusive. Strictly between them the
/// state is unchanged, which is what prevents oscillation.
/// `Hysteresis<f64>` rejects NaN and infinity and returns `Result`;
/// `Hysteresis<i64>` cannot fail.
///
/// # Use Cases
/// - Thermostat logic (turn on at low, turn off at high)
/// - Alert suppression (don't flap at boundary)
/// - Circuit breaker arming and disarming
#[derive(Debug, Clone)]
pub struct Hysteresis<T: Sample> {
    low: T,
    high: T,
    state: bool,
    count: u64,
}

impl<T: Sample> Hysteresis<T> {
    /// Creates a hysteresis gate with the given thresholds. Starts `false`.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if either threshold is NaN or infinite
    /// (an infinite threshold can never be reached, so the state would never
    /// change in that direction), or if `low_threshold` is not strictly
    /// below `high_threshold`.
    #[inline]
    #[allow(clippy::neg_cmp_op_on_partial_ord)]
    pub fn new(low_threshold: T, high_threshold: T) -> Result<Self, nexus_stats_core::ConfigError> {
        if !low_threshold.is_finite() || !high_threshold.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "thresholds must be finite",
            ));
        }
        // Negated form rejects NaN (all NaN comparisons are false).
        if !(low_threshold < high_threshold) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "low threshold must be less than high",
            ));
        }
        Ok(Self {
            low: low_threshold,
            high: high_threshold,
            state: false,
            count: 0,
        })
    }

    /// Current state.
    #[inline]
    #[must_use]
    pub fn state(&self) -> bool {
        self.state
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

    /// Resets the state to `false` and the sample count to zero. The
    /// thresholds are kept.
    #[inline]
    pub fn reset(&mut self) {
        self.state = false;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> bool {
        self.count += 1;
        if sample >= self.high {
            self.state = true;
        } else if sample <= self.low {
            self.state = false;
        }
        self.state
    }
}

impl Hysteresis<f64> {
    /// Feeds a sample. Returns the state after it.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<bool, nexus_stats_core::DataError> {
        check_finite!(sample);
        Ok(self.fold(sample))
    }
}

impl Hysteresis<i64> {
    /// Feeds a sample. Returns the state after it.
    #[must_use]
    #[inline]
    pub fn update(&mut self, sample: i64) -> bool {
        self.fold(sample)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn both_thresholds_are_inclusive() {
        let mut h = Hysteresis::<f64>::new(60.0, 80.0).unwrap();
        // Just under high does not arm; exactly high does.
        assert!(!h.update(79.999).unwrap());
        assert!(h.update(80.0).unwrap());
        // Just over low does not disarm; exactly low does.
        assert!(h.update(60.001).unwrap());
        assert!(!h.update(60.0).unwrap());

        let mut h = Hysteresis::<i64>::new(60, 80).unwrap();
        assert!(!h.update(79));
        assert!(h.update(80));
        assert!(h.update(61));
        assert!(!h.update(60));
    }

    #[test]
    fn rejects_infinite_thresholds() {
        assert!(Hysteresis::<f64>::new(f64::NEG_INFINITY, 80.0).is_err());
        assert!(Hysteresis::<f64>::new(60.0, f64::INFINITY).is_err());
    }

    #[test]
    fn rising_crosses_high() {
        let mut h = Hysteresis::<f64>::new(30.0, 70.0).unwrap();
        assert!(!h.update(50.0).unwrap()); // between thresholds, starts false
        assert!(h.update(80.0).unwrap()); // crosses high
    }

    #[test]
    fn falling_crosses_low() {
        let mut h = Hysteresis::<f64>::new(30.0, 70.0).unwrap();
        let _ = h.update(80.0).unwrap(); // true
        assert!(h.update(50.0).unwrap()); // between, stays true
        assert!(!h.update(20.0).unwrap()); // crosses low
    }

    #[test]
    fn no_oscillation_at_boundary() {
        let mut h = Hysteresis::<f64>::new(30.0, 70.0).unwrap();
        let _ = h.update(80.0).unwrap(); // true

        // Oscillate between thresholds — state should not change
        for _ in 0..10 {
            assert!(h.update(50.0).unwrap());
            assert!(h.update(60.0).unwrap());
            assert!(h.update(40.0).unwrap());
        }
    }

    #[test]
    fn i64_basic() {
        let mut h = Hysteresis::<i64>::new(30, 70).unwrap();
        assert!(!h.update(50));
        assert!(h.update(75));
        assert!(h.update(50)); // between, stays true
        assert!(!h.update(25));
    }

    #[test]
    fn reset() {
        let mut h = Hysteresis::<f64>::new(30.0, 70.0).unwrap();
        let _ = h.update(80.0).unwrap();
        h.reset();
        assert!(!h.state());
    }

    #[test]
    fn rejects_invalid_thresholds() {
        assert!(matches!(
            Hysteresis::<f64>::new(70.0, 30.0),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut h = Hysteresis::<f64>::new(30.0, 70.0).unwrap();
        assert_eq!(
            h.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            h.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(
            h.update(f64::NEG_INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
    }
}
