use crate::Sample;

/// Hysteresis filter — Schmitt trigger with separate high/low thresholds.
///
/// Transitions to `true` when sample exceeds the high threshold.
/// Transitions to `false` when sample drops below the low threshold.
/// Between the thresholds, the state is unchanged — preventing oscillation.
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
    /// Returns `ConfigError::Invalid` if `low_threshold` is not strictly
    /// below `high_threshold` (a NaN threshold fails this test).
    #[inline]
    #[allow(clippy::neg_cmp_op_on_partial_ord)]
    pub fn new(low_threshold: T, high_threshold: T) -> Result<Self, crate::ConfigError> {
        // Negated form rejects NaN (all NaN comparisons are false).
        if !(low_threshold < high_threshold) {
            return Err(crate::ConfigError::Invalid(
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

    /// Resets the state to `false`.
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
    pub fn update(&mut self, sample: f64) -> Result<bool, crate::DataError> {
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
            Err(crate::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut h = Hysteresis::<f64>::new(30.0, 70.0).unwrap();
        assert_eq!(h.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(h.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(h.update(f64::NEG_INFINITY), Err(crate::DataError::Infinite));
    }
}
