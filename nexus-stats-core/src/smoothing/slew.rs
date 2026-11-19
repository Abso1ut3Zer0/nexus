use crate::Sample;

/// Slew rate limiter — clamps output change per sample.
///
/// Limits how fast the output can change between consecutive samples: the
/// output follows the input but moves at most `max_rate` per update, in
/// either direction. The first sample is passed through.
/// `Slew<f64>` rejects NaN and infinity and returns `Result`;
/// `Slew<i64>` cannot fail: the allowed band saturates at the `i64` bounds.
///
/// # Use Cases
/// - Smoothing displayed values without an EMA's lag
/// - Rate-limiting a control output (quote moves per tick)
/// - Protecting downstream consumers from step changes
#[derive(Debug, Clone)]
pub struct Slew<T: Sample> {
    max_rate: T,
    value: T,
    /// Samples processed; the first one seeds the state.
    count: u64,
}

impl<T: Sample> Slew<T> {
    /// Creates a limiter allowing at most `max_rate` of change per sample.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `max_rate` is not finite or not
    /// strictly positive.
    #[inline]
    #[allow(clippy::neg_cmp_op_on_partial_ord)]
    pub fn new(max_rate: T) -> Result<Self, crate::ConfigError> {
        if !max_rate.is_finite() || !(max_rate > T::ZERO) {
            return Err(crate::ConfigError::Invalid(
                "slew max_rate must be finite and positive",
            ));
        }
        Ok(Self {
            max_rate,
            value: T::ZERO,
            count: 0,
        })
    }

    /// Current output value, or `None` before the first sample.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<T> {
        self.is_primed().then_some(self.value)
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

    /// Resets to uninitialized state. `max_rate` is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.value = T::ZERO;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> T {
        self.count += 1;
        if self.count == 1 {
            self.value = sample;
            return sample;
        }
        self.value = sample.clamp_to(
            self.value.sat_sub(self.max_rate),
            self.value.sat_add(self.max_rate),
        );
        self.value
    }
}

impl Slew<f64> {
    /// Feeds a sample. Returns the rate-limited output.
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

impl Slew<i64> {
    /// Feeds a sample. Returns the rate-limited output.
    #[must_use]
    #[inline]
    pub fn update(&mut self, sample: i64) -> i64 {
        self.fold(sample)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i64_band_saturates_at_the_type_bounds() {
        let mut s = Slew::<i64>::new(10).unwrap();
        assert_eq!(s.value(), None);
        assert_eq!(s.update(i64::MAX - 3), i64::MAX - 3);
        // The band's upper edge would overflow; it saturates and the sample
        // inside it passes.
        assert_eq!(s.update(i64::MAX), i64::MAX);
        assert_eq!(s.update(0), i64::MAX - 10);

        let mut s = Slew::<i64>::new(i64::MAX).unwrap();
        assert_eq!(s.update(i64::MIN), i64::MIN);
        assert_eq!(s.update(i64::MAX), -1);
        assert_eq!(s.value(), Some(-1));
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn spike_clamped() {
        let mut s = Slew::<f64>::new(10.0).unwrap();
        assert_eq!(s.update(100.0).unwrap(), 100.0); // first sample, pass through
        assert_eq!(s.update(200.0).unwrap(), 110.0); // clamped: 100 + 10
        assert_eq!(s.update(200.0).unwrap(), 120.0); // clamped: 110 + 10
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn gradual_passes_through() {
        let mut s = Slew::<f64>::new(10.0).unwrap();
        assert_eq!(s.update(100.0).unwrap(), 100.0);
        assert_eq!(s.update(105.0).unwrap(), 105.0); // within rate, passes through
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn negative_clamped() {
        let mut s = Slew::<f64>::new(10.0).unwrap();
        assert_eq!(s.update(100.0).unwrap(), 100.0);
        assert_eq!(s.update(50.0).unwrap(), 90.0); // clamped: 100 - 10
    }

    #[test]
    fn i64_basic() {
        let mut s = Slew::<i64>::new(5).unwrap();
        assert_eq!(s.update(100), 100);
        assert_eq!(s.update(200), 105);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn reset() {
        let mut s = Slew::<f64>::new(10.0).unwrap();
        s.update(100.0).unwrap();
        s.reset();
        assert_eq!(s.update(50.0).unwrap(), 50.0); // re-initialized
    }

    #[test]
    fn rejects_zero_max_rate() {
        assert!(matches!(
            Slew::<f64>::new(0.0),
            Err(crate::ConfigError::Invalid(_))
        ));
        assert!(matches!(
            Slew::<i64>::new(0),
            Err(crate::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut s = Slew::<f64>::new(10.0).unwrap();
        assert!(matches!(
            s.update(f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
        assert!(matches!(
            s.update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        ));
        assert!(matches!(
            s.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        ));
    }
}
