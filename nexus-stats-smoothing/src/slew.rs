/// Slew rate limiter: caps how far the output may move per sample.
///
/// The output follows the input, but rises by at most `rising` and falls
/// by at most `falling` in one update. A jump in the input comes out as a
/// ramp; a move within the limits passes through unchanged. The first
/// sample is the first output.
///
/// The limits are per update, so they suit evenly spaced samples. See
/// [slew rate](https://en.wikipedia.org/wiki/Slew_rate) for the term.
///
/// # Examples
///
/// ```
/// use nexus_stats_smoothing::Slew;
///
/// let mut slew = Slew::new(2.0).unwrap();
/// assert_eq!(slew.update(10.0), 10.0);
/// assert_eq!(slew.update(11.0), 11.0); // within the limit
/// assert_eq!(slew.update(20.0), 13.0); // a jump becomes a ramp
/// assert_eq!(slew.update(20.0), 15.0);
/// ```
#[derive(Debug, Clone)]
pub struct Slew {
    rising: f64,
    falling: f64,
    value: f64,
    count: u64,
}

impl Slew {
    /// Creates a limiter that moves at most `max_rate` per sample in either
    /// direction.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `max_rate` is not finite and
    /// positive.
    pub fn new(max_rate: f64) -> Result<Self, nexus_stats_core::ConfigError> {
        Self::with_limits(max_rate, max_rate)
    }

    /// Creates a limiter that rises at most `rising` and falls at most
    /// `falling` per sample. Both are given as positive amounts.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if either limit is not finite and
    /// positive.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_smoothing::Slew;
    ///
    /// // Quick to fall, slow to rise.
    /// let mut slew = Slew::with_limits(1.0, 5.0).unwrap();
    /// slew.update(10.0);
    /// assert_eq!(slew.update(20.0), 11.0);
    /// assert_eq!(slew.update(0.0), 6.0);
    /// ```
    pub fn with_limits(rising: f64, falling: f64) -> Result<Self, nexus_stats_core::ConfigError> {
        if !is_limit(rising) || !is_limit(falling) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "slew limits must be finite and positive",
            ));
        }
        Ok(Self {
            rising,
            falling,
            value: 0.0,
            count: 0,
        })
    }

    /// Feeds a sample and returns the limited output.
    ///
    /// Does not validate: an infinite first sample pins the output until
    /// [`reset`](Self::reset), and a NaN is returned as the output. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, sample: f64) -> f64 {
        self.count += 1;
        if self.count == 1 {
            self.value = sample;
            return sample;
        }
        self.value = limit(sample, self.value - self.falling, self.value + self.rising);
        self.value
    }

    /// Checked update. Feeds `sample`, or returns an error and leaves the
    /// limiter unchanged if `sample` is NaN or infinite.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `sample` is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if
    ///   `sample` is infinite.
    #[inline]
    pub fn checked_update(&mut self, sample: f64) -> Result<f64, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_input(sample, f64::MAX)?;
        Ok(self.update(sample))
    }

    /// The current output, or `None` before the first sample.
    #[must_use]
    pub fn value(&self) -> Option<f64> {
        if self.count == 0 {
            return None;
        }
        Some(self.value)
    }

    /// The most the output may rise per sample.
    #[must_use]
    pub fn rising(&self) -> f64 {
        self.rising
    }

    /// The most the output may fall per sample.
    #[must_use]
    pub fn falling(&self) -> f64 {
        self.falling
    }

    /// Samples fed since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one sample has been fed.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Forgets the output. The limits are kept.
    pub fn reset(&mut self) {
        self.value = 0.0;
        self.count = 0;
    }
}

/// Whether `rate` can be a limit: finite and above zero.
fn is_limit(rate: f64) -> bool {
    rate.is_finite() && rate > 0.0
}

/// `sample` held to `[low, high]`. Unlike `f64::clamp`, never panics: with
/// a NaN on either side the sample is returned.
#[inline]
fn limit(sample: f64, low: f64, high: f64) -> f64 {
    if sample > high {
        return high;
    }
    if sample < low {
        return low;
    }
    sample
}

#[cfg(test)]
mod tests {
    use super::*;
    use nexus_stats_core::DataError::{Infinite, NotANumber};

    #[test]
    fn a_move_within_the_limits_passes_through_exactly() {
        let mut slew = Slew::new(10.0).unwrap();
        for x in [100.0, 105.0, 95.5, 95.5, 105.5, 0.1 + 0.2 + 95.5] {
            assert_eq!(slew.update(x).to_bits(), x.to_bits());
        }
    }

    #[test]
    fn a_jump_becomes_a_ramp_that_arrives_exactly() {
        let mut slew = Slew::new(2.0).unwrap();
        slew.update(11.0);
        let outputs: Vec<f64> = (0..6).map(|_| slew.update(20.0)).collect();
        assert_eq!(outputs, [13.0, 15.0, 17.0, 19.0, 20.0, 20.0]);
        assert_eq!(slew.update(12.0), 18.0);
    }

    #[test]
    fn rising_and_falling_limits_are_separate() {
        let mut slew = Slew::with_limits(1.0, 5.0).unwrap();
        assert_eq!((slew.rising(), slew.falling()), (1.0, 5.0));
        slew.update(10.0);
        assert_eq!(slew.update(100.0), 11.0);
        assert_eq!(slew.update(-100.0), 6.0);
        // `new` is the same limit both ways.
        let slew = Slew::new(3.0).unwrap();
        assert_eq!((slew.rising(), slew.falling()), (3.0, 3.0));
    }

    /// Against the rule written out directly, over a random walk with jumps.
    #[test]
    fn each_step_is_the_sample_or_the_nearest_limit() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut slew = Slew::with_limits(1.5, 4.0).unwrap();
        let mut previous = slew.update(0.0);
        for _ in 0..50_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let x = (state % 4001) as f64 / 100.0 - 20.0;
            let out = slew.update(x);
            let step = out - previous;
            assert!(step <= 1.5 + 1e-12 && step >= -4.0 - 1e-12, "step {step}");
            // Limited only when the sample is out of reach.
            if out.to_bits() != x.to_bits() {
                assert!(out == previous + 1.5 || out == previous - 4.0);
                assert!((x > out) == (out > previous));
            }
            previous = out;
        }
    }

    #[test]
    fn there_is_no_value_before_the_first_sample_or_after_reset() {
        let mut slew = Slew::new(1.0).unwrap();
        assert_eq!((slew.value(), slew.is_primed()), (None, false));
        slew.update(100.0);
        assert_eq!(slew.value(), Some(100.0));
        slew.reset();
        assert_eq!((slew.value(), slew.count()), (None, 0));
        // The first sample after a reset passes through, however far away.
        assert_eq!(slew.update(-50.0), -50.0);
    }

    #[test]
    fn limits_must_be_finite_and_positive() {
        for bad in [0.0, -1.0, f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert!(Slew::new(bad).is_err(), "{bad}");
            assert!(Slew::with_limits(1.0, bad).is_err(), "{bad}");
            assert!(Slew::with_limits(bad, 1.0).is_err(), "{bad}");
        }
        assert!(Slew::new(f64::MIN_POSITIVE).is_ok());
    }

    #[test]
    fn checked_update_refuses_nan_and_infinity_and_changes_nothing() {
        let mut slew = Slew::new(1.0).unwrap();
        // Refused as the first sample too.
        assert_eq!(slew.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!((slew.value(), slew.count()), (None, 0));

        slew.checked_update(5.0).unwrap();
        assert_eq!(slew.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(slew.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!((slew.value(), slew.count()), (Some(5.0), 1));
        assert_eq!(slew.checked_update(9.0), Ok(6.0));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let (mut checked, mut plain) = (Slew::new(0.75).unwrap(), Slew::new(0.75).unwrap());
        for x in [3.0, 4.0, -9.0, 1e300, f64::MAX, f64::MIN, 0.0, 1e-300] {
            assert_eq!(checked.checked_update(x), Ok(plain.update(x)));
        }
    }

    /// What the unchecked form does with the inputs the checked form refuses.
    #[test]
    fn update_never_panics_on_a_nan_or_an_infinity() {
        let mut slew = Slew::new(1.0).unwrap();
        slew.update(5.0);
        // An infinite sample is only a far target.
        assert_eq!(slew.update(f64::INFINITY), 6.0);
        // A NaN comes out as the output; the next sample then passes through.
        assert!(slew.update(f64::NAN).is_nan());
        assert_eq!(slew.update(50.0), 50.0);
        // An infinite first sample pins the output until reset.
        slew.reset();
        slew.update(f64::INFINITY);
        assert_eq!(slew.update(0.0), f64::INFINITY);
    }
}
