use crate::math::{EwWeight, MulAdd};

/// Asymmetric EMA: one smoothing factor for rising samples, another for
/// falling ones.
///
/// Uses `alpha_up` when the sample is above the current value and
/// `alpha_down` otherwise, for fast attack and slow decay or the reverse.
///
/// # Seeding
///
/// `seed(v)` starts the average at `v`, as if it had already converged
/// there: the value is available at once and the first sample is smoothed
/// into it. `count()` still counts only samples fed, and `reset()` returns
/// to the seed.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::smoothing::AsymEma;
///
/// let mut ema = AsymEma::builder()
///     .alpha_up(0.5)
///     .alpha_down(0.25)
///     .build()
///     .unwrap();
/// assert_eq!(ema.update(8.0), Some(8.0));
/// assert_eq!(ema.update(16.0), Some(12.0)); // rising: half the gap
/// assert_eq!(ema.update(8.0), Some(11.0)); // falling: a quarter
/// ```
#[derive(Debug, Clone)]
pub struct AsymEma {
    alpha_up: f64,
    alpha_down: f64,
    value: f64,
    count: u64,
    /// Samples needed before the value is reported: `min_samples`, or 0 when
    /// seeded. Zero also means "do not take the first sample as the value".
    prime_at: u64,
    /// What `reset` restores: the seed, or 0.0 when unseeded.
    start: f64,
}

/// Builder for [`AsymEma`].
#[derive(Debug, Clone)]
pub struct AsymEmaBuilder {
    alpha_up: Option<EwWeight>,
    alpha_down: Option<EwWeight>,
    min_samples: u64,
    seed: Option<f64>,
}

impl AsymEma {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> AsymEmaBuilder {
        AsymEmaBuilder {
            alpha_up: None,
            alpha_down: None,
            min_samples: 1,
            seed: None,
        }
    }

    /// Feeds a sample. Returns the smoothed value once primed.
    ///
    /// The first sample becomes the value, unless the average was seeded,
    /// in which case it is smoothed into the seed.
    ///
    /// Does not validate `sample`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, sample: f64) -> Option<f64> {
        let first_unseeded = self.count == 0 && self.prime_at != 0;
        self.count += 1;
        if first_unseeded {
            self.value = sample;
            return self.value();
        }

        let alpha = if sample > self.value {
            self.alpha_up
        } else {
            self.alpha_down
        };
        self.value = alpha.fma(sample - self.value, self.value);
        self.value()
    }

    /// Checked update. Feeds `sample` and returns the smoothed value, or
    /// returns an error and leaves the average unchanged if `sample` is NaN
    /// or infinite.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `sample`
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if `sample` is
    ///   infinite.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::{DataError, smoothing::AsymEma};
    ///
    /// let mut ema = AsymEma::builder()
    ///     .alpha_up(0.5)
    ///     .alpha_down(0.25)
    ///     .build()
    ///     .unwrap();
    /// assert_eq!(ema.checked_update(8.0), Ok(Some(8.0)));
    /// assert_eq!(ema.checked_update(f64::NAN), Err(DataError::NotANumber));
    /// assert_eq!(ema.value(), Some(8.0));
    /// ```
    #[inline]
    pub fn checked_update(&mut self, sample: f64) -> Result<Option<f64>, crate::DataError> {
        crate::math::check_input(sample, f64::MAX)?;
        Ok(self.update(sample))
    }

    /// Current smoothed value, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<f64> {
        self.is_primed().then_some(self.value)
    }

    /// Number of samples fed since construction or `reset`. A seed is not a
    /// sample.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether a value is available: `min_samples` reached, or seeded.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.prime_at
    }

    /// Returns to no samples, and to the seed if there is one. Parameters
    /// unchanged.
    pub fn reset(&mut self) {
        self.value = self.start;
        self.count = 0;
    }

    /// Resets to no samples, starting from `value` as a new seed.
    ///
    /// The value is available at once (`min_samples` no longer applies), and
    /// later calls to [`reset`](Self::reset) return to this seed.
    ///
    /// # Errors
    ///
    /// `Invalid` if `value` is not finite. The average is left unchanged.
    pub fn reset_with_seed(&mut self, value: f64) -> Result<(), crate::ConfigError> {
        if !value.is_finite() {
            return Err(crate::ConfigError::Invalid("seed must be finite"));
        }
        self.start = value;
        self.prime_at = 0;
        self.reset();
        Ok(())
    }
}

impl AsymEmaBuilder {
    /// Smoothing factor for a sample above the current value. Must be in
    /// (0, 1) exclusive.
    #[must_use]
    pub fn alpha_up(mut self, alpha: f64) -> Self {
        self.alpha_up = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Smoothing factor for a sample at or below the current value. Must be
    /// in (0, 1) exclusive.
    #[must_use]
    pub fn alpha_down(mut self, alpha: f64) -> Self {
        self.alpha_down = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Rising weight as a half-life in samples. Must be positive and finite.
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife_up(mut self, halflife: f64) -> Self {
        self.alpha_up = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Falling weight as a half-life in samples. Must be positive and
    /// finite.
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife_down(mut self, halflife: f64) -> Self {
        self.alpha_down = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Rising weight as a span (`alpha = 2 / (n + 1)`). Must be at least 2.
    #[must_use]
    pub fn span_up(mut self, n: u64) -> Self {
        self.alpha_up = Some(EwWeight::Span(n));
        self
    }

    /// Falling weight as a span (`alpha = 2 / (n + 1)`). Must be at least 2.
    #[must_use]
    pub fn span_down(mut self, n: u64) -> Self {
        self.alpha_down = Some(EwWeight::Span(n));
        self
    }

    /// Minimum samples before the value is valid. Default: 1.
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Starts the average at `value`.
    ///
    /// The value is available at once (`min_samples` no longer applies), the
    /// first sample is smoothed into it, and `reset()` returns to it.
    #[must_use]
    pub fn seed(mut self, value: f64) -> Self {
        self.seed = Some(value);
        self
    }

    /// Builds the asymmetric EMA.
    ///
    /// # Errors
    ///
    /// - `Missing` if the rising or the falling weight was not set.
    /// - `Invalid` if a weight is out of range; the message names the knob
    ///   set.
    /// - `Invalid` if `min_samples` is 0 or the seed is not finite.
    pub fn build(self) -> Result<AsymEma, crate::ConfigError> {
        let alpha_up = self
            .alpha_up
            .ok_or(crate::ConfigError::Missing("alpha_up"))?
            .resolve()?;
        let alpha_down = self
            .alpha_down
            .ok_or(crate::ConfigError::Missing("alpha_down"))?
            .resolve()?;
        if self.min_samples == 0 {
            return Err(crate::ConfigError::Invalid("min_samples must be >= 1"));
        }
        if self.seed.is_some_and(|seed| !seed.is_finite()) {
            return Err(crate::ConfigError::Invalid("seed must be finite"));
        }

        let start = self.seed.unwrap_or(0.0);
        Ok(AsymEma {
            alpha_up,
            alpha_down,
            value: start,
            count: 0,
            prime_at: if self.seed.is_some() {
                0
            } else {
                self.min_samples
            },
            start,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::float_cmp)]
    fn each_direction_uses_its_own_weight() {
        let mut ema = AsymEma::builder()
            .alpha_up(0.5)
            .alpha_down(0.25)
            .build()
            .unwrap();
        assert_eq!(ema.update(8.0), Some(8.0));
        // Rising: 8 + 0.5 * (16 - 8).
        assert_eq!(ema.update(16.0), Some(12.0));
        // Falling: 12 + 0.25 * (4 - 12).
        assert_eq!(ema.update(4.0), Some(10.0));
        // Equal to the value counts as not rising; either weight leaves it.
        assert_eq!(ema.update(10.0), Some(10.0));
    }

    #[test]
    fn rejects_bad_weights_and_zero_min_samples() {
        use crate::ConfigError::Invalid;
        let base = || AsymEma::builder().alpha_up(0.5).alpha_down(0.5);
        assert_eq!(
            base().alpha_up(1.0).build().unwrap_err(),
            Invalid("alpha must be in (0, 1)")
        );
        assert_eq!(
            base().span_down(1).build().unwrap_err(),
            Invalid("span must be at least 2")
        );
        assert_eq!(
            base().min_samples(0).build().unwrap_err(),
            Invalid("min_samples must be >= 1")
        );
        assert!(base().span_up(2).span_down(50).build().is_ok());
    }

    #[test]
    fn fast_attack_slow_decay() {
        let mut ema = AsymEma::builder()
            .alpha_up(0.9) // fast attack
            .alpha_down(0.1) // slow decay
            .build()
            .unwrap();

        ema.update(0.0); // initialize
        ema.update(100.0); // fast attack
        let after_attack = ema.value().unwrap();

        ema.update(0.0); // slow decay
        let after_decay = ema.value().unwrap();

        // Attack should move a lot, decay should move little
        assert!(
            after_attack > 50.0,
            "fast attack should jump, got {after_attack}"
        );
        assert!(
            after_decay > 30.0,
            "slow decay should hold, got {after_decay}"
        );
    }

    #[test]
    fn asymmetric_response() {
        let mut fast_up = AsymEma::builder()
            .alpha_up(0.9)
            .alpha_down(0.1)
            .build()
            .unwrap();
        let mut fast_down = AsymEma::builder()
            .alpha_up(0.1)
            .alpha_down(0.9)
            .build()
            .unwrap();

        fast_up.update(50.0);
        fast_down.update(50.0);

        fast_up.update(100.0);
        fast_down.update(100.0);

        // fast_up should be closer to 100
        assert!(fast_up.value().unwrap() > fast_down.value().unwrap());
    }

    #[test]
    fn priming() {
        let mut ema = AsymEma::builder()
            .alpha_up(0.5)
            .alpha_down(0.5)
            .min_samples(5)
            .build()
            .unwrap();

        for _ in 0..4 {
            assert!(ema.update(100.0).is_none());
        }
        assert!(ema.update(100.0).is_some());
    }

    #[test]
    fn reset() {
        let mut ema = AsymEma::builder()
            .alpha_up(0.5)
            .alpha_down(0.5)
            .build()
            .unwrap();
        ema.update(100.0);
        ema.reset();
        assert_eq!(ema.count(), 0);
        assert!(ema.value().is_none());
    }

    #[test]
    fn errors_without_alpha_up() {
        let result = AsymEma::builder().alpha_down(0.5).build();
        assert!(matches!(
            result,
            Err(crate::ConfigError::Missing("alpha_up"))
        ));
    }

    fn pair() -> AsymEma {
        AsymEma::builder()
            .alpha_up(0.5)
            .alpha_down(0.25)
            .build()
            .unwrap()
    }

    #[test]
    fn rising_and_falling_use_their_own_weight() {
        let mut ema = pair();
        assert_eq!(ema.update(8.0), Some(8.0));
        assert_eq!(ema.update(16.0), Some(12.0));
        assert_eq!(ema.update(8.0), Some(11.0));
        // A sample equal to the value takes the falling weight and moves
        // nothing.
        assert_eq!(ema.update(11.0), Some(11.0));
    }

    #[test]
    fn seed_is_a_value_not_a_sample() {
        let mut ema = AsymEma::builder()
            .alpha_up(0.5)
            .alpha_down(0.25)
            .min_samples(10)
            .seed(100.0)
            .build()
            .unwrap();
        assert_eq!((ema.count(), ema.value()), (0, Some(100.0)));
        assert_eq!(ema.update(200.0), Some(150.0));
        ema.reset();
        assert_eq!((ema.count(), ema.value()), (0, Some(100.0)));
    }

    #[test]
    fn reset_with_seed_starts_from_the_new_seed() {
        let mut ema = pair();
        ema.update(8.0);
        ema.reset_with_seed(100.0).unwrap();
        assert_eq!((ema.count(), ema.value()), (0, Some(100.0)));
        assert_eq!(ema.update(60.0), Some(90.0));

        assert!(ema.reset_with_seed(f64::NAN).is_err());
        assert_eq!((ema.count(), ema.value()), (1, Some(90.0)));
    }

    #[test]
    fn a_bad_seed_is_refused_at_build() {
        for bad in [f64::NAN, f64::INFINITY] {
            assert!(
                AsymEma::builder()
                    .alpha_up(0.5)
                    .alpha_down(0.25)
                    .seed(bad)
                    .build()
                    .is_err()
            );
        }
    }

    #[test]
    #[cfg(any(feature = "std", feature = "libm"))]
    fn halflife_sets_each_weight() {
        // A half-life of one sample is a weight of one half.
        let mut ema = AsymEma::builder()
            .halflife_up(1.0)
            .halflife_down(1.0)
            .build()
            .unwrap();
        ema.update(0.0);
        assert_eq!(ema.update(8.0), Some(4.0));
        assert_eq!(ema.update(0.0), Some(2.0));
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber};

        let mut ema = pair();
        ema.checked_update(8.0).unwrap();

        assert_eq!(ema.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(ema.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(ema.checked_update(f64::NEG_INFINITY), Err(Infinite));

        assert_eq!((ema.count(), ema.value()), (1, Some(8.0)));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = pair();
        let mut unchecked = checked.clone();
        for x in [2.0, 0.5, 1e300, -3.25] {
            assert_eq!(checked.checked_update(x), Ok(unchecked.update(x)));
        }
    }

    #[test]
    fn update_does_not_validate() {
        let mut ema = pair();
        ema.update(1.0);
        assert!(ema.update(f64::NAN).unwrap().is_nan());
        assert_eq!(ema.count(), 2);
    }
}
