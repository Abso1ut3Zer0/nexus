//! Huber EMA: outlier-robust exponential moving average.

use core::hint::select_unpredictable;

use nexus_stats_core::math::MulAdd;
use nexus_stats_core::parts::EwWeight;

/// Huber EMA: an EMA whose step per sample is bounded.
///
/// The deviation of each sample from the current value is clipped to
/// `[-delta, delta]` before it is blended in (Huber's clipped residual), so
/// one outlier moves the value by at most `alpha * delta`.
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
/// use nexus_stats_smoothing::HuberEma;
///
/// let mut ema = HuberEma::builder().alpha(0.5).delta(4.0).build().unwrap();
/// assert_eq!(ema.update(10.0), Some(10.0));
/// assert_eq!(ema.update(12.0), Some(11.0)); // within delta: a plain EMA step
/// assert_eq!(ema.update(1000.0), Some(13.0)); // clipped: moves alpha * delta
/// ```
#[derive(Debug, Clone)]
pub struct HuberEma {
    alpha: f64,
    delta: f64,
    value: f64,
    count: u64,
    /// Samples needed before the value is reported: `min_samples`, or 0 when
    /// seeded. Zero also means "do not take the first sample as the value".
    prime_at: u64,
    /// What `reset` restores: the seed, or 0.0 when unseeded.
    start: f64,
}

/// Builder for [`HuberEma`].
#[derive(Debug, Clone)]
pub struct HuberEmaBuilder {
    weight: Option<EwWeight>,
    delta: Option<f64>,
    min_samples: u64,
    seed: Option<f64>,
}

impl HuberEma {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> HuberEmaBuilder {
        HuberEmaBuilder {
            weight: None,
            delta: None,
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
        // PERF: `f64::clamp` without its `low <= high` check, which `build`
        // guarantees. The hint keeps both selects branchless.
        #[inline]
        fn clamp(value: f64, low: f64, high: f64) -> f64 {
            debug_assert!(low <= high);
            let clamped = select_unpredictable(value < low, low, value);
            select_unpredictable(clamped > high, high, clamped)
        }

        let first_unseeded = self.count == 0 && self.prime_at != 0;
        self.count += 1;
        if first_unseeded {
            self.value = sample;
            return self.value();
        }

        let deviation = clamp(sample - self.value, -self.delta, self.delta);
        self.value = self.alpha.fma(deviation, self.value);
        self.value()
    }

    /// Checked update. Feeds `sample` and returns the smoothed value, or
    /// returns an error and leaves the average unchanged if `sample` is NaN
    /// or infinite.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `sample` is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if
    ///   `sample` is infinite.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::DataError;
    /// use nexus_stats_smoothing::HuberEma;
    ///
    /// let mut ema = HuberEma::builder().alpha(0.5).delta(4.0).build().unwrap();
    /// assert_eq!(ema.checked_update(10.0), Ok(Some(10.0)));
    /// assert_eq!(ema.checked_update(f64::NAN), Err(DataError::NotANumber));
    /// assert_eq!(ema.value(), Some(10.0));
    /// ```
    #[inline]
    pub fn checked_update(
        &mut self,
        sample: f64,
    ) -> Result<Option<f64>, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_input(sample, f64::MAX)?;
        Ok(self.update(sample))
    }

    /// Current smoothed value, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<f64> {
        self.is_primed().then_some(self.value)
    }

    /// The smoothing factor alpha.
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.alpha
    }

    /// The clipping threshold delta.
    #[must_use]
    pub fn delta(&self) -> f64 {
        self.delta
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
    pub fn reset_with_seed(&mut self, value: f64) -> Result<(), nexus_stats_core::ConfigError> {
        if !value.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "seed must be finite",
            ));
        }
        self.start = value;
        self.prime_at = 0;
        self.reset();
        Ok(())
    }
}

impl HuberEmaBuilder {
    /// Direct smoothing factor. Must be in (0, 1) exclusive.
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Samples for weight to decay by half. Must be positive and finite.
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Span in samples (`alpha = 2 / (n + 1)`). Must be at least 2.
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(EwWeight::Span(n));
        self
    }

    /// The largest deviation blended in at full size. Must be positive and
    /// finite.
    #[must_use]
    pub fn delta(mut self, delta: f64) -> Self {
        self.delta = Some(delta);
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

    /// Builds the Huber EMA.
    ///
    /// # Errors
    ///
    /// - `Missing` if no weight (`alpha`, `halflife`, `span`) or no `delta`
    ///   was set.
    /// - `Invalid` if the weight is out of range (the message names the knob
    ///   set) or `delta` is not positive and finite.
    /// - `Invalid` if `min_samples` is 0 or the seed is not finite.
    pub fn build(self) -> Result<HuberEma, nexus_stats_core::ConfigError> {
        use nexus_stats_core::ConfigError::{Invalid, Missing};

        let alpha = self.weight.ok_or(Missing("alpha"))?.resolve()?;
        let delta = self.delta.ok_or(Missing("delta"))?;
        if !nexus_stats_core::math::positive_finite(delta) {
            return Err(Invalid("delta must be positive and finite"));
        }
        if self.min_samples == 0 {
            return Err(Invalid("min_samples must be >= 1"));
        }
        if self.seed.is_some_and(|seed| !seed.is_finite()) {
            return Err(Invalid("seed must be finite"));
        }

        let start = self.seed.unwrap_or(0.0);
        Ok(HuberEma {
            alpha,
            delta,
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
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    fn basic_huber() -> HuberEma {
        HuberEma::builder().alpha(0.1).delta(5.0).build().unwrap()
    }

    #[test]
    fn normal_inputs_behave_like_ema() {
        let mut h = basic_huber();
        // All inputs within delta of each other → standard EMA
        for &v in &[10.0, 10.5, 9.8, 10.2, 10.1] {
            h.update(v);
        }
        let val = h.value().unwrap();
        assert!((val - 10.0).abs() < 1.0, "value={val}, expected ~10.0");
    }

    #[test]
    fn spike_is_capped() {
        let mut h = basic_huber();
        // Converge to ~10
        for _ in 0..50 {
            h.update(10.0);
        }
        let before = h.value().unwrap();

        // Huge spike — step should be capped at alpha * delta = 0.1 * 5 = 0.5
        h.update(1000.0);
        let after = h.value().unwrap();
        let move_size = (after - before).abs();

        assert!(
            move_size <= 0.5 + 1e-10,
            "move={move_size}, expected <= 0.5 (alpha*delta)"
        );
    }

    #[test]
    fn sustained_shift_converges() {
        let mut h = basic_huber();
        for _ in 0..50 {
            h.update(10.0);
        }
        // Shift to 20 — bounded steps, but should eventually converge
        for _ in 0..500 {
            h.update(20.0);
        }
        let val = h.value().unwrap();
        assert!(
            (val - 20.0).abs() < 1.0,
            "value={val}, expected ~20.0 after sustained shift"
        );
    }

    #[test]
    fn infinite_delta_is_standard_ema() {
        let mut h = HuberEma::builder()
            .alpha(0.1)
            .delta(f64::MAX)
            .build()
            .unwrap();
        let mut ema_val = 0.0f64;
        for (i, &v) in [5.0, 10.0, 15.0, 20.0, 25.0].iter().enumerate() {
            h.update(v);
            if i == 0 {
                ema_val = v;
            } else {
                ema_val = 0.1f64.mul_add(v, 0.9 * ema_val);
            }
        }
        assert!(
            (h.value().unwrap() - ema_val).abs() < 1e-10,
            "huber={}, ema={}",
            h.value().unwrap(),
            ema_val
        );
    }

    #[test]
    fn rejects_invalid_config() {
        assert!(HuberEma::builder().delta(5.0).build().is_err()); // missing alpha
        assert!(HuberEma::builder().alpha(0.1).build().is_err()); // missing delta
        assert!(HuberEma::builder().alpha(0.0).delta(5.0).build().is_err()); // alpha = 0
        assert!(HuberEma::builder().alpha(0.1).delta(-1.0).build().is_err()); // negative delta
    }

    #[test]
    fn reset_clears_state() {
        let mut h = basic_huber();
        for _ in 0..10 {
            h.update(100.0);
        }
        h.reset();
        assert_eq!(h.count(), 0);
        assert!(!h.is_primed());
    }

    #[test]
    fn steps_are_exact_inside_and_outside_delta() {
        let mut h = HuberEma::builder().alpha(0.5).delta(4.0).build().unwrap();
        assert_eq!(h.update(10.0), Some(10.0));
        assert_eq!(h.update(12.0), Some(11.0));
        assert_eq!(h.update(1000.0), Some(13.0));
        assert_eq!(h.update(-1000.0), Some(11.0));
        // Exactly delta away is not clipped.
        assert_eq!(h.update(15.0), Some(13.0));
    }

    #[test]
    fn seed_is_a_value_not_a_sample() {
        let mut h = HuberEma::builder()
            .alpha(0.5)
            .delta(4.0)
            .min_samples(10)
            .seed(100.0)
            .build()
            .unwrap();
        assert_eq!((h.count(), h.value()), (0, Some(100.0)));
        // The first sample is smoothed into the seed, clipped like any other.
        assert_eq!(h.update(200.0), Some(102.0));
        h.reset();
        assert_eq!((h.count(), h.value()), (0, Some(100.0)));
    }

    #[test]
    fn reset_with_seed_starts_from_the_new_seed() {
        let mut h = HuberEma::builder().alpha(0.5).delta(4.0).build().unwrap();
        h.update(10.0);
        h.reset_with_seed(100.0).unwrap();
        assert_eq!((h.count(), h.value()), (0, Some(100.0)));
        assert_eq!(h.update(98.0), Some(99.0));

        assert!(h.reset_with_seed(f64::INFINITY).is_err());
        assert_eq!((h.count(), h.value()), (1, Some(99.0)));

        // On an instance built with a seed, the new one replaces it.
        let mut seeded = HuberEma::builder()
            .alpha(0.5)
            .delta(4.0)
            .seed(1.0)
            .build()
            .unwrap();
        seeded.reset_with_seed(50.0).unwrap();
        seeded.update(52.0);
        seeded.reset();
        assert_eq!((seeded.count(), seeded.value()), (0, Some(50.0)));
    }

    #[test]
    fn span_and_halflife_set_the_weight() {
        // Span 3 is alpha 0.5; a half-life of one sample is alpha 0.5.
        let by_span = HuberEma::builder().span(3).delta(4.0).build().unwrap();
        assert_eq!(by_span.alpha(), 0.5);
        #[cfg(any(feature = "std", feature = "libm"))]
        {
            let by_halflife = HuberEma::builder()
                .halflife(1.0)
                .delta(4.0)
                .build()
                .unwrap();
            assert_eq!(by_halflife.alpha(), 0.5);
        }
    }

    #[test]
    fn a_bad_knob_is_reported_under_its_own_name() {
        use nexus_stats_core::ConfigError::{Invalid, Missing};
        let b = HuberEma::builder;
        assert_eq!(b().delta(1.0).build().unwrap_err(), Missing("alpha"));
        assert_eq!(b().alpha(0.1).build().unwrap_err(), Missing("delta"));
        assert_eq!(
            b().span(1).delta(1.0).build().unwrap_err(),
            Invalid("span must be at least 2")
        );
        assert_eq!(
            b().alpha(1e-17).delta(1.0).build().unwrap_err(),
            Invalid("alpha is too small for a usable weight")
        );
        for delta in [0.0, -1.0, f64::NAN, f64::INFINITY] {
            assert_eq!(
                b().alpha(0.1).delta(delta).build().unwrap_err(),
                Invalid("delta must be positive and finite")
            );
        }
        assert_eq!(
            b().alpha(0.1)
                .delta(1.0)
                .seed(f64::NAN)
                .build()
                .unwrap_err(),
            Invalid("seed must be finite")
        );
        assert_eq!(
            b().alpha(0.1)
                .delta(1.0)
                .min_samples(0)
                .build()
                .unwrap_err(),
            Invalid("min_samples must be >= 1")
        );
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use nexus_stats_core::DataError::{Infinite, NotANumber};

        let mut h = basic_huber();
        h.checked_update(10.0).unwrap();

        assert_eq!(h.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(h.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(h.checked_update(f64::NEG_INFINITY), Err(Infinite));

        assert_eq!((h.count(), h.value()), (1, Some(10.0)));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = basic_huber();
        let mut unchecked = checked.clone();
        for x in [2.0, 0.5, 1e300, -3.25] {
            assert_eq!(checked.checked_update(x), Ok(unchecked.update(x)));
        }
    }

    #[test]
    fn update_does_not_validate() {
        let mut h = basic_huber();
        h.update(1.0);
        assert!(h.update(f64::NAN).unwrap().is_nan());
        assert_eq!(h.count(), 2);
    }
}
