use nexus_stats_core::Sample;

/// Peak hold with decay — instant attack, configurable hold, then decay.
///
/// Captures peaks instantly and holds them for a configurable number of
/// samples. After the hold, `PeakHold<f64>` decays the peak exponentially
/// by `decay_rate` per sample, capturing any sample above the decayed
/// peak; `PeakHold<i64>` drops the peak to the current sample (integers
/// have no fractional decay).
///
/// A NaN is ignored. An infinite sample becomes a peak that holds until
/// [`reset`](Self::reset); `PeakHold<f64>` has a `checked_update` that
/// refuses it. The decay multiplies the peak, so it suits magnitudes: a
/// negative peak moves up toward zero.
///
/// # Use Cases
/// - VU meter / level indicator behavior
/// - Peak envelope tracking
/// - "What was the recent peak?" with graceful decay
///
/// # Weighting clock
///
/// Per `update` call: every sample counts the same. Correct when samples
/// are evenly spaced, or one per event where per-event weighting is wanted.
/// Never feed it from a loop whose iteration time depends on the quantity
/// being measured.
#[derive(Debug, Clone)]
pub struct PeakHold<T: Sample> {
    peak: T,
    hold_samples: u64,
    hold_remaining: u64,
    decay: T::Decay,
    count: u64,
}

/// Builder for [`PeakHold`].
#[derive(Debug, Clone)]
pub struct PeakHoldBuilder<T: Sample> {
    hold_samples: u64,
    decay: Option<T::Decay>,
}

impl<T: Sample> PeakHold<T> {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> PeakHoldBuilder<T> {
        PeakHoldBuilder {
            hold_samples: 0,
            decay: None,
        }
    }

    /// The held or decayed peak, or `None` before the first sample.
    #[inline]
    #[must_use]
    pub fn peak(&self) -> Option<T> {
        if self.count == 0 {
            return None;
        }
        Some(self.peak)
    }

    /// Number of samples processed.
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

    /// Resets to empty state. Configuration is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.peak = T::ZERO;
        self.hold_remaining = 0;
        self.count = 0;
    }

    /// Feeds a sample and returns the peak, or `None` if no sample has been
    /// taken yet.
    ///
    /// A NaN is ignored, as [`f64::max`] ignores one: it is not a peak and
    /// does not count as a step. An infinite sample becomes a peak that
    /// does not decay; [`PeakHold::<f64>::checked_update`] refuses it.
    #[inline]
    pub fn update(&mut self, sample: T) -> Option<T> {
        if sample.is_nan() {
            return self.peak();
        }
        self.count += 1;
        // Instant attack: a new peak, or the very first sample.
        if sample >= self.peak || self.count == 1 {
            return Some(self.capture(sample));
        }
        // Hold period.
        if self.hold_remaining > 0 {
            self.hold_remaining -= 1;
            return Some(self.peak);
        }
        // Hold expired: decay, then capture anything at or above the decayed peak.
        self.peak = T::decay(self.peak, self.decay, sample);
        if sample >= self.peak {
            return Some(self.capture(sample));
        }
        Some(self.peak)
    }

    /// Takes `sample` as the peak and restarts the hold.
    #[inline]
    fn capture(&mut self, sample: T) -> T {
        self.peak = sample;
        self.hold_remaining = self.hold_samples;
        sample
    }
}

impl PeakHold<f64> {
    /// Checked update. Feeds `sample`, or returns an error and leaves the
    /// tracker unchanged if `sample` is NaN or infinite.
    ///
    /// An infinite peak times the decay rate is still infinite, so it
    /// would hold until [`reset`](Self::reset).
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `sample` is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if
    ///   `sample` is infinite.
    #[inline]
    pub fn checked_update(
        &mut self,
        sample: f64,
    ) -> Result<Option<f64>, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_input(sample, f64::MAX)?;
        Ok(self.update(sample))
    }
}

impl<T: Sample> PeakHoldBuilder<T> {
    /// Samples to hold a peak before decay begins. Default 0.
    #[inline]
    #[must_use]
    pub fn hold_samples(mut self, n: u64) -> Self {
        self.hold_samples = n;
        self
    }
}

impl PeakHoldBuilder<f64> {
    /// Multiplicative decay per sample after the hold, in (0, 1].
    #[inline]
    #[must_use]
    pub fn decay_rate(mut self, rate: f64) -> Self {
        self.decay = Some(rate);
        self
    }

    /// Builds the tracker.
    ///
    /// # Errors
    ///
    /// `ConfigError::Missing` if `decay_rate` was not set;
    /// `ConfigError::Invalid` if it is outside (0, 1].
    #[inline]
    pub fn build(self) -> Result<PeakHold<f64>, nexus_stats_core::ConfigError> {
        let rate = self
            .decay
            .ok_or(nexus_stats_core::ConfigError::Missing("decay_rate"))?;
        if !(rate > 0.0 && rate <= 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "decay_rate must be in (0, 1]",
            ));
        }
        Ok(PeakHold {
            peak: 0.0,
            hold_samples: self.hold_samples,
            hold_remaining: 0,
            decay: rate,
            count: 0,
        })
    }
}

impl PeakHoldBuilder<i64> {
    /// Builds the tracker.
    ///
    /// # Errors
    ///
    /// Never fails for `i64`; the `Result` keeps the builder shape uniform.
    #[inline]
    pub fn build(self) -> Result<PeakHold<i64>, nexus_stats_core::ConfigError> {
        Ok(PeakHold {
            peak: 0,
            hold_samples: self.hold_samples,
            hold_remaining: 0,
            decay: (),
            count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // #763: the float form used to return 0.0 for a negative-only stream
    // because the peak started at zero. It now seeds from the first sample.
    #[test]
    fn negative_only_stream_returns_its_true_peak() {
        let mut ph = PeakHold::<f64>::builder()
            .hold_samples(1)
            .decay_rate(0.9)
            .build()
            .unwrap();
        assert_eq!(ph.update(-5.0).unwrap(), -5.0);
        assert_eq!(ph.update(-3.0).unwrap(), -3.0);
        assert_eq!(ph.update(-4.0).unwrap(), -3.0, "held");
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn instant_attack() {
        let mut ph = PeakHold::<f64>::builder()
            .decay_rate(0.95)
            .hold_samples(5)
            .build()
            .unwrap();
        assert_eq!(ph.update(50.0).unwrap(), 50.0);
        assert_eq!(ph.update(100.0).unwrap(), 100.0); // instant capture
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn hold_period() {
        let mut ph = PeakHold::<f64>::builder()
            .decay_rate(0.95)
            .hold_samples(3)
            .build()
            .unwrap();
        let _ = ph.update(100.0).unwrap();
        assert_eq!(ph.update(50.0).unwrap(), 100.0); // held
        assert_eq!(ph.update(50.0).unwrap(), 100.0); // held
        assert_eq!(ph.update(50.0).unwrap(), 100.0); // held (3rd hold sample)
    }

    #[test]
    fn decay_after_hold() {
        let mut ph = PeakHold::<f64>::builder()
            .decay_rate(0.9)
            .hold_samples(0)
            .build()
            .unwrap();
        let _ = ph.update(100.0).unwrap();
        let v = ph.update(0.0).unwrap(); // decay immediately (no hold)
        assert!(
            (v - 90.0).abs() < 1e-9,
            "one decay step of 0.9 from 100, got {v}"
        );
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn new_peak_during_hold() {
        let mut ph = PeakHold::<f64>::builder()
            .decay_rate(0.95)
            .hold_samples(10)
            .build()
            .unwrap();
        let _ = ph.update(100.0).unwrap();
        let _ = ph.update(50.0).unwrap(); // holding at 100
        assert_eq!(ph.update(200.0).unwrap(), 200.0); // new peak resets hold
    }

    #[test]
    fn i64_hold() {
        let mut ph = PeakHold::<i64>::builder().hold_samples(3).build().unwrap();
        let _ = ph.update(100);
        assert_eq!(ph.update(50), Some(100)); // held
        assert_eq!(ph.update(50), Some(100)); // held
        assert_eq!(ph.update(50), Some(100)); // held
        assert_eq!(ph.update(50), Some(50)); // hold expired, reset to current
    }

    #[test]
    fn reset() {
        let mut ph = PeakHold::<f64>::builder().decay_rate(0.95).build().unwrap();
        let _ = ph.update(100.0).unwrap();
        ph.reset();
        assert_eq!((ph.count(), ph.peak()), (0, None));
    }

    #[test]
    fn errors_without_decay_rate() {
        let result = PeakHold::<f64>::builder().build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("decay_rate"))
        ));
    }

    #[test]
    fn there_is_no_peak_before_the_first_sample() {
        let ph = PeakHold::<f64>::builder().decay_rate(0.9).build().unwrap();
        assert_eq!(ph.peak(), None);
        let ph = PeakHold::<i64>::builder().build().unwrap();
        assert_eq!(ph.peak(), None);
    }

    /// Feeds `samples` with and without NaNs scattered among them: the
    /// peaks at the samples that are numbers must be the same.
    #[test]
    fn a_nan_is_ignored_as_if_it_had_not_been_fed() {
        let samples = [3.0, 7.0, 2.0, 1.0, 1.5, 9.0, 4.0, 0.5, 0.25, 6.0, 1.0, 1.0];
        for hold in [0, 1, 3] {
            let build = || {
                PeakHold::<f64>::builder()
                    .hold_samples(hold)
                    .decay_rate(0.5)
                    .build()
                    .unwrap()
            };
            let (mut plain, mut with_nans) = (build(), build());
            // Before anything: a NaN leaves no peak.
            assert_eq!(with_nans.update(f64::NAN), None);
            assert_eq!(with_nans.count(), 0);
            for (i, &x) in samples.iter().enumerate() {
                let want = plain.update(x);
                let got = with_nans.update(x);
                assert_eq!(got, want, "hold {hold} sample {i}");
                // A NaN returns the peak as it stands and changes nothing.
                if i % 2 == 0 {
                    assert_eq!(with_nans.update(f64::NAN), want);
                }
                assert_eq!(with_nans.count(), plain.count());
            }
        }
    }

    #[test]
    fn an_infinite_peak_holds_until_reset() {
        let mut ph = PeakHold::<f64>::builder().decay_rate(0.5).build().unwrap();
        ph.update(10.0);
        assert_eq!(ph.update(f64::INFINITY), Some(f64::INFINITY));
        for _ in 0..100 {
            assert_eq!(ph.update(1.0), Some(f64::INFINITY));
        }
        ph.reset();
        assert_eq!(ph.update(1.0), Some(1.0));
        // Negative infinity is only a very low sample: the next one beats it.
        ph.reset();
        assert_eq!(ph.update(f64::NEG_INFINITY), Some(f64::NEG_INFINITY));
        assert_eq!(ph.update(-3.0), Some(-3.0));
    }

    #[test]
    fn checked_update_refuses_nan_and_infinity_and_changes_nothing() {
        use nexus_stats_core::DataError::{Infinite, NotANumber};

        let mut ph = PeakHold::<f64>::builder()
            .hold_samples(2)
            .decay_rate(0.5)
            .build()
            .unwrap();
        ph.checked_update(8.0).unwrap();
        ph.checked_update(1.0).unwrap();
        let before = ph.clone();

        assert_eq!(ph.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(ph.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(ph.checked_update(f64::NEG_INFINITY), Err(Infinite));

        // Same state: the same samples give the same peaks from here.
        let mut untouched = before;
        for x in [1.0, 1.0, 1.0, 20.0, 0.0] {
            assert_eq!(ph.checked_update(x).unwrap(), untouched.update(x));
        }
        assert_eq!(ph.count(), untouched.count());
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let build = || {
            PeakHold::<f64>::builder()
                .hold_samples(1)
                .decay_rate(0.75)
                .build()
                .unwrap()
        };
        let (mut checked, mut unchecked) = (build(), build());
        for x in [5.0, -2.0, 1e300, f64::MAX, f64::MIN, 0.0, 3.5, 3.5, 1e-300] {
            assert_eq!(checked.checked_update(x).unwrap(), unchecked.update(x));
        }
    }
}
