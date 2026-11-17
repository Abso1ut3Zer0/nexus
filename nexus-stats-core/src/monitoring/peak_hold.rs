use crate::Sample;

/// Peak hold with decay — instant attack, configurable hold, then decay.
///
/// Captures peaks instantly and holds them for a configurable number of
/// samples. After the hold, `PeakHold<f64>` decays the peak exponentially
/// by `decay_rate` per sample, capturing any sample above the decayed
/// peak; `PeakHold<i64>` drops the peak to the current sample (integers
/// have no fractional decay). `PeakHold<f64>` rejects NaN and infinity and
/// returns `Result`; `PeakHold<i64>` cannot fail.
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

    /// Current held (or decayed) peak.
    #[inline]
    #[must_use]
    pub fn peak(&self) -> T {
        self.peak
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

    #[inline]
    fn fold(&mut self, sample: T) -> T {
        self.count += 1;
        // Instant attack: a new peak, or the very first sample.
        if sample >= self.peak || self.count == 1 {
            self.peak = sample;
            self.hold_remaining = self.hold_samples;
            return self.peak;
        }
        // Hold period.
        if self.hold_remaining > 0 {
            self.hold_remaining -= 1;
            return self.peak;
        }
        // Hold expired: decay, then capture anything at or above the decayed peak.
        self.peak = T::decay(self.peak, self.decay, sample);
        if sample >= self.peak {
            self.peak = sample;
            self.hold_remaining = self.hold_samples;
        }
        self.peak
    }
}

impl PeakHold<f64> {
    /// Feeds a sample. Returns the current peak.
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

impl PeakHold<i64> {
    /// Feeds a sample. Returns the current peak.
    #[inline]
    pub fn update(&mut self, sample: i64) -> i64 {
        self.fold(sample)
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
    pub fn build(self) -> Result<PeakHold<f64>, crate::ConfigError> {
        let rate = self
            .decay
            .ok_or(crate::ConfigError::Missing("decay_rate"))?;
        if !(rate > 0.0 && rate <= 1.0) {
            return Err(crate::ConfigError::Invalid("decay_rate must be in (0, 1]"));
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
    pub fn build(self) -> Result<PeakHold<i64>, crate::ConfigError> {
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
        assert_eq!(ph.update(50), 100); // held
        assert_eq!(ph.update(50), 100); // held
        assert_eq!(ph.update(50), 100); // held
        assert_eq!(ph.update(50), 50); // hold expired, reset to current
    }

    #[test]
    fn reset() {
        let mut ph = PeakHold::<f64>::builder().decay_rate(0.95).build().unwrap();
        let _ = ph.update(100.0).unwrap();
        ph.reset();
        assert_eq!(ph.count(), 0);
    }

    #[test]
    fn errors_without_decay_rate() {
        let result = PeakHold::<f64>::builder().build();
        assert!(matches!(
            result,
            Err(crate::ConfigError::Missing("decay_rate"))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut ph = PeakHold::<f64>::builder().decay_rate(0.95).build().unwrap();
        assert!(matches!(
            ph.update(f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
        assert!(matches!(
            ph.update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        ));
        assert!(matches!(
            ph.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        ));
    }
}
