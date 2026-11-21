use crate::math::MulAdd;

/// Rounds `n` up to the next value of the form `2^k - 1`.
///
/// Examples: 1->1, 2->3, 3->3, 4->7, 5->7, 10->15, 20->31.
#[inline]
pub(crate) const fn next_power_of_two_minus_one(n: u64) -> u64 {
    if n == 0 {
        return 0;
    }
    // next_power_of_two(n + 1) - 1
    // But we need to handle the case where n+1 is already a power of 2
    let v = n + 1;
    let p = v.next_power_of_two();
    p - 1
}

/// Returns log2 of (n + 1), where n must be of the form 2^k - 1.
#[inline]
pub(crate) const fn log2_of_span_plus_one(span: u64) -> u32 {
    // span = 2^k - 1, so span + 1 = 2^k
    (span + 1).trailing_zeros()
}

/// EMA — Exponential Moving Average.
///
/// Smooths a streaming signal with exponential decay. Recent samples
/// weighted more heavily. Equivalent to a first-order IIR low-pass filter.
///
/// # Construction
///
/// Three ways to configure the smoothing factor:
/// - `alpha(a)` — direct, a ∈ (0, 1). Higher = more reactive.
/// - `halflife(h)` — samples for weight to decay by half.
/// - `span(n)` — pandas/finance convention, alpha = 2/(n+1).
///
/// # Seeding
///
/// `seed(v)` starts the average at `v`, as if it had already converged
/// there: the value is available at once and the first sample is smoothed
/// into it. `count()` still counts only samples fed, and `reset()` returns
/// to the seed.
///
/// # Use Cases
/// - Smoothing noisy latency measurements
/// - Tracking moving average of throughput
/// - Baseline estimation for anomaly detection
#[derive(Debug, Clone)]
pub struct Ema {
    alpha: f64,
    one_minus_alpha: f64,
    value: f64,
    count: u64,
    /// Samples needed before the value is reported: `min_samples`, or 0 when
    /// seeded (a seed is a value from the start). Zero therefore also means
    /// "do not initialize from the first sample".
    prime_at: u64,
    /// What `reset` restores: the seed, or 0.0 when unseeded.
    start: f64,
}

/// Builder for [`Ema`].
#[derive(Debug, Clone)]
pub struct EmaBuilder {
    weight: Option<crate::math::EwWeight>,
    min_samples: u64,
    seed: Option<f64>,
}

impl Ema {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> EmaBuilder {
        EmaBuilder {
            weight: None,
            min_samples: 1,
            seed: None,
        }
    }

    /// Feeds a sample. Returns smoothed value once primed.
    ///
    /// The first sample initializes the EMA directly (no smoothing), unless
    /// the EMA was seeded, in which case it is smoothed into the seed.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<f64>, crate::DataError> {
        check_finite!(sample);
        let first_unseeded = self.count == 0 && self.prime_at != 0;
        self.count += 1;
        self.value = if first_unseeded {
            sample
        } else {
            self.alpha.fma(sample, self.one_minus_alpha * self.value)
        };
        Ok(self.value())
    }

    /// Current smoothed value, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<f64> {
        self.is_primed().then_some(self.value)
    }

    /// The smoothing factor alpha.
    #[inline]
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.alpha
    }

    /// Number of samples processed since construction or `reset`. A seed is
    /// not a sample.
    #[inline]
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

    /// Returns to the as-built state: no samples, and the seed if one was
    /// configured. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.value = self.start;
        self.count = 0;
    }

    /// Updates the smoothing factor without resetting state.
    ///
    /// # Errors
    ///
    /// Alpha must be in (0, 1) exclusive.
    #[inline]
    pub fn reconfigure_alpha(&mut self, alpha: f64) -> Result<(), crate::ConfigError> {
        if !crate::math::in_unit_interval(alpha) {
            return Err(crate::ConfigError::Invalid("EMA alpha must be in (0, 1)"));
        }
        self.alpha = alpha;
        self.one_minus_alpha = 1.0 - alpha;
        Ok(())
    }
}

impl EmaBuilder {
    /// Direct smoothing factor. Must be in (0, 1) exclusive.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(crate::math::EwWeight::Alpha(alpha));
        self
    }

    /// Samples for weight to decay by half. Must be positive and finite.
    ///
    /// Computes: `alpha = 1 - exp(-ln(2) / halflife)`
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(crate::math::EwWeight::Halflife(halflife));
        self
    }

    /// Span in samples (the pandas `span` convention). Must be at least 2.
    ///
    /// Computes: `alpha = 2 / (n + 1)`
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(crate::math::EwWeight::Span(n));
        self
    }

    /// Minimum samples before value is considered valid. Default: 1.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Pre-loads the smoothed value from calibration data.
    ///
    /// When seeded, `is_primed()` returns true immediately (`min_samples`
    /// no longer applies), the first `update()` applies smoothing (no raw
    /// initialization), and `reset()` returns to the seed.
    #[inline]
    #[must_use]
    pub fn seed(mut self, value: f64) -> Self {
        self.seed = Some(value);
        self
    }

    /// Builds the EMA.
    ///
    /// # Errors
    ///
    /// - `Missing("alpha")` if none of `alpha`, `halflife`, `span` was set.
    /// - `Invalid` if `alpha` is outside (0, 1), `halflife` is not positive
    ///   and finite, or `span` is below 2; the message names the knob set.
    /// - `Invalid` if `min_samples` is 0 or the seed is not finite.
    #[inline]
    pub fn build(self) -> Result<Ema, crate::ConfigError> {
        let alpha = self
            .weight
            .ok_or(crate::ConfigError::Missing("alpha"))?
            .resolve()?;
        if self.min_samples == 0 {
            return Err(crate::ConfigError::Invalid("EMA min_samples must be >= 1"));
        }
        if self.seed.is_some_and(|s| !s.is_finite()) {
            return Err(crate::ConfigError::Invalid("EMA seed must be finite"));
        }

        let start = self.seed.unwrap_or(0.0);
        Ok(Ema {
            alpha,
            one_minus_alpha: 1.0 - alpha,
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
    fn update_follows_the_recurrence_exactly() {
        // alpha 0.25: 8, then 8 + 0.25*(16-8) = 10, then 10 + 0.25*(2-10) = 8.
        let mut ema = Ema::builder().alpha(0.25).build().unwrap();
        assert_eq!(ema.update(8.0).unwrap(), Some(8.0));
        assert_eq!(ema.update(16.0).unwrap(), Some(10.0));
        assert_eq!(ema.update(2.0).unwrap(), Some(8.0));
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn seed_is_a_value_not_samples() {
        let mut ema = Ema::builder()
            .alpha(0.25)
            .min_samples(10)
            .seed(100.0)
            .build()
            .unwrap();
        // Primed by the seed alone; no sample has been counted.
        assert!(ema.is_primed());
        assert_eq!(ema.value(), Some(100.0));
        assert_eq!(ema.count(), 0);
        // The first sample is smoothed into the seed, not substituted for it.
        assert_eq!(ema.update(200.0).unwrap(), Some(125.0));
        assert_eq!(ema.count(), 1);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn reset_returns_to_the_seed() {
        let mut ema = Ema::builder().alpha(0.5).seed(100.0).build().unwrap();
        let _ = ema.update(0.0).unwrap();
        ema.reset();
        assert_eq!(ema.count(), 0);
        assert_eq!(ema.value(), Some(100.0));
        assert_eq!(ema.update(200.0).unwrap(), Some(150.0));
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn unseeded_reset_reinitializes_from_the_next_sample() {
        let mut ema = Ema::builder().alpha(0.5).min_samples(2).build().unwrap();
        let _ = ema.update(10.0).unwrap();
        let _ = ema.update(20.0).unwrap();
        ema.reset();
        assert_eq!(ema.value(), None);
        assert_eq!(ema.update(40.0).unwrap(), None);
        assert_eq!(ema.update(60.0).unwrap(), Some(50.0));
    }

    #[test]
    fn a_bad_knob_is_reported_under_its_own_name() {
        use crate::ConfigError::Invalid;
        let err = |b: EmaBuilder| b.build().unwrap_err();
        assert_eq!(
            err(Ema::builder().alpha(1.0)),
            Invalid("alpha must be in (0, 1)")
        );
        assert_eq!(
            err(Ema::builder().alpha(f64::NAN)),
            Invalid("alpha must be in (0, 1)")
        );
        assert_eq!(
            err(Ema::builder().span(1)),
            Invalid("span must be at least 2")
        );
        assert_eq!(
            err(Ema::builder().span(0)),
            Invalid("span must be at least 2")
        );
        #[cfg(any(feature = "std", feature = "libm"))]
        for h in [0.0, -1.0, f64::NAN, f64::INFINITY] {
            assert_eq!(
                err(Ema::builder().halflife(h)),
                Invalid("halflife must be positive and finite")
            );
        }
        #[cfg(any(feature = "std", feature = "libm"))]
        for h in [1e-3, 1e300] {
            assert_eq!(
                err(Ema::builder().halflife(h)),
                Invalid("halflife is too small or too large for a usable weight")
            );
        }
        assert!(Ema::builder().span(2).build().is_ok());
        assert_eq!(
            err(Ema::builder().span(u64::MAX)),
            Invalid("span is too large for a usable weight")
        );
        assert_eq!(
            err(Ema::builder().alpha(0.5).seed(f64::NAN)),
            Invalid("EMA seed must be finite")
        );
    }

    #[test]
    fn first_sample_initializes() {
        let mut ema = Ema::builder().alpha(0.5).build().unwrap();
        assert_eq!(ema.update(100.0).unwrap(), Some(100.0));
        assert_eq!(ema.value(), Some(100.0));
    }

    #[test]
    fn convergence_toward_constant() {
        let mut ema = Ema::builder().alpha(0.1).build().unwrap();

        // Initialize with 0
        ema.update(0.0).unwrap();

        // Feed constant 100 — should converge
        for _ in 0..1000 {
            ema.update(100.0).unwrap();
        }

        let val = ema.value().unwrap();
        assert!(
            (val - 100.0).abs() < 0.01,
            "EMA should converge to 100, got {val}"
        );
    }

    #[test]
    fn higher_alpha_reacts_faster() {
        let mut fast = Ema::builder().alpha(0.9).build().unwrap();
        let mut slow = Ema::builder().alpha(0.1).build().unwrap();

        fast.update(0.0).unwrap();
        slow.update(0.0).unwrap();

        fast.update(100.0).unwrap();
        slow.update(100.0).unwrap();

        let fast_val = fast.value().unwrap();
        let slow_val = slow.value().unwrap();

        assert!(
            fast_val > slow_val,
            "fast ({fast_val}) should react more than slow ({slow_val})"
        );
    }

    #[test]
    fn priming_behavior() {
        let mut ema = Ema::builder().alpha(0.5).min_samples(5).build().unwrap();

        for i in 1..5 {
            assert_eq!(
                ema.update(100.0).unwrap(),
                None,
                "sample {i} should not be primed"
            );
            assert!(!ema.is_primed());
        }

        assert!(ema.update(100.0).unwrap().is_some());
        assert!(ema.is_primed());
    }

    #[test]
    fn reset_clears_state() {
        let mut ema = Ema::builder().alpha(0.5).build().unwrap();
        ema.update(100.0).unwrap();
        ema.update(200.0).unwrap();

        ema.reset();
        assert_eq!(ema.count(), 0);
        assert_eq!(ema.value(), None);

        // Re-initialize should work
        assert_eq!(ema.update(50.0).unwrap(), Some(50.0));
    }

    #[test]
    fn span_computes_alpha() {
        let ema = Ema::builder().span(19).build().unwrap();
        // alpha = 2 / (19 + 1) = 0.1
        assert!((ema.alpha() - 0.1).abs() < 1e-10);
    }

    #[test]
    fn halflife_computes_alpha() {
        let ema = Ema::builder().halflife(1.0).build().unwrap();
        // halflife=1: alpha = 1 - exp(-ln2) = 1 - 0.5 = 0.5
        assert!((ema.alpha() - 0.5).abs() < 1e-10);
    }

    #[test]
    fn errors_without_alpha() {
        let result = Ema::builder().build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("alpha"))));
    }

    #[test]
    fn errors_on_alpha_zero() {
        let result = Ema::builder().alpha(0.0).build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    #[test]
    fn errors_on_alpha_one() {
        let result = Ema::builder().alpha(1.0).build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    // =========================================================================
    // Reconfigure
    // =========================================================================

    #[test]
    #[allow(clippy::float_cmp)]
    fn float_reconfigure_alpha_preserves_value() {
        let mut ema = Ema::builder().alpha(0.5).build().unwrap();
        ema.update(100.0).unwrap();
        ema.update(200.0).unwrap();
        let val_before = ema.value().unwrap();
        let count_before = ema.count();

        ema.reconfigure_alpha(0.9).unwrap();

        assert!((ema.alpha() - 0.9).abs() < 1e-10);
        assert_eq!(ema.value().unwrap(), val_before);
        assert_eq!(ema.count(), count_before);
    }

    #[test]
    fn float_reconfigure_alpha_validates() {
        let mut ema = Ema::builder().alpha(0.5).build().unwrap();
        assert!(ema.reconfigure_alpha(0.0).is_err());
        assert!(ema.reconfigure_alpha(1.0).is_err());
        assert!(ema.reconfigure_alpha(-0.1).is_err());
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut ema = Ema::builder().alpha(0.5).build().unwrap();
        assert!(matches!(
            ema.update(f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
        assert!(matches!(
            ema.update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        ));
        assert!(matches!(
            ema.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        ));
        // State unchanged — counter should still be 0
        assert_eq!(ema.count(), 0);
    }
}
