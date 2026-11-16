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
    min_samples: u64,
}

/// Builder for [`Ema`].
#[derive(Debug, Clone)]
pub struct EmaBuilder {
    alpha: Option<f64>,
    min_samples: u64,
    seed: Option<f64>,
}

impl Ema {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> EmaBuilder {
        EmaBuilder {
            alpha: None,
            min_samples: 1,
            seed: None,
        }
    }

    /// Feeds a sample. Returns smoothed value once primed.
    ///
    /// First sample initializes the EMA directly (no smoothing).
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<f64>, crate::DataError> {
        check_finite!(sample);
        self.count += 1;

        if self.count == 1 {
            self.value = sample;
        } else {
            self.value = self.alpha.fma(sample, self.one_minus_alpha * self.value);
        }

        if self.count >= self.min_samples {
            Ok(Some(self.value))
        } else {
            Ok(None)
        }
    }

    /// Current smoothed value, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<f64> {
        if self.count >= self.min_samples {
            Some(self.value)
        } else {
            None
        }
    }

    /// The smoothing factor alpha.
    #[inline]
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.alpha
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the EMA has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.value = 0.0;
        self.count = 0;
    }

    /// Updates the smoothing factor without resetting state.
    ///
    /// # Errors
    ///
    /// Alpha must be in (0, 1) exclusive.
    #[inline]
    pub fn reconfigure_alpha(&mut self, alpha: f64) -> Result<(), crate::ConfigError> {
        if !(alpha > 0.0 && alpha < 1.0) {
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
        self.alpha = Some(alpha);
        self
    }

    /// Samples for weight to decay by half.
    ///
    /// Computes: `alpha = 1 - exp(-ln(2) / halflife)`
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        let ln2 = core::f64::consts::LN_2;
        let alpha = 1.0 - crate::math::exp(-ln2 / halflife);
        self.alpha = Some(alpha);
        self
    }

    /// Number of samples for center of mass (pandas convention).
    ///
    /// Computes: `alpha = 2 / (n + 1)`
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        let alpha = 2.0 / (n as f64 + 1.0);
        self.alpha = Some(alpha);
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
    /// When seeded, `is_primed()` returns true immediately and
    /// the first `update()` applies smoothing (no raw initialization).
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
    /// - Alpha must have been set (via `alpha`, `halflife`, or `span`).
    /// - Alpha must be in (0, 1) exclusive.
    #[inline]
    pub fn build(self) -> Result<Ema, crate::ConfigError> {
        let alpha = self.alpha.ok_or(crate::ConfigError::Missing("alpha"))?;
        if !(alpha > 0.0 && alpha < 1.0) {
            return Err(crate::ConfigError::Invalid("EMA alpha must be in (0, 1)"));
        }
        if self.min_samples == 0 {
            return Err(crate::ConfigError::Invalid("EMA min_samples must be >= 1"));
        }
        if self.seed.is_some_and(|s| !s.is_finite()) {
            return Err(crate::ConfigError::Invalid("EMA seed must be finite"));
        }

        let (value, count) = self
            .seed
            .map_or((0.0, 0), |seed_val| (seed_val, self.min_samples));

        Ok(Ema {
            alpha,
            one_minus_alpha: 1.0 - alpha,
            value,
            count,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
