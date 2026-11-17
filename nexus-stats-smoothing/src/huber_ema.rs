//! Huber EMA — outlier-robust exponential moving average.

/// Huber EMA — EMA with bounded step size per observation.
///
/// When `|x - current| <= delta`, behaves as a standard EMA.
/// When the deviation exceeds delta, the step is capped at
/// `alpha * delta`, preventing outliers from yanking the estimate.
///
/// # Use Cases
///
/// - Spread smoothing where occasional tick spikes shouldn't move the estimate
/// - Any streaming signal with fat-tailed noise
#[derive(Debug, Clone)]
pub struct HuberEma {
    alpha: f64,
    delta: f64,
    value: f64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`HuberEma`].
#[derive(Debug, Clone)]
pub struct HuberEmaBuilder {
    alpha: Option<f64>,
    delta: Option<f64>,
    min_samples: u64,
    seed: Option<f64>,
}

impl HuberEma {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> HuberEmaBuilder {
        HuberEmaBuilder {
            alpha: None,
            delta: None,
            min_samples: 1,
            seed: None,
        }
    }

    /// Feed a sample. First sample initializes directly.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if NaN, `DataError::Infinite` if infinite.
    #[inline]
    pub fn update(&mut self, x: f64) -> Result<Option<f64>, nexus_stats_core::DataError> {
        check_finite!(x);
        self.count += 1;

        if self.count == 1 {
            self.value = x;
        } else {
            let diff = x - self.value;
            let step = if diff.abs() <= self.delta {
                self.alpha * diff
            } else {
                self.alpha * self.delta * diff.signum()
            };
            self.value += step;
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

    /// The Huber threshold delta.
    #[inline]
    #[must_use]
    pub fn delta(&self) -> f64 {
        self.delta
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

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.value = 0.0;
        self.count = 0;
    }
}

impl HuberEmaBuilder {
    /// Direct smoothing factor. Must be in (0, 1).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Samples for weight to decay by half.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: f64) -> Self {
        let alpha = nexus_stats_core::math::alpha_from_halflife(halflife);
        self.alpha = Some(alpha);
        self
    }

    /// Maximum influence per observation. When `|x - current| > delta`,
    /// the step is capped at `alpha * delta`.
    #[inline]
    #[must_use]
    pub fn delta(mut self, delta: f64) -> Self {
        self.delta = Some(delta);
        self
    }

    /// Minimum samples before reporting a value. Default: 1.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, n: u64) -> Self {
        self.min_samples = n;
        self
    }

    /// Seed the initial value instead of using the first sample.
    #[inline]
    #[must_use]
    pub fn seed(mut self, value: f64) -> Self {
        self.seed = Some(value);
        self
    }

    /// Build the HuberEma.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if alpha or delta are not set or invalid.
    #[inline]
    pub fn build(self) -> Result<HuberEma, nexus_stats_core::ConfigError> {
        if self.min_samples == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "min_samples must be >= 1",
            ));
        }
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        if !nexus_stats_core::math::in_unit_interval(alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1)",
            ));
        }
        let delta = self
            .delta
            .ok_or(nexus_stats_core::ConfigError::Missing("delta"))?;
        if delta <= 0.0 || !delta.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "delta must be positive",
            ));
        }

        let (value, count) = self.seed.map_or((0.0, 0), |v| (v, 1));

        Ok(HuberEma {
            alpha,
            delta,
            value,
            count,
            min_samples: self.min_samples,
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
            h.update(v).unwrap();
        }
        let val = h.value().unwrap();
        assert!((val - 10.0).abs() < 1.0, "value={val}, expected ~10.0");
    }

    #[test]
    fn spike_is_capped() {
        let mut h = basic_huber();
        // Converge to ~10
        for _ in 0..50 {
            h.update(10.0).unwrap();
        }
        let before = h.value().unwrap();

        // Huge spike — step should be capped at alpha * delta = 0.1 * 5 = 0.5
        h.update(1000.0).unwrap();
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
            h.update(10.0).unwrap();
        }
        // Shift to 20 — bounded steps, but should eventually converge
        for _ in 0..500 {
            h.update(20.0).unwrap();
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
            h.update(v).unwrap();
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
            h.update(100.0).unwrap();
        }
        h.reset();
        assert_eq!(h.count(), 0);
        assert!(!h.is_primed());
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut h = basic_huber();
        h.update(10.0).unwrap();
        assert!(matches!(
            h.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        assert!(matches!(
            h.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert!(matches!(
            h.update(f64::NEG_INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert_eq!(h.count(), 1, "rejected samples leave the state untouched");
    }
}
