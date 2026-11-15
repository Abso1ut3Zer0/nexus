use crate::math::MulAdd;

/// Asymmetric EMA — different smoothing factors for rising vs falling.
///
/// Uses `alpha_up` when the new sample exceeds the current value,
/// `alpha_down` when it's below. This allows fast attack / slow decay
/// or vice versa.
///
/// # Use Cases
/// - Fast attack / slow decay for peak tracking
/// - Slow attack / fast decay for trough tracking
/// - Asymmetric noise filtering
#[derive(Debug, Clone)]
pub struct AsymEma {
    alpha_up: f64,
    alpha_down: f64,
    // Precomputed `1.0 - alpha_*` for the `update` hot path; saves a
    // subtraction per sample at the cost of two f64 fields per
    // instance. Set in `build()` and held constant for the
    // instance's lifetime.
    one_minus_alpha_up: f64,
    one_minus_alpha_down: f64,
    value: f64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`AsymEma`].
#[derive(Debug, Clone)]
pub struct AsymEmaBuilder {
    alpha_up: Option<f64>,
    alpha_down: Option<f64>,
    min_samples: u64,
}

impl AsymEma {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> AsymEmaBuilder {
        AsymEmaBuilder {
            alpha_up: None,
            alpha_down: None,
            min_samples: 1,
        }
    }

    /// Feeds a sample. Returns smoothed value once primed.
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
            let (alpha, one_minus) = if sample > self.value {
                (self.alpha_up, self.one_minus_alpha_up)
            } else {
                (self.alpha_down, self.one_minus_alpha_down)
            };
            self.value = alpha.fma(sample, one_minus * self.value);
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

impl AsymEmaBuilder {
    /// Smoothing factor when sample > current value.
    #[inline]
    #[must_use]
    pub fn alpha_up(mut self, alpha: f64) -> Self {
        self.alpha_up = Some(alpha);
        self
    }

    /// Smoothing factor when sample <= current value.
    #[inline]
    #[must_use]
    pub fn alpha_down(mut self, alpha: f64) -> Self {
        self.alpha_down = Some(alpha);
        self
    }

    /// Span for rising smoothing (alpha_up = 2/(n+1)).
    #[inline]
    #[must_use]
    pub fn span_up(mut self, n: u64) -> Self {
        self.alpha_up = Some(2.0 / (n as f64 + 1.0));
        self
    }

    /// Span for falling smoothing (alpha_down = 2/(n+1)).
    #[inline]
    #[must_use]
    pub fn span_down(mut self, n: u64) -> Self {
        self.alpha_down = Some(2.0 / (n as f64 + 1.0));
        self
    }

    /// Minimum samples before value is valid. Default: 1.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the asymmetric EMA.
    ///
    /// # Errors
    ///
    /// - Both alpha_up and alpha_down must have been set.
    /// - Both must be in (0, 1) exclusive.
    #[inline]
    pub fn build(self) -> Result<AsymEma, crate::ConfigError> {
        let alpha_up = self
            .alpha_up
            .ok_or(crate::ConfigError::Missing("alpha_up"))?;
        let alpha_down = self
            .alpha_down
            .ok_or(crate::ConfigError::Missing("alpha_down"))?;
        if !(alpha_up > 0.0 && alpha_up < 1.0) {
            return Err(crate::ConfigError::Invalid("alpha_up must be in (0, 1)"));
        }
        if !(alpha_down > 0.0 && alpha_down < 1.0) {
            return Err(crate::ConfigError::Invalid("alpha_down must be in (0, 1)"));
        }

        Ok(AsymEma {
            alpha_up,
            alpha_down,
            one_minus_alpha_up: 1.0 - alpha_up,
            one_minus_alpha_down: 1.0 - alpha_down,
            value: 0.0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fast_attack_slow_decay() {
        let mut ema = AsymEma::builder()
            .alpha_up(0.9) // fast attack
            .alpha_down(0.1) // slow decay
            .build()
            .unwrap();

        ema.update(0.0).unwrap(); // initialize
        ema.update(100.0).unwrap(); // fast attack
        let after_attack = ema.value().unwrap();

        ema.update(0.0).unwrap(); // slow decay
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

        fast_up.update(50.0).unwrap();
        fast_down.update(50.0).unwrap();

        fast_up.update(100.0).unwrap();
        fast_down.update(100.0).unwrap();

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
            assert!(ema.update(100.0).unwrap().is_none());
        }
        assert!(ema.update(100.0).unwrap().is_some());
    }

    #[test]
    fn reset() {
        let mut ema = AsymEma::builder()
            .alpha_up(0.5)
            .alpha_down(0.5)
            .build()
            .unwrap();
        ema.update(100.0).unwrap();
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

    #[test]
    fn rejects_nan_and_inf() {
        let mut ema = AsymEma::builder()
            .alpha_up(0.5)
            .alpha_down(0.3)
            .build()
            .unwrap();
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
        assert_eq!(ema.count(), 0);
    }
}
