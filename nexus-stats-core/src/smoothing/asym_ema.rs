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
    value: f64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`AsymEma`].
#[derive(Debug, Clone)]
pub struct AsymEmaBuilder {
    alpha_up: Option<crate::math::EwWeight>,
    alpha_down: Option<crate::math::EwWeight>,
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
            // One select of the weight, then the incremental form
            // `value += alpha * (sample - value)`.
            let alpha = if sample > self.value {
                self.alpha_up
            } else {
                self.alpha_down
            };
            self.value = alpha.fma(sample - self.value, self.value);
        }

        Ok(self.value())
    }

    /// Current smoothed value, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<f64> {
        self.is_primed().then_some(self.value)
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
        self.alpha_up = Some(crate::math::EwWeight::Alpha(alpha));
        self
    }

    /// Smoothing factor when sample <= current value.
    #[inline]
    #[must_use]
    pub fn alpha_down(mut self, alpha: f64) -> Self {
        self.alpha_down = Some(crate::math::EwWeight::Alpha(alpha));
        self
    }

    /// Span for rising smoothing (alpha_up = 2/(n+1)). Must be at least 2.
    #[inline]
    #[must_use]
    pub fn span_up(mut self, n: u64) -> Self {
        self.alpha_up = Some(crate::math::EwWeight::Span(n));
        self
    }

    /// Span for falling smoothing (alpha_down = 2/(n+1)). Must be at least 2.
    #[inline]
    #[must_use]
    pub fn span_down(mut self, n: u64) -> Self {
        self.alpha_down = Some(crate::math::EwWeight::Span(n));
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
    /// - `Missing` if the rising or the falling weight was not set.
    /// - `Invalid` if an alpha is outside (0, 1) or a span is below 2.
    /// - `Invalid` if `min_samples` is 0.
    #[inline]
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

        Ok(AsymEma {
            alpha_up,
            alpha_down,
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
    #[allow(clippy::float_cmp)]
    fn each_direction_uses_its_own_weight() {
        let mut ema = AsymEma::builder()
            .alpha_up(0.5)
            .alpha_down(0.25)
            .build()
            .unwrap();
        assert_eq!(ema.update(8.0).unwrap(), Some(8.0));
        // Rising: 8 + 0.5 * (16 - 8).
        assert_eq!(ema.update(16.0).unwrap(), Some(12.0));
        // Falling: 12 + 0.25 * (4 - 12).
        assert_eq!(ema.update(4.0).unwrap(), Some(10.0));
        // Equal to the value counts as not rising; either weight leaves it.
        assert_eq!(ema.update(10.0).unwrap(), Some(10.0));
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
