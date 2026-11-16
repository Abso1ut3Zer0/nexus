use nexus_stats_core::storage::Ring;

use nexus_stats_core::Direction;

/// MOSUM: Moving Sum change detector.
///
/// Windowed complement to CUSUM. Detects transient shifts (spikes) rather
/// than persistent ones: a ring holds the deviations `sample - target` of the
/// last `window` samples, and the detector reports `Rising` or `Falling` when
/// their sum crosses `±threshold`, `Neutral` otherwise. A transient that
/// leaves the window stops counting.
///
/// O(1) per update. The ring (a [`Ring<f64>`], one slot per window sample) is
/// allocated once in `build()`; nothing allocates after construction. Requires
/// the `alloc` feature.
#[derive(Clone)]
pub struct Mosum {
    target: f64,
    threshold: f64,
    ring: Ring<f64>,
    sum: f64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`Mosum`].
#[derive(Debug, Clone)]
pub struct MosumBuilder {
    target: f64,
    window: Option<usize>,
    threshold: Option<f64>,
    min_samples: Option<u64>,
}

impl Mosum {
    /// Creates a builder with the target (expected baseline mean).
    #[inline]
    #[must_use]
    pub fn builder(target: f64) -> MosumBuilder {
        MosumBuilder {
            target,
            window: None,
            threshold: None,
            min_samples: None,
        }
    }

    /// Feeds a sample. Returns the shift direction once primed.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(
        &mut self,
        sample: f64,
    ) -> Result<Option<Direction>, nexus_stats_core::DataError> {
        check_finite!(sample);
        let deviation = sample - self.target;
        // The evicted deviation leaves the sum. While the ring is filling the
        // slot holds the 0.0 fill, which leaves the sum unchanged.
        let evicted = self.ring.replace(deviation);
        self.sum = self.sum - evicted + deviation;
        self.count += 1;

        if self.count < self.min_samples {
            return Ok(None);
        }
        Ok(Some(if self.sum > self.threshold {
            Direction::Rising
        } else if self.sum < -self.threshold {
            Direction::Falling
        } else {
            Direction::Neutral
        }))
    }

    /// Current moving sum of deviations.
    #[inline]
    #[must_use]
    pub fn sum(&self) -> f64 {
        self.sum
    }

    /// Window size.
    #[inline]
    #[must_use]
    pub fn window_size(&self) -> usize {
        self.ring.capacity()
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether `min_samples` have been seen and detection is active.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to the empty state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.ring.clear(0.0);
        self.sum = 0.0;
        self.count = 0;
    }
}

impl core::fmt::Debug for Mosum {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Mosum")
            .field("window", &self.ring.capacity())
            .field("count", &self.count)
            .field("sum", &self.sum)
            .finish()
    }
}

impl MosumBuilder {
    /// Window size (number of samples in the ring). Required.
    #[inline]
    #[must_use]
    pub fn window_size(mut self, n: usize) -> Self {
        self.window = Some(n);
        self
    }

    /// Decision threshold on the moving sum. Required, positive.
    #[inline]
    #[must_use]
    pub fn threshold(mut self, threshold: f64) -> Self {
        self.threshold = Some(threshold);
        self
    }

    /// Minimum samples before detection activates. Default: window size.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = Some(min);
        self
    }

    /// Builds the MOSUM detector.
    ///
    /// # Errors
    ///
    /// `ConfigError::Missing` if the window or threshold is unset;
    /// `ConfigError::Invalid` for a zero window, a non-finite target or a
    /// threshold that is not positive and finite.
    pub fn build(self) -> Result<Mosum, nexus_stats_core::ConfigError> {
        let window = self
            .window
            .ok_or(nexus_stats_core::ConfigError::Missing("window_size"))?;
        if window == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "window_size must be > 0",
            ));
        }
        let threshold = self
            .threshold
            .ok_or(nexus_stats_core::ConfigError::Missing("threshold"))?;
        if !self.target.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "target must be finite",
            ));
        }
        if !nexus_stats_core::math::positive_finite(threshold) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "threshold must be positive",
            ));
        }
        Ok(Mosum {
            target: self.target,
            threshold,
            ring: Ring::new(window, 0.0)?,
            sum: 0.0,
            count: 0,
            min_samples: self.min_samples.unwrap_or(window as u64),
        })
    }
}
#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    #[test]
    fn no_detection_at_target() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(10)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..10 {
            let _ = mosum.update(100.0);
        }
        for _ in 0..100 {
            assert_eq!(mosum.update(100.0).unwrap(), Some(Direction::Neutral));
        }
    }

    #[test]
    fn detects_upward_spike() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(10)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..10 {
            let _ = mosum.update(100.0);
        }

        let mut triggered = false;
        for _ in 0..10 {
            if mosum.update(110.0).unwrap() == Some(Direction::Rising) {
                triggered = true;
                break;
            }
        }
        assert!(triggered, "should detect upward spike");
    }

    #[test]
    fn transient_clears_after_window() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(5)
            .threshold(40.0)
            .build()
            .unwrap();

        for _ in 0..5 {
            let _ = mosum.update(100.0);
        }
        for _ in 0..5 {
            let _ = mosum.update(120.0);
        }
        for _ in 0..5 {
            let _ = mosum.update(100.0);
        }
        assert!(
            mosum.sum().abs() < 1e-10,
            "sum should return to ~0, got {}",
            mosum.sum()
        );
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn reset_clears_state() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(10)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..20 {
            let _ = mosum.update(120.0);
        }
        mosum.reset();
        assert_eq!(mosum.count(), 0);
        assert_eq!(mosum.sum(), 0.0);
    }

    #[test]
    fn clone_works() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(5)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..5 {
            let _ = mosum.update(110.0);
        }

        let cloned = mosum.clone();
        assert_eq!(cloned.count(), mosum.count());
        assert_eq!(cloned.sum(), mosum.sum());
    }

    #[test]
    fn errors_without_threshold() {
        let result = Mosum::builder(100.0).window_size(10).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("threshold"))
        ));
    }

    #[test]
    fn errors_without_window() {
        let result = Mosum::builder(100.0).threshold(50.0).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("window_size"))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(10)
            .threshold(50.0)
            .build()
            .unwrap();

        assert_eq!(
            mosum.update(f64::NAN).unwrap_err(),
            nexus_stats_core::DataError::NotANumber
        );
        assert_eq!(
            mosum.update(f64::INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(
            mosum.update(f64::NEG_INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(mosum.count(), 0);
    }
}
