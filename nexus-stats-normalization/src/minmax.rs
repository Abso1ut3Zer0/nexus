use core::marker::PhantomData;

use nexus_stats_core::Float;
use nexus_stats_monitoring::{WindowedMax, WindowedMin};

/// Windowed min-max normalizer.
///
/// Scales values to [0, 1] using the windowed minimum and maximum over a
/// sliding timestamp window: `(sample - min) / (max - min)`. When the range
/// is zero (all values equal), returns 0.5.
///
/// The window is tracked by a [`WindowedMin`] and a [`WindowedMax`], three
/// stored samples each, so memory is fixed whatever the window length; see
/// those types for how the window ages and for the timestamp rules. Those
/// trackers are approximate: the reported extremes are always real samples
/// from inside the window, but not always the most extreme ones, so the
/// range used here can be narrower than the true window's, never wider.
///
/// `T` is the sample type at the boundary, `f64` or `f32`; the trackers
/// run in `f64` either way, so `MinMaxNorm<f32>` is for producing `f32`
/// features, not for saving precision.
///
/// # Examples
///
/// ```
/// use nexus_stats_normalization::MinMaxNorm;
///
/// let mut mm = MinMaxNorm::<f32>::builder().window(100).build().unwrap();
/// let _ = mm.update(0, 10.0);
/// let _ = mm.update(1, 20.0);
/// let v = mm.update(2, 15.0).unwrap();
/// assert_eq!(v, Some(0.5));
/// ```
#[derive(Debug, Clone)]
pub struct MinMaxNorm<T: Float> {
    min_tracker: WindowedMin<f64>,
    max_tracker: WindowedMax<f64>,
    _sample: PhantomData<T>,
}

/// Builder for [`MinMaxNorm`].
#[derive(Debug, Clone)]
pub struct MinMaxNormBuilder<T: Float> {
    window: Option<u64>,
    _sample: PhantomData<T>,
}

impl<T: Float> MinMaxNorm<T> {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> MinMaxNormBuilder<T> {
        MinMaxNormBuilder {
            window: None,
            _sample: PhantomData,
        }
    }

    /// Feeds a sample at the given timestamp. Returns normalized value
    /// in [0, 1] once at least one sample has been observed.
    ///
    /// A sample timestamped before the previous one does not enter the
    /// window (see [`WindowedMax`]); it is normalized against the current
    /// window and clamped to [0, 1].
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(
        &mut self,
        timestamp: u64,
        sample: T,
    ) -> Result<Option<T>, nexus_stats_core::DataError> {
        check_finite!(sample);
        let x = sample.to_f64();
        self.min_tracker.update(timestamp, x);
        self.max_tracker.update(timestamp, x);
        // A no-op for a sample that entered the window, which always lies
        // within it; a late sample may not.
        Ok(self
            .compute_normalized(x)
            .map(|v| T::from_f64(v.to_f64().clamp(0.0, 1.0))))
    }

    /// Normalizes an arbitrary value against current windowed min/max
    /// without updating state. Not clamped: a value outside the tracked
    /// range maps below 0 or above 1. [`update`](Self::update) differs: it
    /// widens the range to include its sample first (or clamps a late
    /// sample, which does not enter the window), so it never reads outside
    /// [0, 1].
    ///
    /// Returns `Ok(None)` if not primed.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the value is NaN, or
    /// `DataError::Infinite` if the value is infinite.
    #[inline]
    pub fn normalize(&self, value: T) -> Result<Option<T>, nexus_stats_core::DataError> {
        check_finite!(value);
        Ok(self.compute_normalized(value.to_f64()))
    }

    #[inline]
    fn compute_normalized(&self, value: f64) -> Option<T> {
        let min = self.min_tracker.min()?;
        let max = self.max_tracker.max()?;
        let range = max - min;
        let out = if range > 0.0 {
            (value - min) / range
        } else {
            0.5
        };
        Some(T::from_f64(out))
    }

    /// Current windowed minimum, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn min(&self) -> Option<T> {
        self.min_tracker.min().map(T::from_f64)
    }

    /// Current windowed maximum, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn max(&self) -> Option<T> {
        self.max_tracker.max().map(T::from_f64)
    }

    /// Current range (max - min), or `None` if empty.
    #[inline]
    #[must_use]
    pub fn range(&self) -> Option<T> {
        let min = self.min_tracker.min()?;
        let max = self.max_tracker.max()?;
        Some(T::from_f64(max - min))
    }

    /// Number of samples accepted into the window since construction or
    /// `reset`. The two trackers are fed together and always agree.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.min_tracker.count()
    }

    /// Whether at least one sample has been observed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count() > 0
    }

    /// Resets accumulated state. Window size preserved.
    #[inline]
    pub fn reset(&mut self) {
        self.min_tracker.reset();
        self.max_tracker.reset();
    }
}

impl<T: Float> MinMaxNormBuilder<T> {
    /// Timestamp window size (required, must be positive).
    #[inline]
    #[must_use]
    pub fn window(mut self, window: u64) -> Self {
        self.window = Some(window);
        self
    }

    /// Builds the min-max normalizer.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if the window is missing, zero, or 2^63 ticks or more.
    #[inline]
    pub fn build(self) -> Result<MinMaxNorm<T>, nexus_stats_core::ConfigError> {
        let window = self
            .window
            .ok_or(nexus_stats_core::ConfigError::Missing("window"))?;
        Ok(MinMaxNorm {
            min_tracker: WindowedMin::new(window)?,
            max_tracker: WindowedMax::new(window)?,
            _sample: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scales_to_unit() {
        let mut mm = MinMaxNorm::<f64>::builder().window(1000).build().unwrap();
        let _ = mm.update(0, 10.0).unwrap();
        let _ = mm.update(1, 20.0).unwrap();
        let v = mm.update(2, 30.0).unwrap().unwrap();
        assert!((v - 1.0).abs() < 1e-10, "30 should map to 1.0, got {v}");
        assert_eq!(mm.normalize(20.0).unwrap(), Some(0.5));
    }

    #[test]
    fn windowed_eviction() {
        let mut mm = MinMaxNorm::<f64>::builder().window(30).build().unwrap();
        // Wide range initially
        let _ = mm.update(0, 0.0).unwrap();
        let _ = mm.update(1, 100.0).unwrap();
        let v1 = mm.update(2, 50.0).unwrap().unwrap();
        assert!(
            (v1 - 0.5).abs() < 1e-10,
            "50 in [0,100] should be 0.5, got {v1}"
        );
        // Feed narrow-range values after old extrema expire
        for t in 35..60 {
            let _ = mm.update(t, 40.0 + (t % 10) as f64).unwrap();
        }
        let range = mm.range().unwrap();
        assert!(
            range < 50.0,
            "range should have narrowed after window eviction, got {range}"
        );
    }

    #[test]
    fn constant_returns_half() {
        let mut mm = MinMaxNorm::<f64>::builder().window(100).build().unwrap();
        for i in 0..20u64 {
            let v = mm.update(i, 42.0).unwrap().unwrap();
            assert!(
                (v - 0.5).abs() < 1e-10,
                "constant stream should return 0.5, got {v}"
            );
        }
    }

    #[test]
    fn normalize_without_update() {
        let mut mm = MinMaxNorm::<f64>::builder().window(100).build().unwrap();
        let _ = mm.update(0, 0.0).unwrap();
        let _ = mm.update(1, 100.0).unwrap();
        assert_eq!(mm.normalize(75.0).unwrap(), Some(0.75));
        // Not clamped: outside the window's range reads outside [0, 1].
        assert_eq!(mm.normalize(150.0).unwrap(), Some(1.5));
        assert_eq!(mm.normalize(-50.0).unwrap(), Some(-0.5));
        assert_eq!(mm.count(), 2);
    }

    #[test]
    fn normalize_before_any_sample_is_none() {
        let mm = MinMaxNorm::<f64>::builder().window(100).build().unwrap();
        assert_eq!(mm.normalize(1.0).unwrap(), None);
        assert!(!mm.is_primed());
    }

    #[test]
    fn single_sample() {
        let mut mm = MinMaxNorm::<f64>::builder().window(100).build().unwrap();
        let v = mm.update(0, 42.0).unwrap().unwrap();
        assert!(
            (v - 0.5).abs() < 1e-10,
            "single sample: range=0 -> 0.5, got {v}"
        );
    }

    #[test]
    fn rejects_nan_inf() {
        let mut mm = MinMaxNorm::<f64>::builder().window(100).build().unwrap();
        assert!(mm.update(0, f64::NAN).is_err());
        assert!(mm.update(0, f64::INFINITY).is_err());
        assert!(mm.update(0, f64::NEG_INFINITY).is_err());
        assert_eq!(
            mm.normalize(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            mm.normalize(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(mm.count(), 0);
    }

    // A late sample does not move the window. Before, it reset both trackers
    // to itself (0.5 here) and the next in-order sample read 0.0.
    #[test]
    fn late_sample_is_clamped_and_leaves_the_window() {
        let mut mm = MinMaxNorm::<f64>::builder().window(100).build().unwrap();
        let _ = mm.update(1000, 10.0).unwrap();
        let _ = mm.update(1030, 20.0).unwrap();
        assert_eq!(mm.update(1020, 30.0).unwrap(), Some(1.0));
        assert_eq!(mm.update(1020, 0.0).unwrap(), Some(0.0));
        assert_eq!(mm.update(1020, 15.0).unwrap(), Some(0.5));
        assert_eq!(
            (mm.min(), mm.max(), mm.count()),
            (Some(10.0), Some(20.0), 2)
        );
        assert_eq!(mm.update(1031, 15.0).unwrap(), Some(0.5));

        let mut m32 = MinMaxNorm::<f32>::builder().window(100).build().unwrap();
        let _ = m32.update(1000, 10.0).unwrap();
        let _ = m32.update(1030, 20.0).unwrap();
        assert_eq!(m32.update(1020, 30.0).unwrap(), Some(1.0));
        assert_eq!(m32.update(1020, 0.0).unwrap(), Some(0.0));
    }
}
