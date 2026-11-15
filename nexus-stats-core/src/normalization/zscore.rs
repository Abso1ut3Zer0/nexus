use core::marker::PhantomData;

use crate::Float;
use crate::statistics::EwmaVar;

/// Relative floor under which a standard deviation counts as zero. FMA with
/// a non-exact alpha leaves tiny non-zero variance on constant input; the
/// statistics run in `f64`, so one floor serves every `T`.
const SD_FLOOR: f64 = 1e-14;

/// Z-score normalizer backed by EWMA variance.
///
/// Returns `(sample - mean) / std_dev` using exponentially weighted
/// estimates of mean and standard deviation. Useful for online feature
/// normalization before feeding into adaptive filters or learners.
///
/// `T` is the sample type at the boundary, `f64` or `f32`; the mean and
/// variance accumulate in `f64` either way, so `ZScoreNorm<f32>` is for
/// producing `f32` features, not for saving precision.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::normalization::ZScoreNorm;
///
/// let mut zs = ZScoreNorm::<f64>::builder().span(20).build().unwrap();
/// for i in 0..100 {
///     let _ = zs.update(100.0 + f64::from(i));
/// }
/// let z = zs.update(150.0).unwrap();
/// assert!(z.is_some());
/// ```
#[derive(Debug, Clone)]
pub struct ZScoreNorm<T: Float> {
    inner: EwmaVar,
    _sample: PhantomData<T>,
}

/// Builder for [`ZScoreNorm`].
#[derive(Debug, Clone)]
pub struct ZScoreNormBuilder<T: Float> {
    alpha: Option<f64>,
    min_samples: u64,
    seed_mean: Option<f64>,
    seed_variance: Option<f64>,
    _sample: PhantomData<T>,
}

impl<T: Float> ZScoreNorm<T> {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> ZScoreNormBuilder<T> {
        ZScoreNormBuilder {
            alpha: None,
            min_samples: 2,
            seed_mean: None,
            seed_variance: None,
            _sample: PhantomData,
        }
    }

    /// Feeds a sample. Returns the z-score once primed.
    ///
    /// If the standard deviation is zero (constant stream), returns `0.0`.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: T) -> Result<Option<T>, crate::DataError> {
        check_finite!(sample);
        let x = sample.to_f64();
        self.inner.update(x)?;
        Ok(self.compute_zscore(x))
    }

    /// Normalizes an arbitrary value against current statistics
    /// without updating state.
    ///
    /// Returns `None` if not primed.
    #[inline]
    #[must_use]
    pub fn normalize(&self, value: T) -> Option<T> {
        self.compute_zscore(value.to_f64())
    }

    #[inline]
    fn compute_zscore(&self, value: f64) -> Option<T> {
        if !self.inner.is_primed() {
            return None;
        }
        let mean = self.inner.mean()?;
        let sd = self.inner.std_dev()?;
        let floor = mean.abs().max(1.0) * SD_FLOOR;
        let z = if sd > floor { (value - mean) / sd } else { 0.0 };
        Some(T::from_f64(z))
    }

    /// Current smoothed mean, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn mean(&self) -> Option<T> {
        self.inner.mean().map(T::from_f64)
    }

    /// Current exponentially weighted standard deviation, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn std_dev(&self) -> Option<T> {
        self.inner.std_dev().map(T::from_f64)
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.inner.count()
    }

    /// Whether enough samples have been observed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.inner.is_primed()
    }

    /// Resets accumulated state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.inner.reset();
    }
}

impl<T: Float> ZScoreNormBuilder<T> {
    /// Direct smoothing factor. Must be in (0, 1) exclusive.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: T) -> Self {
        self.alpha = Some(alpha.to_f64());
        self
    }

    /// Samples for weight to decay by half.
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: T) -> Self {
        let alpha = 1.0 - crate::math::exp(-core::f64::consts::LN_2 / halflife.to_f64());
        self.alpha = Some(alpha);
        self
    }

    /// Number of samples for center of mass (pandas convention).
    #[inline]
    #[must_use]
    #[allow(clippy::cast_precision_loss)]
    pub fn span(mut self, n: u64) -> Self {
        self.alpha = Some(2.0 / (n as f64 + 1.0));
        self
    }

    /// Minimum samples before values are valid. Default: 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Pre-loads mean and variance from calibration data.
    #[inline]
    #[must_use]
    pub fn seed(mut self, mean: T, variance: T) -> Self {
        self.seed_mean = Some(mean.to_f64());
        self.seed_variance = Some(variance.to_f64());
        self
    }

    /// Builds the z-score normalizer.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if alpha is missing or not in (0, 1).
    pub fn build(self) -> Result<ZScoreNorm<T>, crate::ConfigError> {
        let mut ewma = EwmaVar::builder();
        if let Some(a) = self.alpha {
            ewma = ewma.alpha(a);
        }
        ewma = ewma.min_samples(self.min_samples);
        if let (Some(m), Some(v)) = (self.seed_mean, self.seed_variance) {
            ewma = ewma.seed(m, v);
        }
        Ok(ZScoreNorm {
            inner: ewma.build()?,
            _sample: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shifted_scaled() {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
        for i in 0..500 {
            let _ = zs.update(100.0 + (i % 10) as f64);
        }
        let z = zs.update(105.0).unwrap().unwrap();
        assert!(
            z.abs() < 3.0,
            "z-score of near-mean value should be moderate, got {z}"
        );
    }

    #[test]
    fn warmup_returns_none() {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
        assert!(zs.update(1.0).unwrap().is_none());
        assert!(!zs.is_primed());
    }

    #[test]
    fn normalize_without_update() {
        let mut zs = ZScoreNorm::<f64>::builder()
            .alpha(0.1)
            .seed(100.0, 25.0)
            .build()
            .unwrap();
        let z = zs.normalize(105.0).unwrap();
        assert!((z - 1.0).abs() < 0.01, "expected z ≈ 1.0, got {z}");
        let z2 = zs.update(105.0).unwrap().unwrap();
        assert!(z != z2, "update should change internal state");
    }

    #[test]
    fn zero_variance() {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
        for _ in 0..100 {
            let z = zs.update(42.0).unwrap();
            if let Option::Some(v) = z {
                assert!(
                    v.abs() < 1e-10,
                    "constant stream z-score should be 0.0, got {v}"
                );
            }
        }
    }

    #[test]
    fn rejects_nan_inf() {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
        assert!(zs.update(f64::NAN).is_err());
        assert!(zs.update(f64::INFINITY).is_err());
        assert!(zs.update(f64::NEG_INFINITY).is_err());
        assert_eq!(zs.count(), 0);
    }

    #[test]
    fn reset_clears() {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
        for i in 0..50 {
            let _ = zs.update(i as f64);
        }
        assert!(zs.is_primed());
        zs.reset();
        assert_eq!(zs.count(), 0);
        assert!(!zs.is_primed());
        assert!(zs.mean().is_none());
    }
}
