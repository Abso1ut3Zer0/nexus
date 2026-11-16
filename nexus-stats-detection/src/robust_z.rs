use core::marker::PhantomData;

use nexus_stats_core::Float;
use nexus_stats_core::math::MulAdd;

/// Robust z-score — EMA-based modified z-score with estimator freeze.
///
/// Uses the EMA of absolute deviations (EMA-MAD) instead of standard
/// deviation. More robust to outliers than Welford-based z-scores.
/// Freezes the estimator when the z-score exceeds a reject threshold,
/// preventing outliers from corrupting the baseline.
///
/// Robust z-score: `sqrt(2/π) * (x - ema) / ema_abs_dev`.
///
/// The scale is an EMA of the *mean* absolute deviation about the EMA (there
/// is no sorted window, so no median). For normal data `E|X - μ| = σ·sqrt(2/π)`,
/// so scaling by `sqrt(2/π) ≈ 0.798` makes the score comparable to a standard
/// z-score. (The 0.6745 that goes with a *median* absolute deviation would
/// understate it by 15%.)
///
/// # Use Cases
/// - Outlier detection robust to contamination
/// - Market data quality where outliers are common
/// - Any signal where Welford's variance would be corrupted by spikes
///
/// `T` is the sample type at the boundary, `f64` or `f32`; the baseline and
/// the absolute-deviation scale accumulate in `f64` either way, so
/// `RobustZScore<f32>` is for `f32` feature pipelines, not for saving
/// precision.
///
/// # Examples
///
/// ```
/// use nexus_stats_detection::detection::RobustZScore;
///
/// let mut rz = RobustZScore::<f64>::builder().span(20).reject_threshold(3.5).build().unwrap();
/// for i in 0..50 {
///     let _ = rz.update(100.0 + f64::from(i % 3));
/// }
/// assert!(rz.is_primed());
/// ```
#[derive(Debug, Clone)]
pub struct RobustZScore<T: Float> {
    alpha: f64,
    one_minus_alpha: f64,
    ema: f64,
    ema_abs_dev: f64,
    last_z: f64,
    reject_threshold: f64,
    count: u64,
    min_samples: u64,
    initialized: bool,
    _sample: PhantomData<T>,
}

/// Builder for [`RobustZScore`].
#[derive(Debug, Clone)]
pub struct RobustZScoreBuilder<T: Float> {
    alpha: Option<f64>,
    reject_threshold: Option<f64>,
    min_samples: u64,
    _sample: PhantomData<T>,
}

/// `sqrt(2/π)`: the mean absolute deviation of a normal variable in units of
/// its standard deviation, so `(x - μ) / (MeanAD / sqrt(2/π))` is a z-score.
const MEAN_ABS_DEV_TO_Z: f64 = 0.797_884_560_802_865_4;

impl<T: Float> RobustZScore<T> {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> RobustZScoreBuilder<T> {
        RobustZScoreBuilder {
            alpha: None,
            reject_threshold: None,
            min_samples: 10,
            _sample: PhantomData,
        }
    }

    /// Feeds a sample. Returns the robust z-score once primed. Samples whose
    /// z-score exceeds `reject_threshold` do not move the estimators.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: T) -> Result<Option<T>, nexus_stats_core::DataError> {
        check_finite!(sample);
        let x = sample.to_f64();
        self.count += 1;

        if !self.initialized {
            self.ema = x;
            self.ema_abs_dev = 0.0;
            self.initialized = true;
            self.last_z = 0.0;
            return Ok(self.is_primed().then(|| T::from_f64(0.0)));
        }

        let abs_dev = (x - self.ema).abs();
        self.last_z = if self.ema_abs_dev > 0.0 {
            MEAN_ABS_DEV_TO_Z * (x - self.ema) / self.ema_abs_dev
        } else {
            0.0
        };

        // Only update estimators if not rejected.
        if self.last_z.abs() <= self.reject_threshold {
            self.ema = self.alpha.fma(x, self.one_minus_alpha * self.ema);
            self.ema_abs_dev = self
                .alpha
                .fma(abs_dev, self.one_minus_alpha * self.ema_abs_dev);
        }

        Ok(self.is_primed().then(|| T::from_f64(self.last_z)))
    }

    /// Most recent robust z-score, or `None` until primed.
    #[inline]
    #[must_use]
    pub fn z_score(&self) -> Option<T> {
        self.is_primed().then(|| T::from_f64(self.last_z))
    }

    /// Current baseline (the EMA), or `None` until primed.
    #[inline]
    #[must_use]
    pub fn baseline(&self) -> Option<T> {
        self.is_primed().then(|| T::from_f64(self.ema))
    }

    /// Current smoothed mean absolute deviation about the EMA, or `None`
    /// until primed.
    #[inline]
    #[must_use]
    pub fn mean_abs_dev(&self) -> Option<T> {
        self.is_primed().then(|| T::from_f64(self.ema_abs_dev))
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether `min_samples` have been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets accumulated state. Parameters are kept.
    #[inline]
    pub fn reset(&mut self) {
        self.ema = 0.0;
        self.ema_abs_dev = 0.0;
        self.last_z = 0.0;
        self.count = 0;
        self.initialized = false;
    }
}

impl<T: Float> RobustZScoreBuilder<T> {
    /// Direct smoothing factor in (0, 1).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: T) -> Self {
        self.alpha = Some(alpha.to_f64());
        self
    }

    /// Smoothing span in samples: `alpha = 2 / (n + 1)`.
    #[inline]
    #[must_use]
    #[allow(clippy::cast_precision_loss)]
    pub fn span(mut self, n: u64) -> Self {
        self.alpha = Some(2.0 / (n as f64 + 1.0));
        self
    }

    /// Z-score above which a sample is treated as an outlier and does not
    /// move the estimators.
    #[inline]
    #[must_use]
    pub fn reject_threshold(mut self, z: T) -> Self {
        self.reject_threshold = Some(z.to_f64());
        self
    }

    /// Samples before values are reported. Default 10.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the detector.
    ///
    /// # Errors
    ///
    /// `ConfigError::Missing` if `alpha` (or `span`) or `reject_threshold`
    /// was not set; `ConfigError::Invalid` if alpha is outside (0, 1) or the
    /// threshold is not positive.
    pub fn build(self) -> Result<RobustZScore<T>, nexus_stats_core::ConfigError> {
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        let reject = self
            .reject_threshold
            .ok_or(nexus_stats_core::ConfigError::Missing("reject_threshold"))?;
        if !(alpha > 0.0 && alpha < 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1)",
            ));
        }
        if !nexus_stats_core::math::positive_finite(reject) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "reject_threshold must be positive",
            ));
        }
        Ok(RobustZScore {
            alpha,
            one_minus_alpha: 1.0 - alpha,
            ema: 0.0,
            ema_abs_dev: 0.0,
            last_z: 0.0,
            reject_threshold: reject,
            count: 0,
            min_samples: self.min_samples,
            initialized: false,
            _sample: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stable_signal_low_z() {
        let mut rz = RobustZScore::<f64>::builder()
            .alpha(0.1)
            .reject_threshold(10.0)
            .min_samples(5)
            .build()
            .unwrap();

        for _ in 0..20 {
            let _ = rz.update(100.0);
        }

        let z = rz.z_score().unwrap();
        assert!(
            z.abs() < 0.1,
            "stable signal should have ~zero z-score, got {z}"
        );
    }

    #[test]
    fn outlier_high_z() {
        let mut rz = RobustZScore::<f64>::builder()
            .alpha(0.1)
            .reject_threshold(10.0)
            .min_samples(5)
            .build()
            .unwrap();

        // Build baseline around 100 with small variation
        for i in 0..20 {
            let _ = rz.update(100.0 + (i % 3) as f64);
        }

        // Outlier
        let z = rz.update(200.0).unwrap().unwrap();
        assert!(z.abs() > 3.0, "outlier should have high z-score, got {z}");
    }

    #[test]
    fn estimator_freeze_on_reject() {
        let mut rz = RobustZScore::<f64>::builder()
            .alpha(0.1)
            .reject_threshold(3.0)
            .min_samples(5)
            .build()
            .unwrap();

        for i in 0..20 {
            let _ = rz.update(100.0 + (i % 2) as f64);
        }

        let baseline_before = rz.baseline().unwrap();

        // Feed outlier that exceeds reject threshold
        let _ = rz.update(500.0);

        let baseline_after = rz.baseline().unwrap();
        assert!(
            (baseline_before - baseline_after).abs() < 1e-10,
            "baseline should not move on rejected sample"
        );
    }

    #[test]
    fn recovery_after_freeze() {
        let mut rz = RobustZScore::<f64>::builder()
            .alpha(0.1)
            .reject_threshold(5.0)
            .min_samples(5)
            .build()
            .unwrap();

        for _ in 0..20 {
            let _ = rz.update(100.0);
        }
        let _ = rz.update(500.0); // rejected

        // Normal samples resume — estimator should continue updating
        for _ in 0..10 {
            let _ = rz.update(100.0);
        }

        let z = rz.z_score().unwrap();
        assert!(z.abs() < 1.0, "should recover after freeze, got {z}");
    }

    #[test]
    fn priming() {
        let mut rz = RobustZScore::<f64>::builder()
            .alpha(0.1)
            .reject_threshold(5.0)
            .min_samples(10)
            .build()
            .unwrap();

        for _ in 0..9 {
            assert!(rz.update(100.0).unwrap().is_none());
        }
        assert!(rz.update(100.0).unwrap().is_some());
    }

    #[test]
    fn reset() {
        let mut rz = RobustZScore::<f64>::builder()
            .alpha(0.1)
            .reject_threshold(5.0)
            .min_samples(5)
            .build()
            .unwrap();

        for _ in 0..20 {
            let _ = rz.update(100.0);
        }
        rz.reset();
        assert_eq!(rz.count(), 0);
    }

    #[test]
    fn f32_basic() {
        let mut rz = RobustZScore::<f32>::builder()
            .alpha(0.1)
            .reject_threshold(5.0)
            .min_samples(5)
            .build()
            .unwrap();

        for _ in 0..10 {
            let _ = rz.update(100.0);
        }
        assert!(rz.is_primed());
    }

    #[test]
    fn errors_without_reject_threshold() {
        let result = RobustZScore::<f64>::builder().alpha(0.1).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("reject_threshold"))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut rz = RobustZScore::<f64>::builder()
            .alpha(0.1)
            .reject_threshold(5.0)
            .min_samples(5)
            .build()
            .unwrap();

        assert_eq!(
            rz.update(f64::NAN).unwrap_err(),
            nexus_stats_core::DataError::NotANumber
        );
        assert_eq!(
            rz.update(f64::INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(
            rz.update(f64::NEG_INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(rz.count(), 0);
    }

    /// On normal data the scale must be sqrt(2/π)·σ and the score a z-score:
    /// Irwin-Hall (sum of 12 uniforms minus 6) has mean 0 and variance 1.
    #[test]
    fn scale_and_score_are_calibrated_for_normal_data() {
        let mut rng = 0x9E37_79B9_7F4A_7C15u64;
        let mut uniform = || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            (rng >> 11) as f64 / (1u64 << 53) as f64
        };
        let mut rz = RobustZScore::<f64>::builder()
            .alpha(0.002)
            .reject_threshold(100.0)
            .build()
            .unwrap();
        for _ in 0..200_000 {
            let x: f64 = (0..12).map(|_| uniform()).sum::<f64>() - 6.0;
            rz.update(x).unwrap();
        }
        let scale = rz.mean_abs_dev().unwrap();
        assert!((scale - 0.7979).abs() < 0.03, "mean abs dev {scale}");
        let z = rz.update(3.0).unwrap().unwrap();
        assert!((z - 3.0).abs() < 0.3, "z-score of a 3σ sample: {z}");
    }
}
