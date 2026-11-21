use core::marker::PhantomData;

use crate::Float;
use crate::statistics::EwmVar;

/// Relative floor under which a standard deviation, or a deviation from the
/// mean of a constant stream, counts as zero. FMA with a non-exact alpha
/// leaves tiny non-zero variance (and a mean a few ulps off) on constant
/// input; the statistics run in `f64`, so one floor serves every `T`.
const SD_FLOOR: f64 = 1e-14;

/// Z-score normalizer backed by EWMA variance.
///
/// Returns `(sample - mean) / std_dev` using exponentially weighted
/// estimates of the mean and standard deviation of the samples seen before
/// it. Use it to put streams with different scales on a common one, and as
/// an outlier score. Against a constant stream, which has no scale, a
/// different value scores `+inf` or `-inf`; see
/// [`update`](ZScoreNorm::update).
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
///     let _ = zs.update(100.0 + f64::from(i % 5));
/// }
/// // In-range samples score small; an outlier is not capped.
/// assert!(zs.normalize(102.0).unwrap().unwrap().abs() < 1.0);
/// assert!(zs.update(1_000.0).unwrap().unwrap() > 100.0);
/// ```
#[derive(Debug, Clone)]
pub struct ZScoreNorm<T: Float> {
    inner: EwmVar,
    _sample: PhantomData<T>,
}

/// Builder for [`ZScoreNorm`].
#[derive(Debug, Clone)]
pub struct ZScoreNormBuilder<T: Float> {
    weight: Option<crate::math::EwWeight>,
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
            weight: None,
            min_samples: 2,
            seed_mean: None,
            seed_variance: None,
            _sample: PhantomData,
        }
    }

    /// Scores a sample against the statistics of the samples before it,
    /// then folds it in.
    ///
    /// Scoring first is what lets an outlier read as one: a sample folded
    /// into the mean and variance before being scored against them can
    /// never exceed `sqrt((1 - alpha) / alpha)`, whatever its size.
    ///
    /// Returns `Ok(None)` until `min_samples` earlier samples have been seen
    /// (or a seed supplied); the sample is folded in either way. Equivalent
    /// to [`normalize`](Self::normalize) followed by the fold.
    ///
    /// # Zero scale
    ///
    /// The standard deviation counts as zero below
    /// `max(|mean|, 1.0) * 1e-14`. That is the case while every sample so
    /// far has been the same value, after a long enough flat stretch for the
    /// exponentially weighted variance to decay there, and for a seed with
    /// zero variance. The score then follows the usual numerical convention
    /// for division by zero: `+inf` for a sample above the mean and `-inf`
    /// for one below, so a threshold test such as `z > 4.0` fires on a jump
    /// out of a flat stream and `z.clamp(lo, hi)` bounds it. A sample on
    /// the mean (within the same floor) scores `0.0`.
    ///
    /// The samples after such a jump are scored against statistics the jump
    /// itself created: a second sample at the new level scores exactly
    /// `sqrt((1 - alpha) / alpha)`, whatever the size of the jump.
    ///
    /// An infinite score is not valid input to the other types in this
    /// crate, which reject it; clamp it before feeding it on.
    /// `ZScoreNorm<f32>` also returns infinity for a finite score too large
    /// for `f32`. As everywhere in this crate, inputs large enough to
    /// overflow the accumulated variance (around `1e154` and beyond) are
    /// outside the supported range, and can score NaN.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: T) -> Result<Option<T>, crate::DataError> {
        check_finite!(sample);
        let x = sample.to_f64();
        let z = self.score(x);
        self.inner.update(x);
        Ok(z)
    }

    /// Scores an arbitrary value against the current mean and standard
    /// deviation without updating state.
    ///
    /// Returns `Ok(None)` if not primed. With a zero standard deviation the
    /// score is `0.0`, `+inf` or `-inf` as described on
    /// [`update`](Self::update).
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the value is NaN, or
    /// `DataError::Infinite` if the value is infinite.
    #[inline]
    pub fn normalize(&self, value: T) -> Result<Option<T>, crate::DataError> {
        check_finite!(value);
        Ok(self.score(value.to_f64()))
    }

    #[inline]
    fn score(&self, value: f64) -> Option<T> {
        let reading = self.inner.value()?;
        let mean = reading.mean;
        let sd = reading.std_dev();
        let floor = mean.abs().max(1.0) * SD_FLOOR;
        let deviation = value - mean;
        let z = if sd > floor {
            deviation / sd
        } else if deviation.abs() <= floor {
            // On the constant itself: zero at every positive scale.
            0.0
        } else {
            f64::INFINITY.copysign(deviation)
        };
        Some(T::from_f64(z))
    }

    /// Current smoothed mean, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn mean(&self) -> Option<T> {
        self.inner.value().map(|reading| T::from_f64(reading.mean))
    }

    /// Current exponentially weighted standard deviation, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn std_dev(&self) -> Option<T> {
        self.inner
            .value()
            .map(|reading| T::from_f64(reading.std_dev()))
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
        self.weight = Some(crate::math::EwWeight::Alpha(alpha.to_f64()));
        self
    }

    /// Samples for weight to decay by half. Must be positive and finite.
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: T) -> Self {
        self.weight = Some(crate::math::EwWeight::Halflife(halflife.to_f64()));
        self
    }

    /// Span in samples (the pandas `span` convention, `alpha = 2 / (n + 1)`).
    /// Must be at least 2.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(crate::math::EwWeight::Span(n));
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
    /// - `Missing("alpha")` if none of `alpha`, `halflife`, `span` was set.
    /// - `Invalid` if `alpha` is outside (0, 1), `halflife` is not positive
    ///   and finite, or `span` is below 2; the message names the knob set.
    #[inline]
    pub fn build(self) -> Result<ZScoreNorm<T>, crate::ConfigError> {
        let alpha = self
            .weight
            .ok_or(crate::ConfigError::Missing("alpha"))?
            .resolve()?;
        let mut ewma = EwmVar::builder().alpha(alpha).min_samples(self.min_samples);
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

    fn warmed(alpha: f64) -> ZScoreNorm<f64> {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(alpha).build().unwrap();
        for i in 0..500 {
            let _ = zs.update(100.0 + f64::from(i % 7)).unwrap();
        }
        zs
    }

    #[test]
    fn scores_against_the_statistics_before_the_sample() {
        let mut zs = warmed(0.1);
        let (mean, sd) = (zs.mean().unwrap(), zs.std_dev().unwrap());
        let x = 110.0;
        let expected = (x - mean) / sd;
        assert_eq!(zs.normalize(x).unwrap(), Some(expected));
        assert_eq!(zs.update(x).unwrap(), Some(expected));
        // The fold happened after the score.
        assert!(zs.mean().unwrap() > mean);
    }

    #[test]
    fn an_outlier_is_not_capped_by_its_own_weight() {
        // Folding first bounds |z| by sqrt((1 - alpha) / alpha): 3.0 at
        // alpha 0.1, 1.0 at 0.5.
        for alpha in [0.1, 0.5] {
            let mut zs = warmed(alpha);
            let z = zs.update(1e9).unwrap().unwrap();
            assert!(z > 1e6, "alpha {alpha}: z = {z}");
        }
    }

    #[test]
    fn nothing_to_score_against_is_none() {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
        // min_samples 2: the first two samples have no primed statistics
        // behind them; the third does.
        assert_eq!(zs.update(1.0).unwrap(), None);
        assert_eq!(zs.normalize(5.0).unwrap(), None);
        assert_eq!(zs.update(3.0).unwrap(), None);
        assert!(zs.is_primed());
        assert!(zs.update(2.0).unwrap().is_some());
        assert_eq!(zs.count(), 3);
    }

    #[test]
    fn zero_scale_follows_the_division_by_zero_convention() {
        // 0.1 is not exact in binary, so the mean and variance carry
        // rounding residue; the floor absorbs it.
        for constant in [42.0, 0.1, -1e9, 0.0] {
            let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
            let _ = zs.update(constant).unwrap();
            let _ = zs.update(constant).unwrap();
            for _ in 0..100 {
                assert_eq!(zs.update(constant).unwrap(), Some(0.0), "{constant}");
            }
            let step = constant.abs().max(1.0) * 1e-6;
            assert_eq!(
                zs.normalize(constant + step).unwrap(),
                Some(f64::INFINITY),
                "{constant}"
            );
            assert_eq!(
                zs.normalize(constant - step).unwrap(),
                Some(f64::NEG_INFINITY),
                "{constant}"
            );
        }
    }

    #[test]
    fn a_jump_out_of_a_flat_stream_scores_infinite_then_finite() {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
        let mut tracker = EwmVar::builder().alpha(0.1).build().unwrap();
        for _ in 0..50 {
            let _ = zs.update(100.0).unwrap();
            tracker.update(100.0);
        }
        let z = zs.update(150.0).unwrap().unwrap();
        assert!(z > 4.0);
        assert_eq!(z.clamp(-5.0, 5.0), 5.0);
        // The jump gave the stream a scale: a second sample at the new level
        // scores against the mean and deviation the jump left behind.
        let after_jump = tracker.update(150.0).unwrap();
        let expected = (150.0 - after_jump.mean) / after_jump.std_dev();
        assert_eq!(zs.update(150.0).unwrap(), Some(expected));
        assert!((2.5..3.5).contains(&expected), "{expected}");
    }

    #[test]
    fn f32_zero_scale_is_infinite_too() {
        let mut zs = ZScoreNorm::<f32>::builder().alpha(0.1).build().unwrap();
        for _ in 0..10 {
            let _ = zs.update(7.0).unwrap();
        }
        assert_eq!(zs.update(8.0).unwrap(), Some(f32::INFINITY));
    }

    #[test]
    fn seeded_statistics_score_at_once() {
        let mut zs = ZScoreNorm::<f64>::builder()
            .alpha(0.1)
            .seed(100.0, 25.0)
            .build()
            .unwrap();
        assert_eq!(zs.normalize(105.0).unwrap(), Some(1.0));
        assert_eq!(zs.update(90.0).unwrap(), Some(-2.0));
    }

    #[test]
    fn f32_boundary() {
        let mut zs = ZScoreNorm::<f32>::builder()
            .alpha(0.1)
            .seed(100.0, 25.0)
            .build()
            .unwrap();
        assert_eq!(zs.update(110.0).unwrap(), Some(2.0f32));
    }

    #[test]
    fn rejects_nan_inf() {
        let mut zs = warmed(0.1);
        let n = zs.count();
        assert_eq!(zs.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(zs.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(zs.normalize(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(
            zs.normalize(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(zs.count(), n);
    }

    #[test]
    fn a_bad_knob_is_reported_under_its_own_name() {
        use crate::ConfigError::{Invalid, Missing};
        let b = ZScoreNorm::<f64>::builder;
        assert_eq!(b().build().unwrap_err(), Missing("alpha"));
        assert_eq!(
            b().span(1).build().unwrap_err(),
            Invalid("span must be at least 2")
        );
        assert_eq!(
            b().halflife(0.0).build().unwrap_err(),
            Invalid("halflife must be positive and finite")
        );
        assert_eq!(
            b().alpha(1.0).build().unwrap_err(),
            Invalid("alpha must be in (0, 1)")
        );
    }

    #[test]
    fn reset_clears() {
        let mut zs = warmed(0.1);
        assert!(zs.is_primed());
        zs.reset();
        assert_eq!(zs.count(), 0);
        assert!(!zs.is_primed());
        assert!(zs.mean().is_none());
    }
}
