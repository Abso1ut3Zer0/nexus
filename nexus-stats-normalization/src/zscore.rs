use core::marker::PhantomData;

use nexus_stats_core::Float;
use nexus_stats_core::statistics::{EwmVar, MeanVariance};

/// Z-score normalizer over an exponentially weighted mean and variance.
///
/// Scores a sample as `(sample - mean) / std_dev`, against the [`EwmVar`]
/// statistics of the samples before it. Use it to put streams of different
/// scales on a common one, and as an outlier score.
///
/// A stream with no spread has no scale, so there is no score: `None`, as
/// NumPy, pandas, and SciPy report no value (NaN) there.
///
/// `T` is the sample type at the boundary, `f64` or `f32`. The statistics
/// accumulate in `f64` either way, and `ZScoreNorm<f32>` returns infinity
/// for a finite score too large for `f32`.
///
/// # Examples
///
/// ```
/// use nexus_stats_normalization::ZScoreNorm;
///
/// let mut zs = ZScoreNorm::<f64>::builder().span(20).build().unwrap();
/// for i in 0..100 {
///     zs.update(100.0 + f64::from(i % 5));
/// }
/// // In-range samples score small; an outlier is not capped.
/// assert!(zs.normalize(102.0).unwrap().abs() < 1.0);
/// assert!(zs.update(1_000.0).unwrap() > 100.0);
/// ```
#[derive(Debug, Clone)]
pub struct ZScoreNorm<T: Float> {
    inner: EwmVar,
    _sample: PhantomData<T>,
}

/// Builder for [`ZScoreNorm`].
#[derive(Debug, Clone)]
pub struct ZScoreNormBuilder<T: Float> {
    weight: Option<nexus_stats_core::math::EwWeight>,
    min_samples: u64,
    seed: Option<MeanVariance>,
    _sample: PhantomData<T>,
}

impl<T: Float> ZScoreNorm<T> {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> ZScoreNormBuilder<T> {
        ZScoreNormBuilder {
            weight: None,
            min_samples: 2,
            seed: None,
            _sample: PhantomData,
        }
    }

    /// Scores a sample against the statistics of the samples before it,
    /// then feeds it in.
    ///
    /// Returns `None` until primed, and while the stream has no spread to
    /// score against. The sample is fed in either way.
    ///
    /// Does not validate `sample`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    pub fn update(&mut self, sample: T) -> Option<T> {
        let sample = sample.to_f64();
        // Scored before it is fed in, so an outlier cannot dilute itself.
        let score = self.score(sample);
        self.inner.update(sample);
        score
    }

    /// Checked update. Scores and feeds `sample`, or returns an error and
    /// leaves the normalizer unchanged if `sample` is NaN, infinite, or
    /// above `1e120` in magnitude (see [input limits](nexus_stats_core#input-limits)).
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber) if `sample`
    ///   is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if `sample` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](nexus_stats_core::DataError::OutOfRange) if `sample`
    ///   is finite and above the limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_normalization::{DataError, ZScoreNorm};
    ///
    /// let mut zs = ZScoreNorm::<f64>::builder().alpha(0.5).build().unwrap();
    /// assert_eq!(zs.checked_update(1.0), Ok(None));
    /// assert_eq!(zs.checked_update(f64::NAN), Err(DataError::NotANumber));
    /// assert_eq!(zs.count(), 1);
    /// ```
    pub fn checked_update(&mut self, sample: T) -> Result<Option<T>, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_input(
            sample.to_f64(),
            nexus_stats_core::math::LIMIT_FOR_SQUARES,
        )?;
        Ok(self.update(sample))
    }

    /// Scores a value against the current statistics without feeding it in.
    ///
    /// Returns `None` if not primed, or if the stream has no spread.
    ///
    /// Does not validate `value`; arithmetic follows IEEE 754. See
    /// [`checked_normalize`](Self::checked_normalize).
    #[must_use]
    pub fn normalize(&self, value: T) -> Option<T> {
        self.score(value.to_f64())
    }

    /// Checked normalize. Scores `value`, or returns an error if it is NaN,
    /// infinite, or above `1e120` in magnitude: the values
    /// [`checked_update`](Self::checked_update) accepts.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber) if `value`
    ///   is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if `value` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](nexus_stats_core::DataError::OutOfRange) if `value`
    ///   is finite and above the limit.
    pub fn checked_normalize(&self, value: T) -> Result<Option<T>, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_input(
            value.to_f64(),
            nexus_stats_core::math::LIMIT_FOR_SQUARES,
        )?;
        Ok(self.normalize(value))
    }

    /// Current exponentially weighted mean, or `None` if not primed.
    #[must_use]
    pub fn mean(&self) -> Option<T> {
        self.inner.value().map(|reading| T::from_f64(reading.mean))
    }

    /// Current exponentially weighted standard deviation, or `None` if not
    /// primed.
    #[must_use]
    pub fn std_dev(&self) -> Option<T> {
        self.inner
            .value()
            .map(|reading| T::from_f64(reading.std_dev()))
    }

    /// Number of samples fed since construction or `reset`. A seed is not a
    /// sample.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.inner.count()
    }

    /// Whether the statistics are available: `min_samples` reached, or
    /// seeded.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.inner.is_primed()
    }

    /// Returns to no samples, and to the seed if there is one. Parameters
    /// unchanged.
    pub fn reset(&mut self) {
        self.inner.reset();
    }

    /// Resets to no samples, starting from `mean` and `variance` as a new
    /// seed.
    ///
    /// # Errors
    ///
    /// `Invalid` if `mean` is not finite or `variance` is not finite and
    /// non-negative. The normalizer is left unchanged.
    pub fn reset_with_seed(
        &mut self,
        mean: T,
        variance: T,
    ) -> Result<(), nexus_stats_core::ConfigError> {
        self.inner.reset_with_seed(mean.to_f64(), variance.to_f64())
    }

    fn score(&self, value: f64) -> Option<T> {
        let reading = self.inner.value()?;

        // No spread beyond rounding: no scale to score against.
        if reading.variance <= nexus_stats_core::math::rounding_variance(reading.mean) {
            return None;
        }

        Some(T::from_f64((value - reading.mean) / reading.std_dev()))
    }
}

impl<T: Float> ZScoreNormBuilder<T> {
    /// Direct smoothing factor. Must be in (0, 1) exclusive.
    #[must_use]
    pub fn alpha(mut self, alpha: T) -> Self {
        self.weight = Some(nexus_stats_core::math::EwWeight::Alpha(alpha.to_f64()));
        self
    }

    /// Samples for weight to decay by half. Must be positive and finite.
    #[must_use]
    pub fn halflife(mut self, halflife: T) -> Self {
        self.weight = Some(nexus_stats_core::math::EwWeight::Halflife(
            halflife.to_f64(),
        ));
        self
    }

    /// Span in samples (the pandas `span` convention, `alpha = 2 / (n + 1)`).
    /// Must be at least 2.
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(nexus_stats_core::math::EwWeight::Span(n));
        self
    }

    /// Minimum samples before values are valid. Default and minimum: 2
    /// (one sample has no deviation).
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Starts the normalizer converged on this mean and variance.
    ///
    /// Scores are available at once (`min_samples` no longer applies),
    /// `count()` still counts only samples fed, and `reset()` returns to the
    /// seed.
    #[must_use]
    pub fn seed(mut self, mean: T, variance: T) -> Self {
        self.seed = Some(MeanVariance {
            mean: mean.to_f64(),
            variance: variance.to_f64(),
        });
        self
    }

    /// Builds the z-score normalizer.
    ///
    /// # Errors
    ///
    /// - `Missing("alpha")` if none of `alpha`, `halflife`, `span` was set.
    /// - `Invalid` if `alpha` is outside (0, 1), `halflife` is not positive
    ///   and finite, or `span` is below 2; the message names the knob set.
    /// - `Invalid` if `min_samples` is below 2, or the seed is not a finite
    ///   mean and a finite non-negative variance.
    pub fn build(self) -> Result<ZScoreNorm<T>, nexus_stats_core::ConfigError> {
        let alpha = self
            .weight
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?
            .resolve()?;
        let mut statistics = EwmVar::builder().alpha(alpha).min_samples(self.min_samples);
        if let Some(seed) = self.seed {
            statistics = statistics.seed(seed.mean, seed.variance);
        }
        Ok(ZScoreNorm {
            inner: statistics.build()?,
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
            zs.update(100.0 + f64::from(i % 7));
        }
        zs
    }

    #[test]
    fn scores_against_the_statistics_before_the_sample() {
        let mut zs = warmed(0.1);
        let (mean, sd) = (zs.mean().unwrap(), zs.std_dev().unwrap());
        let x = 110.0;
        let expected = (x - mean) / sd;
        assert_eq!(zs.normalize(x), Some(expected));
        assert_eq!(zs.update(x), Some(expected));
        // The sample was fed in after it was scored.
        assert!(zs.mean().unwrap() > mean);
    }

    #[test]
    fn an_outlier_is_not_capped_by_its_own_weight() {
        // Fed in before scoring, a sample's own weight would bound its
        // score: about 2.9 at alpha 0.1.
        for alpha in [0.1, 0.5] {
            let mut zs = warmed(alpha);
            let z = zs.update(1e9).unwrap();
            assert!(z > 1e6, "alpha {alpha}: z = {z}");
        }
    }

    #[test]
    fn nothing_to_score_against_is_none() {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
        // min_samples 2: the first two samples have no primed statistics
        // behind them; the third does.
        assert_eq!(zs.update(1.0), None);
        assert_eq!(zs.normalize(5.0), None);
        assert_eq!(zs.update(3.0), None);
        assert!(zs.is_primed());
        assert!(zs.update(2.0).is_some());
        assert_eq!(zs.count(), 3);
    }

    #[test]
    fn a_stream_with_no_spread_has_no_score() {
        for constant in [42.0, 0.1, -1e9, 0.0] {
            let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
            for _ in 0..100 {
                assert_eq!(zs.update(constant), None, "{constant}");
            }
            assert!(zs.is_primed());
            let step = constant.abs().max(1.0) * 1e-6;
            assert_eq!(zs.normalize(constant), None, "{constant}");
            assert_eq!(zs.normalize(constant + step), None, "{constant}");
            assert_eq!(zs.normalize(constant - step), None, "{constant}");
        }
    }

    #[test]
    fn a_jump_out_of_a_flat_stream_has_no_score_then_gives_one() {
        let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
        let mut statistics = EwmVar::builder().alpha(0.1).build().unwrap();
        for _ in 0..50 {
            zs.update(100.0);
            statistics.update(100.0);
        }
        // Nothing to measure the jump against.
        assert_eq!(zs.update(150.0), None);
        // The jump gave the stream a spread: the next sample is scored
        // against it.
        let after_jump = statistics.update(150.0).unwrap();
        let expected = (150.0 - after_jump.mean) / after_jump.std_dev();
        assert_eq!(zs.update(150.0), Some(expected));
    }

    #[test]
    fn spread_within_rounding_of_the_mean_counts_as_none() {
        // A variance of (EPSILON * mean)^2 is what rounding alone produces.
        let mean = 1e6;
        let at = (f64::EPSILON * mean) * (f64::EPSILON * mean);
        let flat = ZScoreNorm::<f64>::builder()
            .alpha(0.1)
            .seed(mean, at / 4.0)
            .build()
            .unwrap();
        assert_eq!(flat.normalize(mean + 1.0), None);

        let spread = ZScoreNorm::<f64>::builder()
            .alpha(0.1)
            .seed(mean, at * 4.0)
            .build()
            .unwrap();
        assert!(spread.normalize(mean + 1.0).is_some());
    }

    #[test]
    fn seeded_statistics_score_at_once() {
        let mut zs = ZScoreNorm::<f64>::builder()
            .alpha(0.1)
            .seed(100.0, 25.0)
            .build()
            .unwrap();
        assert_eq!(zs.normalize(105.0), Some(1.0));
        assert_eq!(zs.update(90.0), Some(-2.0));
    }

    #[test]
    fn f32_boundary() {
        let mut zs = ZScoreNorm::<f32>::builder()
            .alpha(0.1)
            .seed(100.0, 25.0)
            .build()
            .unwrap();
        assert_eq!(zs.update(110.0), Some(2.0f32));

        let mut flat = ZScoreNorm::<f32>::builder().alpha(0.1).build().unwrap();
        for _ in 0..10 {
            flat.update(7.0);
        }
        assert_eq!(flat.update(8.0), None);

        // A finite score too large for f32.
        let tight = ZScoreNorm::<f32>::builder()
            .alpha(0.1)
            .seed(0.0, 1e-6)
            .build()
            .unwrap();
        assert_eq!(tight.normalize(1e36), Some(f32::INFINITY));
    }

    #[test]
    fn min_samples_below_two_is_refused() {
        for min in [0, 1] {
            assert!(
                ZScoreNorm::<f64>::builder()
                    .alpha(0.1)
                    .min_samples(min)
                    .build()
                    .is_err(),
                "{min}"
            );
        }
    }

    #[test]
    fn a_seed_is_a_state_not_samples() {
        let mut zs = ZScoreNorm::<f64>::builder()
            .alpha(0.1)
            .seed(100.0, 25.0)
            .build()
            .unwrap();
        assert!(zs.is_primed());
        assert_eq!(zs.count(), 0);
        zs.update(110.0);
        zs.reset();
        assert_eq!(zs.count(), 0);
        assert_eq!(zs.normalize(110.0), Some(2.0));
    }

    #[test]
    fn reset_with_seed_starts_from_the_new_seed() {
        let mut zs = warmed(0.1);
        zs.reset_with_seed(10.0, 4.0).unwrap();
        assert_eq!(zs.count(), 0);
        assert_eq!(zs.normalize(14.0), Some(2.0));

        assert!(zs.reset_with_seed(f64::NAN, 1.0).is_err());
        assert!(zs.reset_with_seed(0.0, -1.0).is_err());
        assert_eq!(zs.normalize(14.0), Some(2.0));
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use nexus_stats_core::DataError::{Infinite, NotANumber, OutOfRange};

        let mut zs = warmed(0.1);
        let before = (zs.count(), zs.mean(), zs.std_dev());

        assert_eq!(zs.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(zs.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(zs.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(zs.checked_update(1e121), Err(OutOfRange));

        assert_eq!((zs.count(), zs.mean(), zs.std_dev()), before);
    }

    #[test]
    fn checked_normalize_refuses_what_checked_update_refuses() {
        use nexus_stats_core::DataError::{Infinite, NotANumber, OutOfRange};

        let zs = warmed(0.1);
        assert_eq!(zs.checked_normalize(f64::NAN), Err(NotANumber));
        assert_eq!(zs.checked_normalize(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(zs.checked_normalize(1e121), Err(OutOfRange));
        assert_eq!(zs.checked_normalize(105.0), Ok(zs.normalize(105.0)));

        // At the limit the score is still finite.
        let score = zs.checked_normalize(1e120).unwrap().unwrap();
        assert!(score.is_finite(), "{score}");
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = warmed(0.2);
        let mut unchecked = checked.clone();
        for x in [102.0, 99.5, 1e9, 103.25] {
            assert_eq!(checked.checked_update(x), Ok(unchecked.update(x)));
        }
    }

    #[test]
    fn update_does_not_validate() {
        let mut zs = warmed(0.1);
        let n = zs.count();
        assert!(zs.update(f64::NAN).unwrap().is_nan());
        assert_eq!(zs.count(), n + 1);
    }

    #[test]
    fn a_bad_knob_is_reported_under_its_own_name() {
        use nexus_stats_core::ConfigError::{Invalid, Missing};
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
