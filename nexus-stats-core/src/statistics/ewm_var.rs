use crate::math::{EwWeight, MulAdd};
use crate::statistics::running_mean::step_mean;

/// Exponentially weighted mean and variance.
///
/// Sample `i` of `n` carries weight `(1 - alpha)^(n - i)`. The mean is the
/// weighted mean and the variance is the unbiased weighted variance. This is
/// what pandas computes by default, `ewm(alpha=a).mean()` and
/// `ewm(alpha=a).var()`, and what Polars computes as `ewm_mean` and
/// `ewm_var`.
///
/// # Seeding
///
/// `seed(mean, variance)` starts the tracker as if it had already converged
/// on a stream with that mean and variance: a reading is available at once,
/// `count()` still counts only samples fed, and `reset()` returns to the
/// seed.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::EwmVar;
///
/// let mut ew = EwmVar::builder().alpha(0.5).build().unwrap();
/// assert_eq!(ew.update(0.0), None); // one sample has no variance
/// let reading = ew.update(2.0).unwrap();
/// // Weights 0.5 and 1: mean 4/3, variance 2.
/// assert!((reading.mean - 4.0 / 3.0).abs() < 1e-12);
/// assert!((reading.variance - 2.0).abs() < 1e-12);
/// ```
#[derive(Debug, Clone)]
pub struct EwmVar {
    alpha: f64,
    /// `1 - alpha`: what one sample does to every earlier weight.
    decay: f64,
    mean: f64,
    /// Weighted sum of squared deviations from the mean.
    squared_deviations: f64,
    /// Sum of the weights.
    weight: f64,
    /// Sum of the squared weights.
    weight_squares: f64,
    count: u64,
    /// Samples needed before a reading: `min_samples`, or 0 when seeded.
    prime_at: u64,
    /// What `reset` restores.
    seed: Option<MeanVariance>,
}

/// An [`EwmVar`] reading.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MeanVariance {
    /// Exponentially weighted mean.
    pub mean: f64,
    /// Unbiased exponentially weighted variance.
    pub variance: f64,
}

impl MeanVariance {
    /// Standard deviation: the square root of the variance.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn std_dev(&self) -> f64 {
        crate::math::sqrt(self.variance)
    }
}

/// Builder for [`EwmVar`].
#[derive(Debug, Clone)]
pub struct EwmVarBuilder {
    weight: Option<EwWeight>,
    min_samples: u64,
    seed: Option<MeanVariance>,
}

impl EwmVar {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> EwmVarBuilder {
        EwmVarBuilder {
            weight: None,
            min_samples: 2,
            seed: None,
        }
    }

    /// Feeds a sample. Returns the reading once primed.
    ///
    /// Does not validate `sample`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, sample: f64) -> Option<MeanVariance> {
        self.count += 1;

        // Every earlier weight decays; the new sample enters at weight 1.
        self.weight = self.decay.fma(self.weight, 1.0);
        self.weight_squares = (self.decay * self.decay).fma(self.weight_squares, 1.0);

        let deviation = step_mean(&mut self.mean, sample, 1.0 / self.weight);
        self.squared_deviations = self
            .decay
            .fma(self.squared_deviations, deviation.before * deviation.after);

        self.value()
    }

    /// Checked update. Feeds `sample` and returns the reading, or returns an
    /// error and leaves the tracker unchanged if `sample` is NaN, infinite,
    /// or above `1e120` in magnitude (see [input limits](crate#input-limits)).
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `sample`
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if `sample` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if `sample`
    ///   is finite and above the limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::{DataError, statistics::EwmVar};
    ///
    /// let mut ew = EwmVar::builder().alpha(0.5).build().unwrap();
    /// assert_eq!(ew.checked_update(1.0), Ok(None));
    /// assert_eq!(ew.checked_update(f64::NAN), Err(DataError::NotANumber));
    /// assert_eq!(ew.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(
        &mut self,
        sample: f64,
    ) -> Result<Option<MeanVariance>, crate::DataError> {
        crate::math::check_input(sample, crate::math::LIMIT_FOR_SQUARES)?;
        Ok(self.update(sample))
    }

    /// The current reading, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<MeanVariance> {
        if !self.is_primed() {
            return None;
        }

        // The unbiased divisor for weighted samples: W - W2 / W.
        let divisor = self.weight - self.weight_squares / self.weight;
        Some(MeanVariance {
            mean: self.mean,
            variance: self.squared_deviations / divisor,
        })
    }

    /// The smoothing factor alpha.
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.alpha
    }

    /// Number of samples fed since construction or `reset`. A seed is not a
    /// sample.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether a reading is available: `min_samples` reached, or seeded.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.prime_at
    }

    /// Returns to the as-built state: no samples, and the seed if one was
    /// configured. Parameters unchanged.
    pub fn reset(&mut self) {
        self.count = 0;
        self.start();
    }

    /// Sets the as-built state: empty, or converged on the seed.
    fn start(&mut self) {
        let Some(seed) = self.seed else {
            self.mean = 0.0;
            self.squared_deviations = 0.0;
            self.weight = 0.0;
            self.weight_squares = 0.0;
            return;
        };

        // Where the two weight sums converge: 1 / (1 - decay) and
        // 1 / (1 - decay^2).
        self.weight = 1.0 / self.alpha;
        self.weight_squares = 1.0 / (self.alpha * (2.0 - self.alpha));
        self.mean = seed.mean;
        self.squared_deviations = seed.variance * (self.weight - self.weight_squares / self.weight);
    }
}

impl EwmVarBuilder {
    /// Direct smoothing factor. Must be in (0, 1) exclusive.
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Samples for weight to decay by half. Must be positive and finite.
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Span in samples (the pandas `span` convention, `alpha = 2 / (n + 1)`).
    /// Must be at least 2.
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(EwWeight::Span(n));
        self
    }

    /// Minimum samples before a reading is returned. Default and minimum: 2
    /// (one sample has no variance).
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Starts the tracker converged on this mean and variance.
    ///
    /// A reading is available at once (`min_samples` no longer applies) and
    /// `reset()` returns to the seed.
    #[must_use]
    pub fn seed(mut self, mean: f64, variance: f64) -> Self {
        self.seed = Some(MeanVariance { mean, variance });
        self
    }

    /// Builds the tracker.
    ///
    /// # Errors
    ///
    /// - `Missing("alpha")` if none of `alpha`, `halflife`, `span` was set.
    /// - `Invalid` if `alpha` is outside (0, 1), `halflife` is not positive
    ///   and finite, or `span` is below 2; the message names the knob set.
    /// - `Invalid` if `min_samples` is below 2, or the seed is not a finite
    ///   mean and a finite non-negative variance.
    pub fn build(self) -> Result<EwmVar, crate::ConfigError> {
        let alpha = self
            .weight
            .ok_or(crate::ConfigError::Missing("alpha"))?
            .resolve()?;
        if self.min_samples < 2 {
            return Err(crate::ConfigError::Invalid(
                "min_samples must be >= 2: one sample has no variance",
            ));
        }
        if let Some(seed) = self.seed
            && (!seed.mean.is_finite() || !crate::math::nonnegative_finite(seed.variance))
        {
            return Err(crate::ConfigError::Invalid(
                "seed needs a finite mean and a finite non-negative variance",
            ));
        }

        let mut tracker = EwmVar {
            alpha,
            decay: 1.0 - alpha,
            mean: 0.0,
            squared_deviations: 0.0,
            weight: 0.0,
            weight_squares: 0.0,
            count: 0,
            prime_at: if self.seed.is_some() {
                0
            } else {
                self.min_samples
            },
            seed: self.seed,
        };
        tracker.start();
        Ok(tracker)
    }
}

#[cfg(test)]
// Expected values are written as plain arithmetic, independent of the fused
// forms the code under test uses.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;

    fn close(a: f64, b: f64) -> bool {
        (a - b).abs() <= 1e-12 * b.abs().max(1.0)
    }

    fn assert_close(got: MeanVariance, want: MeanVariance, context: &str) {
        assert!(
            close(got.mean, want.mean) && close(got.variance, want.variance),
            "{context}: {got:?} vs {want:?}"
        );
    }

    /// The defining formulas, computed from the stored samples: weights
    /// `(1 - alpha)^(n - i)`, weighted mean, unbiased weighted variance.
    fn reference(samples: &[f64], alpha: f64) -> MeanVariance {
        let n = samples.len();
        let weights: [f64; 64] = core::array::from_fn(|i| {
            if i < n {
                (1.0 - alpha).powi((n - 1 - i) as i32)
            } else {
                0.0
            }
        });
        let w: f64 = weights.iter().sum();
        let w2: f64 = weights.iter().map(|x| x * x).sum();
        let mean = samples
            .iter()
            .zip(&weights)
            .map(|(x, w)| x * w)
            .sum::<f64>()
            / w;
        let ss: f64 = samples
            .iter()
            .zip(&weights)
            .map(|(x, w)| w * (x - mean) * (x - mean))
            .sum();
        MeanVariance {
            mean,
            variance: ss / (w - w2 / w),
        }
    }

    #[test]
    fn matches_hand_computed_values() {
        // alpha 0.5, samples 0, 2, 4.
        // After two: weights 0.5, 1. Mean 4/3. Sum of squared deviations
        // 0.5 * (4/3)^2 + (2/3)^2 = 4/3; W - W2/W = 1.5 - 1.25/1.5 = 2/3.
        // After three: weights 0.25, 0.5, 1. Mean 20/7; variance 26/7.
        let mut ew = EwmVar::builder().alpha(0.5).build().unwrap();
        assert_eq!(ew.update(0.0), None);
        let r = ew.update(2.0).unwrap();
        assert!(close(r.mean, 4.0 / 3.0) && close(r.variance, 2.0), "{r:?}");
        let r = ew.update(4.0).unwrap();
        assert!(
            close(r.mean, 20.0 / 7.0) && close(r.variance, 26.0 / 7.0),
            "{r:?}"
        );
    }

    #[test]
    fn matches_the_defining_formulas_at_every_step() {
        let samples: [f64; 40] =
            core::array::from_fn(|i| 100.0 + ((i * 37 % 11) as f64 - 5.0) * 1.5 + (i / 13) as f64);
        for alpha in [0.02, 0.1, 0.5, 0.9] {
            let mut ew = EwmVar::builder().alpha(alpha).build().unwrap();
            for (i, &x) in samples.iter().enumerate() {
                let got = ew.update(x);
                if i == 0 {
                    assert_eq!(got, None);
                    continue;
                }
                assert_close(
                    got.unwrap(),
                    reference(&samples[..=i], alpha),
                    &format!("alpha {alpha} step {i}"),
                );
            }
        }
    }

    #[test]
    fn matches_pandas_reference_values() {
        // pandas 3.1.1: s.ewm(alpha=0.1).mean() / .var() on these samples.
        let samples = [
            99.932_122_668_392_3,
            104.556_595_384_052_86,
            104.065_758_219_926_12,
        ];
        let want = [
            (102.366_055_676_634_7, 10.692_873_948_944_445),
            (102.993_252_187_074_35, 6.077_790_683_504_025),
        ];
        let mut ew = EwmVar::builder().alpha(0.1).build().unwrap();
        let _ = ew.update(samples[0]);
        for (x, (mean, variance)) in samples[1..].iter().zip(want) {
            let r = ew.update(*x).unwrap();
            assert_close(r, MeanVariance { mean, variance }, "pandas");
        }
    }

    #[test]
    fn matches_the_defining_formulas_on_a_long_stream() {
        // At alpha 0.5 the 64 newest samples carry all the weight an f64
        // can resolve.
        let alpha = 0.5;
        let mut ew = EwmVar::builder().alpha(alpha).build().unwrap();
        let mut window = [0.0f64; 64];
        for i in 0..5_000u32 {
            let x = f64::from(i * 7 % 13);
            window.copy_within(1.., 0);
            window[63] = x;
            let _ = ew.update(x);
        }
        assert_close(ew.value().unwrap(), reference(&window, alpha), "long");
    }

    #[test]
    fn update_returns_what_value_reads() {
        let mut ew = EwmVar::builder().alpha(0.3).build().unwrap();
        for x in [1.0, 5.0, 2.0, 8.0] {
            assert_eq!(ew.update(x), ew.value());
        }
    }

    #[test]
    fn constant_input_has_zero_variance() {
        let mut ew = EwmVar::builder().alpha(0.1).build().unwrap();
        for _ in 0..200 {
            let _ = ew.update(100.0);
        }
        let r = ew.value().unwrap();
        assert_eq!(r.mean, 100.0);
        assert_eq!(r.variance, 0.0);
    }

    #[test]
    #[cfg(any(feature = "std", feature = "libm"))]
    fn std_dev_is_the_root_of_the_variance() {
        let r = MeanVariance {
            mean: 1.0,
            variance: 25.0,
        };
        assert_eq!(r.std_dev(), 5.0);
    }

    #[test]
    fn seed_is_a_converged_state_not_samples() {
        let seed = MeanVariance {
            mean: 100.0,
            variance: 25.0,
        };
        let mut ew = EwmVar::builder()
            .alpha(0.1)
            .min_samples(50)
            .seed(seed.mean, seed.variance)
            .build()
            .unwrap();
        assert!(ew.is_primed());
        assert_eq!(ew.count(), 0);
        assert_close(ew.value().unwrap(), seed, "as built");

        // A sample is blended at the converged weight, alpha.
        let r = ew.update(110.0).unwrap();
        assert!(close(r.mean, 101.0), "{r:?}");
        assert_eq!(ew.count(), 1);

        ew.reset();
        assert_eq!(ew.count(), 0);
        assert_close(ew.value().unwrap(), seed, "after reset");
    }

    #[test]
    fn a_seed_evolves_as_a_converged_tracker_would() {
        // Converge an unseeded tracker on a long stream, seed a second one
        // with its reading, then feed both the same samples: they agree.
        let alpha = 0.2;
        let mut warm = EwmVar::builder().alpha(alpha).build().unwrap();
        for i in 0..2_000u32 {
            let _ = warm.update(50.0 + f64::from(i * 7 % 13));
        }
        let at = warm.value().unwrap();
        let mut seeded = EwmVar::builder()
            .alpha(alpha)
            .seed(at.mean, at.variance)
            .build()
            .unwrap();
        for x in [48.0, 61.0, 55.5, 30.0, 58.0] {
            assert_close(seeded.update(x).unwrap(), warm.update(x).unwrap(), "seeded");
        }
    }

    #[test]
    fn unseeded_reset_starts_over() {
        let mut ew = EwmVar::builder().alpha(0.5).build().unwrap();
        for x in [5.0, 9.0, 1.0] {
            let _ = ew.update(x);
        }
        ew.reset();
        assert_eq!(ew.count(), 0);
        assert_eq!(ew.value(), None);
        assert_eq!(ew.update(0.0), None);
        let r = ew.update(2.0).unwrap();
        assert!(close(r.mean, 4.0 / 3.0) && close(r.variance, 2.0), "{r:?}");
    }

    #[test]
    fn min_samples_withholds_the_reading() {
        let mut ew = EwmVar::builder().alpha(0.1).min_samples(5).build().unwrap();
        for i in 0..4 {
            assert_eq!(ew.update(f64::from(i)), None);
            assert!(!ew.is_primed());
        }
        assert!(ew.update(4.0).is_some());
    }

    #[test]
    fn builder_validation() {
        use crate::ConfigError::{Invalid, Missing};
        let b = EwmVar::builder;
        assert_eq!(b().build().unwrap_err(), Missing("alpha"));
        assert_eq!(
            b().alpha(1.0).build().unwrap_err(),
            Invalid("alpha must be in (0, 1)")
        );
        assert_eq!(
            b().span(1).build().unwrap_err(),
            Invalid("span must be at least 2")
        );
        for min in [0, 1] {
            assert_eq!(
                b().alpha(0.1).min_samples(min).build().unwrap_err(),
                Invalid("min_samples must be >= 2: one sample has no variance")
            );
        }
        for (mean, variance) in [
            (f64::NAN, 1.0),
            (0.0, -1.0),
            (0.0, f64::INFINITY),
            (0.0, f64::NAN),
        ] {
            assert_eq!(
                b().alpha(0.1).seed(mean, variance).build().unwrap_err(),
                Invalid("seed needs a finite mean and a finite non-negative variance")
            );
        }
        assert!(b().alpha(0.1).seed(0.0, 0.0).build().is_ok());
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let mut ew = EwmVar::builder().alpha(0.1).build().unwrap();
        ew.checked_update(1.0).unwrap();
        ew.checked_update(3.0).unwrap();
        let before = ew.value();

        assert_eq!(ew.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(ew.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(ew.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(ew.checked_update(1e121), Err(OutOfRange));
        assert_eq!(ew.checked_update(-1e121), Err(OutOfRange));

        assert_eq!((ew.count(), ew.value()), (2, before));
    }

    #[test]
    fn checked_update_accepts_the_limit_without_overflow() {
        let limit = crate::math::LIMIT_FOR_SQUARES;
        let mut ew = EwmVar::builder().alpha(1e-9).build().unwrap();
        for i in 0..10_000u32 {
            let x = if i % 2 == 0 { limit } else { -limit };
            ew.checked_update(x).unwrap();
        }
        let r = ew.value().unwrap();
        assert!(r.mean.is_finite() && r.variance.is_finite(), "{r:?}");
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = EwmVar::builder().alpha(0.2).build().unwrap();
        let mut unchecked = checked.clone();
        for x in [2.0, 0.5, 1e9, 3.25] {
            assert_eq!(checked.checked_update(x), Ok(unchecked.update(x)));
        }
    }

    #[test]
    fn update_does_not_validate() {
        let mut ew = EwmVar::builder().alpha(0.5).build().unwrap();
        let _ = ew.update(1.0);
        let r = ew.update(f64::NAN).unwrap();
        assert!(r.mean.is_nan());
        assert_eq!(ew.count(), 2);
    }
}
