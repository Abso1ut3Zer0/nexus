use crate::math::{EwWeight, MulAdd};

/// Exponentially weighted mean and variance.
///
/// The estimator is the exponentially weighted mean and the unbiased
/// weighted variance: sample `i` of `n` carries weight `(1 - alpha)^(n - i)`,
/// the mean is the weighted mean, and the variance is the weighted sum of
/// squared deviations divided by `W - W2 / W`, where `W` is the sum of the
/// weights and `W2` the sum of their squares. This is what pandas computes
/// by default, `ewm(alpha=a).mean()` and `ewm(alpha=a).var()` (that is,
/// `adjust=True, bias=False`), and the readings match it to rounding.
///
/// It is unbiased from the second sample on: there is no warm-up period in
/// which the variance reads low, and no steady-state shortfall. (The plain
/// recursion `var = (1 - alpha) * (var + alpha * d^2)`, RiskMetrics-style,
/// reads 18% of the true variance after two samples at alpha 0.1 and 5% low
/// forever.)
///
/// # Precision at extreme weights
///
/// With alpha very close to 1 the mean follows each sample almost exactly,
/// so the variance is a difference of nearly equal numbers and loses
/// precision in proportion to `1 / (1 - alpha)`: negligible at 0.999,
/// nothing left at the largest alpha the builder accepts. The reading is
/// still a finite, non-negative number.
///
/// # Cost
///
/// The weight totals converge to constants (within about `36 / alpha`
/// samples). Until they do, an update refreshes two reciprocals; after
/// that it is two fused multiply-adds, the same work as the plain
/// recursion.
///
/// # Seeding
///
/// `seed(mean, variance)` starts the tracker as if it had already converged
/// on a stream with that mean and variance: readings are available at once,
/// `count()` still counts only samples fed, and `reset()` returns to the
/// seed.
///
/// # Use Cases
/// - Volatility tracking
/// - Adaptive thresholds (mean ± k * std_dev)
/// - Regime detection (variance spike = regime change)
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::EwmaVar;
///
/// let mut ew = EwmaVar::builder().alpha(0.5).build().unwrap();
/// assert_eq!(ew.update(0.0), None); // one sample has no variance
/// let reading = ew.update(2.0).unwrap();
/// // Two samples, weights 0.5 and 1: mean 4/3, unbiased variance 2.
/// assert!((reading.mean - 4.0 / 3.0).abs() < 1e-12);
/// assert!((reading.variance - 2.0).abs() < 1e-12);
/// assert_eq!(ew.last(), Some(reading));
/// ```
#[derive(Debug, Clone)]
pub struct EwmaVar {
    alpha: f64,
    one_minus_alpha: f64,
    one_minus_alpha_sq: f64,
    /// Weighted mean.
    mean: f64,
    /// Weighted sum of squared deviations from the mean.
    sum_sq_dev: f64,
    /// Sum of the weights, and of their squares.
    weight: f64,
    weight_sq: f64,
    /// `1 / weight` and `1 / (weight - weight_sq / weight)`: refreshed with
    /// the totals, constant once they settle. Kept as reciprocals so no
    /// division sits on the mean's dependency chain.
    inv_weight: f64,
    variance_scale: f64,
    /// The weight totals have stopped changing.
    settled: bool,
    count: u64,
    /// Samples needed before a reading: `min_samples`, or 0 when seeded.
    prime_at: u64,
    /// What `reset` restores: the seed, if any.
    seed: Option<MeanVariance>,
}

/// An [`EwmaVar`] reading: the exponentially weighted mean and variance.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MeanVariance {
    /// Exponentially weighted mean.
    pub mean: f64,
    /// Unbiased exponentially weighted variance. Never negative.
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

/// Builder for [`EwmaVar`].
#[derive(Debug, Clone)]
pub struct EwmaVarBuilder {
    weight: Option<EwWeight>,
    min_samples: u64,
    seed: Option<(f64, f64)>,
}

impl EwmaVar {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> EwmaVarBuilder {
        EwmaVarBuilder {
            weight: None,
            min_samples: 2,
            seed: None,
        }
    }

    /// Feeds a sample. Returns the reading once primed.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in. A
    /// NaN or an infinity makes the readings NaN from then on, until
    /// [`reset`](Self::reset); a finite value above
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT) in magnitude can overflow them. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Option<MeanVariance> {
        self.fold(sample);
        self.last()
    }

    /// [`update`](Self::update) with the input validated first: refuses a
    /// value that is NaN, infinite, or above [`INPUT_LIMIT`](crate::INPUT_LIMIT) in
    /// magnitude, and leaves the state untouched. Fed only through this
    /// method, no reading is ever NaN, or infinite unless its documentation
    /// says so.
    ///
    /// # Errors
    ///
    /// `DataError::NotANumber`, `DataError::Infinite`, or
    /// `DataError::OutOfRange` for a finite magnitude above the limit.
    #[inline]
    pub fn checked_update(
        &mut self,
        sample: f64,
    ) -> Result<Option<MeanVariance>, crate::DataError> {
        check_magnitude!(sample, crate::INPUT_LIMIT);
        Ok(self.update(sample))
    }

    /// The current reading, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<MeanVariance> {
        self.is_primed().then_some(MeanVariance {
            mean: self.mean,
            variance: self.sum_sq_dev * self.variance_scale,
        })
    }

    /// The smoothing factor alpha.
    #[inline]
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.alpha
    }

    /// Number of samples processed since construction or `reset`. A seed is
    /// not a sample.
    #[inline]
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
    #[inline]
    pub fn reset(&mut self) {
        self.count = 0;
        self.start();
    }

    /// Sum of the weights and sum of their squares, for callers that need
    /// the effective sample size.
    #[cfg(feature = "alloc")]
    #[inline]
    pub(crate) fn weight_totals(&self) -> (f64, f64) {
        (self.weight, self.weight_sq)
    }

    /// Whether the weight totals have reached their limits.
    #[cfg(feature = "alloc")]
    #[inline]
    pub(crate) fn is_settled(&self) -> bool {
        self.settled
    }

    /// [`update`](Self::update) without taking a reading: for the types
    /// built on this one.
    #[inline]
    pub(crate) fn fold(&mut self, sample: f64) {
        self.count += 1;
        if !self.settled {
            self.advance_weights();
        }
        // West's incremental weighted mean and sum of squared deviations,
        // with every earlier weight scaled by (1 - alpha) and the new
        // sample at weight 1.
        let deviation = sample - self.mean;
        self.mean = deviation.fma(self.inv_weight, self.mean);
        self.sum_sq_dev = self
            .one_minus_alpha
            .fma(self.sum_sq_dev, deviation * (sample - self.mean));
    }

    /// One more sample's worth of weight; cold once the totals settle.
    #[inline]
    fn advance_weights(&mut self) {
        let weight = self.one_minus_alpha.fma(self.weight, 1.0);
        let weight_sq = self.one_minus_alpha_sq.fma(self.weight_sq, 1.0);
        #[allow(clippy::float_cmp)]
        {
            self.settled = weight == self.weight && weight_sq == self.weight_sq;
        }
        self.weight = weight;
        self.weight_sq = weight_sq;
        self.inv_weight = 1.0 / weight;
        // Infinite for the first sample (one weight leaves no degree of
        // freedom); `min_samples >= 2` keeps that reading from being taken.
        self.variance_scale = 1.0 / weight_sq.fma(-self.inv_weight, weight);
    }

    /// Sets the as-built state: empty, or converged on the seed.
    fn start(&mut self) {
        if let Some(seed) = self.seed {
            // The limits of the weight totals: 1 / alpha and
            // 1 / (1 - (1 - alpha)^2).
            self.weight = 1.0 / self.alpha;
            self.weight_sq = 1.0 / (1.0 - self.one_minus_alpha_sq);
            self.inv_weight = self.alpha;
            self.variance_scale = 1.0 / self.weight_sq.fma(-self.inv_weight, self.weight);
            self.settled = true;
            self.mean = seed.mean;
            self.sum_sq_dev = seed.variance / self.variance_scale;
        } else {
            self.weight = 0.0;
            self.weight_sq = 0.0;
            self.inv_weight = 0.0;
            self.variance_scale = 0.0;
            self.settled = false;
            self.mean = 0.0;
            self.sum_sq_dev = 0.0;
        }
    }
}

impl EwmaVarBuilder {
    /// Direct smoothing factor. Must be in (0, 1) exclusive.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Samples for weight to decay by half. Must be positive and finite.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Span in samples (the pandas `span` convention, `alpha = 2 / (n + 1)`).
    /// Must be at least 2.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(EwWeight::Span(n));
        self
    }

    /// Minimum samples before a reading is returned. Default and minimum: 2
    /// (one sample has no variance).
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Pre-loads the mean and variance from calibration data.
    ///
    /// When seeded, a reading is available immediately (`min_samples` no
    /// longer applies), new samples are blended in as if the tracker had
    /// already converged, and `reset()` returns to the seed.
    #[inline]
    #[must_use]
    pub fn seed(mut self, mean: f64, variance: f64) -> Self {
        self.seed = Some((mean, variance));
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
    ///   mean and a finite non-negative variance. (A seed beyond
    ///   [`INPUT_LIMIT`](crate::INPUT_LIMIT), or a variance beyond its
    ///   square, is accepted and can overflow like any such input.)
    #[inline]
    pub fn build(self) -> Result<EwmaVar, crate::ConfigError> {
        let alpha = self
            .weight
            .ok_or(crate::ConfigError::Missing("alpha"))?
            .resolve()?;
        if self.min_samples < 2 {
            return Err(crate::ConfigError::Invalid(
                "min_samples must be >= 2: one sample has no variance",
            ));
        }
        if let Some((mean, variance)) = self.seed
            && (!mean.is_finite() || !crate::math::nonnegative_finite(variance))
        {
            return Err(crate::ConfigError::Invalid(
                "seed needs a finite mean and a finite non-negative variance",
            ));
        }
        let one_minus_alpha = 1.0 - alpha;
        let mut tracker = EwmaVar {
            alpha,
            one_minus_alpha,
            one_minus_alpha_sq: one_minus_alpha * one_minus_alpha,
            mean: 0.0,
            sum_sq_dev: 0.0,
            weight: 0.0,
            weight_sq: 0.0,
            inv_weight: 0.0,
            variance_scale: 0.0,
            settled: false,
            count: 0,
            prime_at: if self.seed.is_some() {
                0
            } else {
                self.min_samples
            },
            seed: self
                .seed
                .map(|(mean, variance)| MeanVariance { mean, variance }),
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
        let mut ew = EwmaVar::builder().alpha(0.5).build().unwrap();
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
            let mut ew = EwmaVar::builder().alpha(alpha).build().unwrap();
            for (i, &x) in samples.iter().enumerate() {
                let got = ew.update(x);
                if i == 0 {
                    assert_eq!(got, None);
                    continue;
                }
                let want = reference(&samples[..=i], alpha);
                let got = got.unwrap();
                assert!(
                    close(got.mean, want.mean) && close(got.variance, want.variance),
                    "alpha {alpha} step {i}: {got:?} vs {want:?}"
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
        let mut ew = EwmaVar::builder().alpha(0.1).build().unwrap();
        let _ = ew.update(samples[0]);
        for (x, (mean, variance)) in samples[1..].iter().zip(want) {
            let r = ew.update(*x).unwrap();
            assert!(close(r.mean, mean) && close(r.variance, variance), "{r:?}");
        }
    }

    #[test]
    fn unchanged_once_the_weights_settle() {
        // After settling, readings still follow the defining formulas: the
        // frozen reciprocals are the limits, not stale values.
        let alpha = 0.5;
        let mut ew = EwmaVar::builder().alpha(alpha).build().unwrap();
        let mut window = [0.0f64; 64];
        for i in 0..5_000u32 {
            let x = f64::from(i * 7 % 13);
            window.copy_within(1.., 0);
            window[63] = x;
            let _ = ew.update(x);
        }
        assert!(ew.settled);
        // At alpha 0.5 the 64 newest samples carry all the weight an f64
        // can resolve.
        let want = reference(&window, alpha);
        let got = ew.last().unwrap();
        assert!(
            close(got.mean, want.mean) && close(got.variance, want.variance),
            "{got:?} vs {want:?}"
        );
    }

    #[test]
    fn constant_input_has_zero_variance() {
        let mut ew = EwmaVar::builder().alpha(0.1).build().unwrap();
        for _ in 0..200 {
            let _ = ew.update(100.0);
        }
        let r = ew.last().unwrap();
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
        let mut ew = EwmaVar::builder()
            .alpha(0.1)
            .min_samples(50)
            .seed(100.0, 25.0)
            .build()
            .unwrap();
        assert!(ew.is_primed());
        assert_eq!(ew.count(), 0);
        let r = ew.last().unwrap();
        assert!(close(r.mean, 100.0) && close(r.variance, 25.0), "{r:?}");
        // A sample is blended at the converged weight, alpha.
        let r = ew.update(110.0).unwrap();
        assert!(close(r.mean, 101.0), "{r:?}");
        assert_eq!(ew.count(), 1);
        ew.reset();
        assert_eq!(ew.count(), 0);
        let r = ew.last().unwrap();
        assert!(close(r.mean, 100.0) && close(r.variance, 25.0), "{r:?}");
    }

    #[test]
    fn a_seed_evolves_as_a_converged_tracker_would() {
        // Converge an unseeded tracker on a long stream, seed a second one
        // with its reading, then feed both the same samples: they agree.
        let alpha = 0.2;
        let mut warm = EwmaVar::builder().alpha(alpha).build().unwrap();
        for i in 0..2_000u32 {
            let _ = warm.update(50.0 + f64::from(i * 7 % 13));
        }
        assert!(warm.settled);
        let at = warm.last().unwrap();
        let mut seeded = EwmaVar::builder()
            .alpha(alpha)
            .seed(at.mean, at.variance)
            .build()
            .unwrap();
        for x in [48.0, 61.0, 55.5, 30.0, 58.0] {
            let (a, b) = (warm.update(x).unwrap(), seeded.update(x).unwrap());
            assert!(
                close(a.mean, b.mean) && close(a.variance, b.variance),
                "{a:?} {b:?}"
            );
        }
    }

    #[test]
    fn weights_settle_across_the_alpha_range() {
        // The frozen reciprocals keep matching the defining formulas: checked
        // against a second tracker that is never allowed to settle.
        for alpha in [0.01, 0.1, 0.9] {
            let mut ew = EwmaVar::builder().alpha(alpha).build().unwrap();
            let mut never = ew.clone();
            let mut settled_at = None;
            for i in 0..8_000u32 {
                let x = f64::from(i * 31 % 17) - 8.0;
                let a = ew.update(x);
                never.settled = false;
                let b = never.update(x);
                if let (Some(a), Some(b)) = (a, b) {
                    assert!(
                        close(a.mean, b.mean) && close(a.variance, b.variance),
                        "{alpha} {i}"
                    );
                }
                if ew.settled && settled_at.is_none() {
                    settled_at = Some(i);
                }
            }
            // Within the documented bound of about 36 / alpha samples.
            let bound = (40.0 / alpha) as u32;
            assert!(
                settled_at.is_some_and(|n| n <= bound),
                "{alpha}: {settled_at:?}"
            );
        }
    }

    #[test]
    fn unseeded_reset_starts_over() {
        let mut ew = EwmaVar::builder().alpha(0.5).build().unwrap();
        for x in [5.0, 9.0, 1.0] {
            let _ = ew.update(x);
        }
        ew.reset();
        assert_eq!(ew.count(), 0);
        assert_eq!(ew.last(), None);
        assert_eq!(ew.update(0.0), None);
        let r = ew.update(2.0).unwrap();
        assert!(close(r.mean, 4.0 / 3.0) && close(r.variance, 2.0), "{r:?}");
    }

    #[test]
    fn min_samples_withholds_the_reading() {
        let mut ew = EwmaVar::builder()
            .alpha(0.1)
            .min_samples(5)
            .build()
            .unwrap();
        for i in 0..4 {
            assert_eq!(ew.update(f64::from(i)), None);
            assert!(!ew.is_primed());
        }
        assert!(ew.update(4.0).is_some());
    }

    #[test]
    fn builder_validation() {
        use crate::ConfigError::{Invalid, Missing};
        let b = EwmaVar::builder;
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
    fn rejects_nan_and_inf() {
        let mut ew = EwmaVar::builder().alpha(0.1).build().unwrap();
        assert_eq!(
            ew.checked_update(f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        assert_eq!(
            ew.checked_update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(ew.count(), 0);
    }
}
