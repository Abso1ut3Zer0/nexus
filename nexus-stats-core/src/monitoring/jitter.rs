use crate::Sample;
use crate::sample::EmaKernel;

/// Jitter tracker — smoothed absolute deviation between consecutive samples.
///
/// Internally tracks an EMA of absolute consecutive deltas and an EMA of
/// values for computing the jitter ratio. `Jitter<f64>` smooths with an
/// alpha (`alpha`, `halflife` or `span`), can be seeded, rejects NaN and
/// infinity and returns `Result`; `Jitter<i64>` smooths with the
/// fixed-point shift EMA (`span`, rounded to `2^k - 1`) and cannot fail.
///
/// # Use Cases
/// - Network jitter (variation in inter-packet delay)
/// - Latency jitter (variation in response times)
/// - Clock stability monitoring
///
/// # Weighting clock
///
/// Per `update` call: every sample counts the same. Correct when samples
/// are evenly spaced, or one per event where per-event weighting is wanted.
/// Never feed it from a loop whose iteration time depends on the quantity
/// being measured.
#[derive(Debug, Clone)]
pub struct Jitter<T: Sample> {
    deviation: T::Ema,
    mean: T::Ema,
    last_sample: T,
    last_deviation: T,
    count: u64,
    min_samples: u64,
}

/// Builder for [`Jitter`].
#[derive(Debug, Clone)]
pub struct JitterBuilder<T: Sample> {
    ema: Option<T::EmaConfig>,
    min_samples: u64,
    seed_value: Option<T>,
    seed_jitter: Option<T>,
}

impl<T: Sample> Jitter<T> {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> JitterBuilder<T> {
        JitterBuilder {
            ema: None,
            min_samples: 2,
            seed_value: None,
            seed_jitter: None,
        }
    }

    /// Smoothed jitter, or `None` until primed.
    #[inline]
    #[must_use]
    pub fn jitter(&self) -> Option<T> {
        if self.is_primed() {
            Some(self.deviation.value())
        } else {
            None
        }
    }

    /// Most recent absolute deviation, or `None` before the second sample.
    #[inline]
    #[must_use]
    pub fn last_deviation(&self) -> Option<T> {
        if self.count >= 2 {
            Some(self.last_deviation)
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

    /// Whether `min_samples` have been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets accumulated state. Configuration is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.deviation.reset();
        self.mean.reset();
        self.last_sample = T::ZERO;
        self.last_deviation = T::ZERO;
        self.count = 0;
    }

    /// Shared body: fold a sample, return the jitter once primed.
    #[inline]
    fn fold(&mut self, sample: T, abs_delta: impl FnOnce(T, T) -> T) -> Option<T> {
        self.count += 1;
        if self.count == 1 {
            self.last_sample = sample;
            self.mean.seed(sample);
            return None;
        }
        let dev = abs_delta(sample, self.last_sample);
        self.last_deviation = dev;
        self.last_sample = sample;
        self.deviation.fold(dev);
        self.mean.fold(sample);
        if self.is_primed() {
            Some(self.deviation.value())
        } else {
            None
        }
    }
}

impl Jitter<f64> {
    /// Feeds a sample. Returns the smoothed jitter once primed.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<f64>, crate::DataError> {
        check_finite!(sample);
        Ok(self.fold(sample, |a, b| (a - b).abs()))
    }

    /// Jitter relative to the smoothed level, `jitter / mean`, or `None`
    /// until primed or while the mean is zero.
    #[inline]
    #[must_use]
    pub fn jitter_ratio(&self) -> Option<f64> {
        let mean = self.mean.value();
        if self.is_primed() && mean.abs() > f64::EPSILON {
            Some(self.deviation.value() / mean)
        } else {
            None
        }
    }
}

impl Jitter<i64> {
    /// Feeds a sample. Returns the smoothed jitter once primed.
    #[inline]
    pub fn update(&mut self, sample: i64) -> Option<i64> {
        self.fold(sample, |a, b| (a - b).abs())
    }

    /// Jitter relative to the smoothed level, `jitter / mean`, or `None`
    /// until primed or while the mean is zero.
    #[inline]
    #[must_use]
    #[allow(clippy::cast_precision_loss)]
    pub fn jitter_ratio(&self) -> Option<f64> {
        let mean = self.mean.value();
        if self.is_primed() && mean != 0 {
            Some(self.deviation.value() as f64 / mean as f64)
        } else {
            None
        }
    }

    /// The span actually used, rounded to `2^k - 1`.
    #[inline]
    #[must_use]
    pub fn effective_span(&self) -> u64 {
        self.deviation.span
    }
}

impl<T: Sample> JitterBuilder<T> {
    /// Smoothing span in samples. For `f64` this sets `alpha = 2 / (n + 1)`;
    /// for `i64` it is rounded to `2^k - 1`.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.ema = Some(T::ema_config_from_span(n));
        self
    }

    /// Minimum samples before `jitter()` is reported. Default 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Pre-loads the level and the jitter from calibration data; the
    /// detector starts primed.
    #[inline]
    #[must_use]
    pub fn seed(mut self, value: T, jitter: T) -> Self {
        self.seed_value = Some(value);
        self.seed_jitter = Some(jitter);
        self
    }

    /// Builds the tracker.
    ///
    /// # Errors
    ///
    /// `ConfigError::Missing("alpha")` (`f64`) or `Missing("span")` (`i64`) if
    /// no smoothing was configured;
    /// `ConfigError::Invalid` if it is out of range (alpha outside (0, 1),
    /// span below 1).
    pub fn build(self) -> Result<Jitter<T>, crate::ConfigError> {
        let config = self
            .ema
            .ok_or(crate::ConfigError::Missing(T::EMA_CONFIG_NAME))?;
        // One sample has no deviation, so an unseeded Jitter cannot report
        // before its second; a seed supplies the deviation and may prime at one.
        let seeded = self.seed_value.is_some() && self.seed_jitter.is_some();
        let floor = if seeded { 1 } else { 2 };
        if self.min_samples < floor {
            return Err(crate::ConfigError::Invalid(
                "Jitter min_samples must be >= 2 unseeded, >= 1 seeded",
            ));
        }
        if let (Some(v), Some(j)) = (self.seed_value, self.seed_jitter)
            && (!v.is_finite() || !j.is_finite())
        {
            return Err(crate::ConfigError::Invalid("Jitter seed must be finite"));
        }
        let mut deviation = T::Ema::new(config)?;
        let mut mean = T::Ema::new(config)?;
        let (last_sample, count) = match (self.seed_value, self.seed_jitter) {
            (Some(v), Some(j)) => {
                mean.seed(v);
                deviation.seed(j);
                (v, self.min_samples)
            }
            _ => (T::ZERO, 0),
        };
        Ok(Jitter {
            deviation,
            mean,
            last_sample,
            last_deviation: T::ZERO,
            count,
            min_samples: self.min_samples,
        })
    }
}

impl JitterBuilder<f64> {
    /// Direct smoothing factor in (0, 1).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.ema = Some(alpha);
        self
    }

    /// Samples for a sample's weight to decay by half.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.ema = Some(1.0 - crate::math::exp(-core::f64::consts::LN_2 / halflife));
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // #763: with `min_samples(1)` the seeded jitter used to be discarded
    // (the old code inferred "first real sample" from `count`). The kernel
    // now carries an explicit seeded state: 0.3 * 10 + 0.7 * 5 = 6.5.
    #[test]
    fn seeded_jitter_survives_min_samples_one() {
        let mut j = Jitter::<f64>::builder()
            .alpha(0.3)
            .min_samples(1)
            .seed(100.0, 5.0)
            .build()
            .unwrap();
        let out = j.update(110.0).unwrap().unwrap();
        assert!((out - 6.5).abs() < 1e-12, "{out}");
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn constant_input_zero_jitter() {
        let mut j = Jitter::<f64>::builder().alpha(0.3).build().unwrap();
        for _ in 0..100 {
            let _ = j.update(100.0).unwrap();
        }
        let jitter = j.jitter().unwrap();
        assert!(
            jitter.abs() < 1e-10,
            "constant input should have ~zero jitter, got {jitter}"
        );
    }

    #[test]
    fn alternating_input_high_jitter() {
        let mut j = Jitter::<f64>::builder().alpha(0.5).build().unwrap();
        for i in 0..50 {
            let _ = j.update(if i % 2 == 0 { 100.0 } else { 200.0 }).unwrap();
        }
        let jitter = j.jitter().unwrap();
        assert!(
            jitter > 50.0,
            "alternating input should have high jitter, got {jitter}"
        );
    }

    #[test]
    fn jitter_ratio_correctness() {
        let mut j = Jitter::<f64>::builder().alpha(0.3).build().unwrap();
        for i in 0..100 {
            let _ = j.update(100.0 + (i % 10) as f64).unwrap();
        }
        let ratio = j.jitter_ratio().unwrap();
        assert!(
            ratio > 0.0 && ratio < 1.0,
            "ratio should be reasonable, got {ratio}"
        );
    }

    #[test]
    fn priming() {
        let mut j = Jitter::<f64>::builder()
            .alpha(0.3)
            .min_samples(5)
            .build()
            .unwrap();
        for _ in 0..4 {
            assert!(j.update(100.0).unwrap().is_none());
        }
        assert!(j.update(100.0).unwrap().is_some());
    }

    #[test]
    fn reset() {
        let mut j = Jitter::<f64>::builder().alpha(0.3).build().unwrap();
        for _ in 0..10 {
            let _ = j.update(100.0).unwrap();
        }
        j.reset();
        assert_eq!(j.count(), 0);
        assert!(j.jitter().is_none());
    }

    #[test]
    fn i64_basic() {
        let mut j = Jitter::<i64>::builder().span(7).build().unwrap();
        let _ = j.update(100);
        let _ = j.update(110);
        let _ = j.update(105);
        assert!(j.jitter().is_some());
    }

    #[test]
    fn seeded_is_primed() {
        let j = Jitter::<f64>::builder()
            .alpha(0.3)
            .seed(100.0, 5.0)
            .build()
            .unwrap();

        assert!(j.is_primed());
        assert!((j.jitter().unwrap() - 5.0).abs() < 1e-10);
    }

    #[test]
    fn seeded_next_update_uses_seed_value() {
        let mut j = Jitter::<f64>::builder()
            .alpha(0.3)
            .seed(100.0, 5.0)
            .build()
            .unwrap();

        // Next update should compute deviation from seeded last_sample=100
        let result = j.update(110.0).unwrap();
        assert!(result.is_some());
        // Deviation is |110-100|=10, smoothed jitter = 0.3*10 + 0.7*5 = 6.5
        let jitter = result.unwrap();
        assert!((jitter - 6.5).abs() < 1e-10);
    }

    #[test]
    fn errors_without_alpha() {
        let result = Jitter::<f64>::builder().build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("alpha"))));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut j = Jitter::<f64>::builder().alpha(0.3).build().unwrap();
        assert!(matches!(
            j.update(f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
        assert!(matches!(
            j.update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        ));
        assert!(matches!(
            j.update(f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        ));
    }
}
