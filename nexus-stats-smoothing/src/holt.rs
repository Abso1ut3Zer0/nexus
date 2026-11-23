use nexus_stats_core::math::{EwWeight, MulAdd, Warmup, Weight};

/// Holt's linear method: an exponentially weighted level and trend.
///
/// An average lags a signal that is trending. Holt's method tracks the
/// trend as well, so the level keeps up and the pair gives a forecast:
/// `level + steps * slope`.
///
/// The first sample is the level; the second sets the slope to the
/// difference. From then on, with weights `alpha` and `beta`:
///
/// ```text
/// level = alpha * sample + (1 - alpha) * (level + slope)
/// slope = beta * (level - previous level) + (1 - beta) * slope
/// ```
///
/// This is double exponential smoothing as given in
/// [Exponential smoothing](https://en.wikipedia.org/wiki/Exponential_smoothing).
///
/// # Choosing parameters
///
/// Start `alpha` where a plain EMA on the same data would have it, and
/// `beta` several times smaller: a trend that adapts as fast as the level
/// oscillates. If forecasts overshoot, lower `beta`. If the level lags,
/// raise `alpha`.
///
/// # Examples
///
/// ```
/// use nexus_stats_smoothing::Holt;
///
/// let mut holt = Holt::builder().alpha(0.5).beta(0.5).build().unwrap();
/// assert_eq!(holt.update(10.0), None); // one sample has no trend
/// let reading = holt.update(12.0).unwrap();
/// assert_eq!((reading.level, reading.slope), (12.0, 2.0));
/// assert_eq!(reading.forecast(3), 18.0);
/// ```
#[derive(Debug, Clone)]
pub struct Holt {
    level_weight: Weight,
    slope_weight: Weight,
    state: Trend,
    warmup: Warmup,
    /// What `reset` restores.
    seed: Option<Trend>,
}

/// A [`Holt`] reading: where the signal is and how fast it is moving.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Trend {
    /// The smoothed value.
    pub level: f64,
    /// The trend: the smoothed change per sample.
    pub slope: f64,
}

impl Trend {
    /// The placeholder state before any sample; never reported.
    const REST: Self = Self {
        level: 0.0,
        slope: 0.0,
    };

    /// The value expected `steps` samples ahead: `level + steps * slope`.
    #[must_use]
    pub fn forecast(&self, steps: u64) -> f64 {
        self.slope.fma(steps as f64, self.level)
    }
}

/// Builder for [`Holt`].
#[derive(Debug, Clone)]
pub struct HoltBuilder {
    alpha: Option<f64>,
    beta: Option<f64>,
    min_samples: u64,
    seed: Option<Trend>,
}

impl Holt {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> HoltBuilder {
        HoltBuilder {
            alpha: None,
            beta: None,
            min_samples: 2,
            seed: None,
        }
    }

    /// Feeds a sample. Returns the level and slope once primed.
    ///
    /// Does not validate `sample`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, sample: f64) -> Option<Trend> {
        let count = self.warmup.tick();
        if self.seed.is_none() && count <= 2 {
            self.start(sample, count);
        } else {
            self.step(sample);
        }
        self.reading()
    }

    /// Checked update. Feeds `sample`, or returns an error and leaves the
    /// state unchanged if `sample` is NaN or infinite.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `sample` is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if
    ///   `sample` is infinite.
    #[inline]
    pub fn checked_update(
        &mut self,
        sample: f64,
    ) -> Result<Option<Trend>, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_input(sample, f64::MAX)?;
        Ok(self.update(sample))
    }

    /// The level and slope, or `None` until primed.
    #[must_use]
    pub fn reading(&self) -> Option<Trend> {
        if !self.warmup.is_primed() {
            return None;
        }
        Some(self.state)
    }

    /// The value expected `steps` samples ahead, or `None` until primed.
    #[must_use]
    pub fn forecast(&self, steps: u64) -> Option<f64> {
        Some(self.reading()?.forecast(steps))
    }

    /// The level weight.
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.level_weight.alpha()
    }

    /// The trend weight.
    #[must_use]
    pub fn beta(&self) -> f64 {
        self.slope_weight.alpha()
    }

    /// Samples fed since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.warmup.count()
    }

    /// Whether a reading is available.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.warmup.is_primed()
    }

    /// Returns to the as-built state: no samples, and the seed if one was
    /// configured. Parameters unchanged.
    pub fn reset(&mut self) {
        self.state = self.seed.unwrap_or(Trend::REST);
        self.warmup.reset();
    }

    /// Resets to no samples, starting from `level` and `slope` as a new
    /// seed.
    ///
    /// The reading is available at once (`min_samples` no longer applies),
    /// and later calls to [`reset`](Self::reset) return to this seed.
    ///
    /// # Errors
    ///
    /// `Invalid` if either value is not finite. The state is left unchanged.
    pub fn reset_with_seed(
        &mut self,
        level: f64,
        slope: f64,
    ) -> Result<(), nexus_stats_core::ConfigError> {
        let seed = checked_seed(level, slope)?;
        self.seed = Some(seed);
        self.state = seed;
        self.warmup.reset_seeded();
        Ok(())
    }

    /// The published start of an unseeded smoother: the first sample is the
    /// level, and the second sets the slope to the difference.
    #[inline]
    fn start(&mut self, sample: f64, count: u64) {
        if count == 2 {
            self.state.slope = sample - self.state.level;
        }
        self.state.level = sample;
    }

    /// One step of Holt's recursion.
    #[inline]
    fn step(&mut self, sample: f64) {
        let Trend {
            level: previous,
            slope,
        } = self.state;
        let level = self.level_weight.blend(sample, previous + slope);
        self.state = Trend {
            level,
            slope: self.slope_weight.blend(level - previous, slope),
        };
    }
}

impl HoltBuilder {
    /// Level weight, in `(0, 1)`. Larger follows the samples more closely.
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Trend weight, in `(0, 1)`. Larger lets the slope change faster.
    #[must_use]
    pub fn beta(mut self, beta: f64) -> Self {
        self.beta = Some(beta);
        self
    }

    /// Samples before a reading is given. Default 2, the fewest that give
    /// a slope.
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Starts from a known level and slope, as if already converged there:
    /// the reading is available at once and the first sample is smoothed
    /// into it.
    #[must_use]
    pub fn seed(mut self, level: f64, slope: f64) -> Self {
        self.seed = Some(Trend { level, slope });
        self
    }

    /// Builds the smoother.
    ///
    /// # Errors
    ///
    /// - `Missing` if `alpha` or `beta` was not set.
    /// - `Invalid` if either is outside `(0, 1)`, if `min_samples` is below
    ///   2, or if the seed is not finite.
    pub fn build(self) -> Result<Holt, nexus_stats_core::ConfigError> {
        use nexus_stats_core::ConfigError::{Invalid, Missing};

        let alpha = EwWeight::Alpha(self.alpha.ok_or(Missing("alpha"))?).resolve()?;
        let beta = EwWeight::Alpha(self.beta.ok_or(Missing("beta"))?)
            .resolve()
            .map_err(|_| Invalid("beta must be in (0, 1)"))?;
        if self.min_samples < 2 {
            return Err(Invalid("min_samples must be >= 2"));
        }
        let seed = match self.seed {
            Some(seed) => Some(checked_seed(seed.level, seed.slope)?),
            None => None,
        };
        Ok(Holt {
            level_weight: Weight::new(alpha),
            slope_weight: Weight::new(beta),
            state: seed.unwrap_or(Trend::REST),
            warmup: Warmup::new(self.min_samples, seed.is_some()),
            seed,
        })
    }
}

/// A seed, if both parts are finite.
fn checked_seed(level: f64, slope: f64) -> Result<Trend, nexus_stats_core::ConfigError> {
    if !level.is_finite() || !slope.is_finite() {
        return Err(nexus_stats_core::ConfigError::Invalid(
            "seed must be finite",
        ));
    }
    Ok(Trend { level, slope })
}

#[cfg(test)]
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;
    use nexus_stats_core::ConfigError;
    use nexus_stats_core::DataError::{Infinite, NotANumber};

    fn holt(alpha: f64, beta: f64) -> Holt {
        Holt::builder().alpha(alpha).beta(beta).build().unwrap()
    }

    /// Holt's recursion written out from the published equations, with the
    /// published start: `s0 = x0`, `b0 = x1 - x0`.
    fn reference(samples: &[f64], alpha: f64, beta: f64) -> Vec<(f64, f64)> {
        let (mut level, mut slope) = (samples[0], samples[1] - samples[0]);
        let mut out = Vec::new();
        for &x in &samples[1..] {
            let previous = level;
            level = alpha * x + (1.0 - alpha) * (previous + slope);
            slope = beta * (level - previous) + (1.0 - beta) * slope;
            out.push((level, slope));
        }
        out
    }

    #[test]
    fn matches_the_published_recursion() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let samples: Vec<f64> = (0..400)
            .map(|i| {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                100.0 + 0.3 * f64::from(i) + (state % 1000) as f64 / 100.0
            })
            .collect();
        for (alpha, beta) in [(0.5, 0.5), (0.3, 0.1), (0.9, 0.05), (0.05, 0.9)] {
            let want = reference(&samples, alpha, beta);
            let mut h = holt(alpha, beta);
            assert_eq!(h.update(samples[0]), None);
            for (i, &x) in samples[1..].iter().enumerate() {
                let got = h.update(x).unwrap();
                let (level, slope) = want[i];
                let scale = level.abs().max(1.0);
                assert!((got.level - level).abs() <= 1e-12 * scale, "level at {i}");
                assert!((got.slope - slope).abs() <= 1e-12 * scale, "slope at {i}");
            }
        }
    }

    #[test]
    fn the_second_sample_gives_the_first_reading() {
        let mut h = holt(0.5, 0.5);
        assert_eq!(h.update(10.0), None);
        assert!(!h.is_primed());
        assert_eq!(
            h.update(12.0),
            Some(Trend {
                level: 12.0,
                slope: 2.0
            })
        );
        assert_eq!(h.forecast(3), Some(18.0));
    }

    #[test]
    fn a_straight_line_is_followed_exactly() {
        let mut h = holt(0.4, 0.2);
        for i in 0..200 {
            h.update(5.0 + 0.25 * f64::from(i));
        }
        let reading = h.reading().unwrap();
        assert!((reading.level - (5.0 + 0.25 * 199.0)).abs() < 1e-9);
        assert!((reading.slope - 0.25).abs() < 1e-12);
        assert!((reading.forecast(4) - (5.0 + 0.25 * 203.0)).abs() < 1e-9);
    }

    #[test]
    fn a_constant_has_no_slope() {
        let mut h = holt(0.3, 0.1);
        for _ in 0..100 {
            h.update(42.0);
        }
        assert_eq!(
            h.reading(),
            Some(Trend {
                level: 42.0,
                slope: 0.0
            })
        );
    }

    #[test]
    fn min_samples_delays_the_reading() {
        let mut h = Holt::builder()
            .alpha(0.5)
            .beta(0.5)
            .min_samples(4)
            .build()
            .unwrap();
        for x in [1.0, 2.0, 3.0] {
            assert_eq!(h.update(x), None);
        }
        assert!(h.update(4.0).is_some());
    }

    #[test]
    fn a_seed_gives_a_reading_at_once_and_smooths_the_first_sample_in() {
        let mut h = Holt::builder()
            .alpha(0.5)
            .beta(0.5)
            .seed(100.0, 1.0)
            .build()
            .unwrap();
        assert_eq!(
            h.reading(),
            Some(Trend {
                level: 100.0,
                slope: 1.0
            })
        );
        assert_eq!(h.count(), 0);
        // level = 0.5 * 103 + 0.5 * 101 = 102; slope = 0.5 * 2 + 0.5 * 1.
        assert_eq!(
            h.update(103.0),
            Some(Trend {
                level: 102.0,
                slope: 1.5
            })
        );
        h.reset();
        assert_eq!((h.count(), h.forecast(2)), (0, Some(102.0)));
    }

    #[test]
    fn reset_with_seed_replaces_the_start() {
        let mut h = holt(0.5, 0.5);
        h.update(1.0);
        h.reset_with_seed(50.0, -1.0).unwrap();
        assert_eq!(h.forecast(1), Some(49.0));
        h.update(60.0);
        h.reset();
        assert_eq!(h.forecast(0), Some(50.0));
        // A bad seed is refused and changes nothing.
        assert!(h.reset_with_seed(f64::NAN, 0.0).is_err());
        assert!(h.reset_with_seed(0.0, f64::INFINITY).is_err());
        assert_eq!(h.forecast(0), Some(50.0));
    }

    #[test]
    fn reset_without_a_seed_starts_over() {
        let mut h = holt(0.5, 0.5);
        h.update(10.0);
        h.update(20.0);
        h.reset();
        assert_eq!((h.reading(), h.count()), (None, 0));
        assert_eq!(h.update(7.0), None);
        assert_eq!(
            h.update(8.0),
            Some(Trend {
                level: 8.0,
                slope: 1.0
            })
        );
    }

    #[test]
    fn the_builder_checks_its_configuration() {
        let missing = |r: Result<Holt, ConfigError>| matches!(r, Err(ConfigError::Missing(_)));
        assert!(missing(Holt::builder().beta(0.5).build()));
        assert!(missing(Holt::builder().alpha(0.5).build()));
        for bad in [0.0, 1.0, -0.1, 1.5, f64::NAN, f64::INFINITY] {
            assert!(Holt::builder().alpha(bad).beta(0.5).build().is_err());
            assert!(Holt::builder().alpha(0.5).beta(bad).build().is_err());
        }
        for min in [0, 1] {
            let built = Holt::builder()
                .alpha(0.5)
                .beta(0.5)
                .min_samples(min)
                .build();
            assert!(built.is_err(), "min_samples {min}");
        }
        let seeded = Holt::builder().alpha(0.5).beta(0.5).seed(f64::NAN, 0.0);
        assert!(seeded.build().is_err());
    }

    #[test]
    fn checked_update_refuses_nan_and_infinity_and_changes_nothing() {
        let mut h = holt(0.5, 0.5);
        assert_eq!(h.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(h.count(), 0);
        h.checked_update(10.0).unwrap();
        h.checked_update(12.0).unwrap();
        let before = h.reading();
        assert_eq!(h.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(h.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(h.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!((h.reading(), h.count()), (before, 2));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let (mut checked, mut plain) = (holt(0.3, 0.2), holt(0.3, 0.2));
        for x in [5.0, -2.0, 1e150, -1e150, 0.0, 3.5, 1e-300] {
            assert_eq!(checked.checked_update(x), Ok(plain.update(x)));
        }
    }
}
