use crate::smoothing::Ema;

/// Fraction of directionally correct predictions with exponential weighting.
///
/// Tracks both a cumulative hit rate (hits / total) and an exponentially
/// weighted hit rate for recency. A "hit" is when `predicted_direction`
/// and `realized_direction` have the same sign.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::HitRate;
///
/// let mut hr = HitRate::builder()
///     .halflife(50.0)
///     .build()
///     .unwrap();
///
/// // Correct prediction: both positive
/// hr.update(1.0, 0.5);
/// assert!((hr.hit_rate().unwrap() - 1.0).abs() < f64::EPSILON);
/// ```
#[derive(Debug, Clone)]
pub struct HitRate {
    hits: u64,
    total: u64,
    ew_hits: Ema,
}

/// Builder for [`HitRate`].
#[derive(Debug, Clone)]
pub struct HitRateBuilder {
    alpha: Option<f64>,
}

impl HitRate {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> HitRateBuilder {
        HitRateBuilder { alpha: None }
    }

    /// Feed a prediction and realized direction.
    ///
    /// A "hit" is recorded when both values have the same sign (both
    /// positive or both negative). Zero is treated as no direction: if
    /// either is zero, it counts as a miss.
    ///
    /// Unchecked: a NaN on either side has no sign and counts as a miss.
    /// Use [`checked_update`](Self::checked_update) to have it refused
    /// instead. (Only signs are used, so no magnitude can overflow.)
    #[inline]
    pub fn update(&mut self, predicted_direction: f64, realized_direction: f64) {
        self.total += 1;
        let is_hit = same_sign(predicted_direction, realized_direction);
        self.hits += u64::from(is_hit);
        let _ = self.ew_hits.fold(crate::math::indicator(is_hit));
    }

    /// [`update`](Self::update) with both values validated first: refuses a
    /// NaN or an infinity and leaves the state untouched.
    ///
    /// # Errors
    ///
    /// `DataError::NotANumber` or `DataError::Infinite` for either value.
    #[inline]
    pub fn checked_update(
        &mut self,
        predicted_direction: f64,
        realized_direction: f64,
    ) -> Result<(), crate::DataError> {
        check_finite!(predicted_direction);
        check_finite!(realized_direction);
        self.update(predicted_direction, realized_direction);
        Ok(())
    }

    /// Cumulative hit rate (hits / total), or `None` before any observation:
    /// a rate over nothing is undefined, not zero.
    #[inline]
    #[must_use]
    pub fn hit_rate(&self) -> Option<f64> {
        (self.total > 0).then(|| self.hits as f64 / self.total as f64)
    }

    /// Exponentially weighted hit rate for recency, or `None` before any
    /// observation.
    #[inline]
    #[must_use]
    pub fn ew_hit_rate(&self) -> Option<f64> {
        self.ew_hits.value()
    }

    /// Total number of observations.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total
    }

    /// Whether enough observations have been fed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.total > 0
    }

    /// Reset all state.
    pub fn reset(&mut self) {
        self.hits = 0;
        self.total = 0;
        self.ew_hits.reset();
    }
}

impl HitRateBuilder {
    /// EW halflife in observations. One of `halflife` or `alpha` is required.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.alpha = Some(crate::math::alpha_from_halflife(halflife));
        self
    }

    /// Direct smoothing factor for the EW hit rate. Must be in (0, 1).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Build the hit rate tracker.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if no smoothing factor was set.
    #[inline]
    pub fn build(self) -> Result<HitRate, crate::ConfigError> {
        let alpha = self.alpha.ok_or(crate::ConfigError::Missing("alpha"))?;

        let ew_hits = Ema::builder().alpha(alpha).build()?;

        Ok(HitRate {
            hits: 0,
            total: 0,
            ew_hits,
        })
    }
}

/// Whether both values are strictly positive or both strictly negative.
///
/// Non-short-circuit on purpose: four flag tests instead of four jumps on
/// data the branch predictor cannot learn.
#[inline]
#[allow(clippy::needless_bitwise_bool)]
fn same_sign(a: f64, b: f64) -> bool {
    ((a > 0.0) & (b > 0.0)) | ((a < 0.0) & (b < 0.0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_correct() {
        let mut hr = HitRate::builder().alpha(0.1).build().unwrap();
        for _ in 0..100 {
            hr.update(1.0, 1.0);
        }
        assert!((hr.hit_rate().unwrap() - 1.0).abs() < f64::EPSILON);
        assert!(hr.ew_hit_rate().unwrap() > 0.99);
    }

    #[test]
    fn all_wrong() {
        let mut hr = HitRate::builder().alpha(0.1).build().unwrap();
        for _ in 0..100 {
            hr.update(1.0, -1.0);
        }
        assert!(hr.hit_rate().unwrap().abs() < f64::EPSILON);
        assert!(hr.ew_hit_rate().unwrap() < 0.01);
    }

    #[test]
    fn mixed_directions() {
        let mut hr = HitRate::builder().alpha(0.1).build().unwrap();
        // 5 hits, 5 misses
        for i in 0..10 {
            if i < 5 {
                hr.update(1.0, 1.0);
            } else {
                hr.update(1.0, -1.0);
            }
        }
        assert!((hr.hit_rate().unwrap() - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn zero_treated_as_miss() {
        let mut hr = HitRate::builder().alpha(0.1).build().unwrap();
        hr.update(0.0, 1.0);
        assert!(hr.hit_rate().unwrap().abs() < f64::EPSILON);
        hr.update(1.0, 0.0);
        assert!(hr.hit_rate().unwrap().abs() < f64::EPSILON);
    }

    #[test]
    fn priming() {
        let hr = HitRate::builder().alpha(0.1).build().unwrap();
        assert!(!hr.is_primed());
        assert_eq!(hr.count(), 0);
    }

    #[test]
    fn reset_clears_state() {
        let mut hr = HitRate::builder().alpha(0.1).build().unwrap();
        hr.update(1.0, 1.0);
        hr.reset();
        assert_eq!(hr.count(), 0);
        assert!(!hr.is_primed());
        assert!(hr.hit_rate().is_none());
        assert!(hr.ew_hit_rate().is_none());
    }

    #[test]
    fn nan_rejected() {
        let mut hr = HitRate::builder().alpha(0.1).build().unwrap();
        assert!(hr.checked_update(f64::NAN, 1.0).is_err());
        assert!(hr.checked_update(1.0, f64::NAN).is_err());
    }

    #[test]
    fn inf_rejected() {
        let mut hr = HitRate::builder().alpha(0.1).build().unwrap();
        assert!(hr.checked_update(f64::INFINITY, 1.0).is_err());
    }
}
