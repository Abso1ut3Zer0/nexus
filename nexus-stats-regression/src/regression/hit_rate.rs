use nexus_stats_core::math::EwWeight;
use nexus_stats_smoothing::Ema;

/// Directional accuracy: the fraction of predictions whose sign matched the
/// outcome.
///
/// Keeps two rates: the cumulative one, `hits / total`, and an
/// exponentially weighted one for recency.
///
/// A hit is a prediction and an outcome that are both positive or both
/// negative. A zero on either side has no direction and counts as a miss.
/// This is the hit rate of Pesaran and Timmermann (1992, "A Simple
/// Nonparametric Test of Predictive Performance", *Journal of Business &
/// Economic Statistics*), which they restate (2009, *Journal of the
/// American Statistical Association*) as the share of pairs with
/// `prediction * outcome > 0`. Some implementations count zero against zero
/// as a hit; this one does not. The exponentially weighted rate is an
/// addition of this crate.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::regression::HitRate;
///
/// let mut hits = HitRate::builder().alpha(0.5).build().unwrap();
/// hits.update(1.0, 0.5); // both up: a hit
/// hits.update(1.0, -0.5); // predicted up, went down: a miss
/// assert_eq!(hits.hit_rate(), Some(0.5));
/// assert_eq!(hits.ew_hit_rate(), Some(0.5));
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
    weight: Option<EwWeight>,
}

impl HitRate {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> HitRateBuilder {
        HitRateBuilder { weight: None }
    }

    /// Feeds a predicted and a realized direction. Only their signs are
    /// used.
    ///
    /// Does not validate its inputs; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, predicted: f64, realized: f64) {
        // Signs, not `predicted * realized > 0.0`: the product of two tiny
        // values underflows to zero.
        //
        // PERF: not short-circuited, so four flag tests and no jumps on data
        // the predictor cannot learn.
        #[allow(clippy::needless_bitwise_bool)]
        #[inline]
        fn same_sign(a: f64, b: f64) -> bool {
            ((a > 0.0) & (b > 0.0)) | ((a < 0.0) & (b < 0.0))
        }

        let hit = same_sign(predicted, realized);
        self.total += 1;
        self.hits += u64::from(hit);
        self.ew_hits.update(nexus_stats_core::math::indicator(hit));
    }

    /// Checked update. Feeds the pair, or returns an error and leaves the
    /// tracker unchanged if either value is NaN or infinite.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber) if either
    ///   value is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if either value
    ///   is infinite.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::DataError;
    /// use nexus_stats_regression::regression::HitRate;
    ///
    /// let mut hits = HitRate::builder().alpha(0.5).build().unwrap();
    /// assert_eq!(hits.checked_update(1.0, 0.5), Ok(()));
    /// assert_eq!(hits.checked_update(f64::NAN, 0.5), Err(DataError::NotANumber));
    /// assert_eq!(hits.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(
        &mut self,
        predicted: f64,
        realized: f64,
    ) -> Result<(), nexus_stats_core::DataError> {
        nexus_stats_core::math::check_inputs!(predicted, realized)?;
        self.update(predicted, realized);
        Ok(())
    }

    /// Cumulative hit rate, `hits / total`, or `None` before any pair.
    #[must_use]
    pub fn hit_rate(&self) -> Option<f64> {
        if self.total == 0 {
            return None;
        }
        Some(self.hits as f64 / self.total as f64)
    }

    /// Exponentially weighted hit rate, or `None` before any pair.
    #[must_use]
    pub fn ew_hit_rate(&self) -> Option<f64> {
        self.ew_hits.value()
    }

    /// Number of pairs fed.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total
    }

    /// Whether a pair has been fed.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.total > 0
    }

    /// Resets to no pairs. Parameters unchanged.
    pub fn reset(&mut self) {
        self.hits = 0;
        self.total = 0;
        self.ew_hits.reset();
    }
}

impl HitRateBuilder {
    /// Direct smoothing factor for the weighted rate. Must be in (0, 1)
    /// exclusive.
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Pairs for weight to decay by half. Must be positive and finite.
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Span in pairs (`alpha = 2 / (n + 1)`). Must be at least 2.
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(EwWeight::Span(n));
        self
    }

    /// Builds the tracker.
    ///
    /// # Errors
    ///
    /// - `Missing("alpha")` if none of `alpha`, `halflife`, `span` was set.
    /// - `Invalid` if the weight is out of range; the message names the knob
    ///   set.
    pub fn build(self) -> Result<HitRate, nexus_stats_core::ConfigError> {
        let alpha = self
            .weight
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?
            .resolve()?;
        Ok(HitRate {
            hits: 0,
            total: 0,
            ew_hits: Ema::builder().alpha(alpha).build()?,
        })
    }
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
    fn only_strictly_matching_signs_are_hits() {
        // (predicted, realized, hit)
        let cases = [
            (2.0, 0.1, true),
            (-2.0, -0.1, true),
            (2.0, -0.1, false),
            (-2.0, 0.1, false),
            (0.0, 0.0, false),
            (-0.0, -1.0, false),
            // Same sign, but the product underflows to zero.
            (1e-200, 1e-200, true),
            (-1e-200, -1e-200, true),
        ];
        for (predicted, realized, hit) in cases {
            let mut hr = HitRate::builder().alpha(0.5).build().unwrap();
            hr.update(predicted, realized);
            let expected = if hit { 1.0 } else { 0.0 };
            assert_eq!(hr.hit_rate(), Some(expected), "{predicted} {realized}");
            assert_eq!(hr.ew_hit_rate(), Some(expected), "{predicted} {realized}");
        }
    }

    #[test]
    fn the_weighted_rate_follows_recent_pairs() {
        let mut hr = HitRate::builder().alpha(0.5).build().unwrap();
        hr.update(1.0, 1.0);
        hr.update(1.0, 1.0);
        hr.update(1.0, -1.0);
        // Cumulative 2/3; weighted 0.5 * 0 + 0.5 * 1.
        assert_eq!(hr.hit_rate(), Some(2.0 / 3.0));
        assert_eq!(hr.ew_hit_rate(), Some(0.5));
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use nexus_stats_core::DataError::{Infinite, NotANumber};

        let mut hr = HitRate::builder().alpha(0.5).build().unwrap();
        hr.checked_update(1.0, 1.0).unwrap();
        let before = (hr.count(), hr.hit_rate(), hr.ew_hit_rate());

        assert_eq!(hr.checked_update(f64::NAN, 1.0), Err(NotANumber));
        assert_eq!(hr.checked_update(1.0, f64::NAN), Err(NotANumber));
        assert_eq!(hr.checked_update(f64::INFINITY, 1.0), Err(Infinite));
        assert_eq!(hr.checked_update(1.0, f64::NEG_INFINITY), Err(Infinite));

        assert_eq!((hr.count(), hr.hit_rate(), hr.ew_hit_rate()), before);
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = HitRate::builder().alpha(0.2).build().unwrap();
        let mut unchecked = checked.clone();
        for (p, r) in [(1.0, 2.0), (-1.0, 2.0), (0.0, 1.0), (-3.0, -0.5)] {
            checked.checked_update(p, r).unwrap();
            unchecked.update(p, r);
        }
        assert_eq!(checked.count(), unchecked.count());
        assert_eq!(checked.hit_rate(), unchecked.hit_rate());
        assert_eq!(checked.ew_hit_rate(), unchecked.ew_hit_rate());
    }

    #[test]
    fn update_does_not_validate() {
        // NaN compares false both ways: it is counted, as a miss.
        let mut hr = HitRate::builder().alpha(0.5).build().unwrap();
        hr.update(f64::NAN, 1.0);
        assert_eq!((hr.count(), hr.hit_rate()), (1, Some(0.0)));
    }

    #[test]
    fn a_bad_knob_is_reported_under_its_own_name() {
        use nexus_stats_core::ConfigError::{Invalid, Missing};
        let b = HitRate::builder;
        assert_eq!(b().build().unwrap_err(), Missing("alpha"));
        assert_eq!(
            b().span(1).build().unwrap_err(),
            Invalid("span must be at least 2")
        );
        assert_eq!(b().span(3).build().unwrap().hit_rate(), None);
    }
}
