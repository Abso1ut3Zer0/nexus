/// Decaying accumulator — event-driven score with exponential decay.
///
/// Lazy evaluation: only computes decay when `update()` or `score()` is called.
/// Between calls, no work is done.
///
/// # Use Cases
/// - Weighted event scoring with temporal decay
/// - "How active has this been recently?"
/// - Rate limiting with smooth backoff
#[derive(Debug, Clone)]
pub struct DecayAccum {
    score: f64,
    last_time: u64,
    decay_constant: f64, // ln(2) / half_life
    initialized: bool,
    /// Updates since construction or `reset` (`score()` does not count).
    count: u64,
}

impl DecayAccum {
    /// Creates a new decaying accumulator with the given half-life.
    ///
    /// `half_life` is in the same time units as the timestamps passed to
    /// `update()` and `score()`.
    #[inline]
    pub fn new(half_life: f64) -> Result<Self, nexus_stats_core::ConfigError> {
        #[allow(clippy::neg_cmp_op_on_partial_ord)]
        if !(half_life > 0.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "half_life must be positive",
            ));
        }
        Ok(Self {
            score: 0.0,
            last_time: 0,
            decay_constant: core::f64::consts::LN_2 / half_life,
            initialized: false,
            count: 0,
        })
    }

    /// Updates with a weighted event at the given timestamp.
    ///
    /// Applies decay from the last event/query before adding.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if `weight` is NaN, or
    /// `DataError::Infinite` if it is infinite.
    #[inline]
    pub fn update(
        &mut self,
        timestamp: u64,
        weight: f64,
    ) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(weight);
        self.apply_decay(timestamp);
        self.score += weight;
        self.count += 1;
        Ok(())
    }

    /// Queries the current decayed score at the given timestamp.
    #[inline]
    #[must_use]
    pub fn score(&mut self, now: u64) -> f64 {
        self.apply_decay(now);
        self.score
    }

    #[inline]
    fn apply_decay(&mut self, timestamp: u64) {
        if !self.initialized {
            self.last_time = timestamp;
            self.initialized = true;
            return;
        }

        let dt = (timestamp.wrapping_sub(self.last_time) as i64) as f64;
        if dt > 0.0 {
            self.score *= nexus_stats_core::math::exp(-self.decay_constant * dt);
            self.last_time = timestamp;
        }
    }

    /// Samples processed since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one update has been applied.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets to zero score.
    #[inline]
    pub fn reset(&mut self) {
        self.score = 0.0;
        self.initialized = false;
        self.count = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accumulates() {
        let mut da = DecayAccum::new(10.0).unwrap();
        da.update(0, 1.0).unwrap();
        da.update(0, 1.0).unwrap();
        let s = da.score(0);
        assert!((s - 2.0).abs() < 1e-10);
    }

    #[test]
    fn decays_over_time() {
        let mut da = DecayAccum::new(10.0).unwrap();
        da.update(0, 100.0).unwrap();

        let s = da.score(10); // one half-life
        assert!(
            (s - 50.0).abs() < 1.0,
            "should be ~50 after one half-life, got {s}"
        );

        let s = da.score(20); // two half-lives
        assert!(
            (s - 25.0).abs() < 1.0,
            "should be ~25 after two half-lives, got {s}"
        );
    }

    #[test]
    fn lazy_evaluation() {
        let mut da = DecayAccum::new(10.0).unwrap();
        da.update(0, 100.0).unwrap();
        // No work done between calls
        da.update(5, 50.0).unwrap(); // decays 100 by 5 time units, adds 50

        let s = da.score(5);
        // After 5 units: 100 * exp(-ln2/10 * 5) + 50 ≈ 100 * 0.707 + 50 ≈ 120.7
        assert!(s > 100.0 && s < 130.0, "score should be ~120, got {s}");
    }

    #[test]
    fn reset() {
        let mut da = DecayAccum::new(10.0).unwrap();
        da.update(0, 100.0).unwrap();
        da.reset();
        let s = da.score(0);
        assert!((s).abs() < 1e-10);
    }

    #[test]
    fn rejects_zero_half_life() {
        assert!(matches!(
            DecayAccum::new(0.0),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn rejects_invalid_weight() {
        let mut da = DecayAccum::new(10.0).unwrap();
        assert!(matches!(
            da.update(0, f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        assert!(matches!(
            da.update(0, f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
    }
}
