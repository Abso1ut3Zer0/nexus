/// Policy for when to close a bucket and start a new one.
#[derive(Debug, Clone, Copy)]
pub enum BucketPolicy {
    /// Close after N observations.
    Count(u64),
    /// Close after accumulating this much volume.
    Volume(f64),
    /// Close once the stamps passed to `update_at` span this many ticks
    /// (any unit; the caller's clock).
    Ticks(u64),
}

/// Summary of a closed bucket.
#[derive(Debug, Clone, Copy)]
pub struct BucketSummary {
    sum: f64,
    count: u64,
    first: f64,
    last: f64,
}

impl BucketSummary {
    /// Sum of all observations in the bucket.
    #[inline]
    #[must_use]
    pub fn sum(&self) -> f64 {
        self.sum
    }

    /// Number of observations in the bucket.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Mean of observations in the bucket.
    #[inline]
    #[must_use]
    pub fn mean(&self) -> f64 {
        self.sum / self.count as f64
    }

    /// First observation in the bucket.
    #[inline]
    #[must_use]
    pub fn first(&self) -> f64 {
        self.first
    }

    /// Last observation in the bucket.
    #[inline]
    #[must_use]
    pub fn last(&self) -> f64 {
        self.last
    }

    /// Change from first to last observation.
    #[inline]
    #[must_use]
    pub fn change(&self) -> f64 {
        self.last - self.first
    }
}

/// Accumulates observations into time/count/volume-based buckets.
///
/// Tracks sum, count, first, last for each bucket. On close, the user
/// reads whichever summary they need (mean, sum, count, change).
/// No prediction logic — that's composition with `LaggedPredictor` or
/// `EwLinearRegression`.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::{BucketAccumulator, BucketPolicy};
///
/// let mut bucket = BucketAccumulator::builder()
///     .policy(BucketPolicy::Count(10))
///     .build().unwrap();
///
/// let mut closures = 0;
/// for i in 0..25 {
///     if let Ok(Some(_summary)) = bucket.update(i as f64) {
///         closures += 1;
///     }
/// }
/// assert_eq!(closures, 2); // 10 + 10, then 5 still open
/// ```
#[derive(Debug, Clone)]
pub struct BucketAccumulator {
    policy: BucketPolicy,
    sum: f64,
    count: u64,
    first: f64,
    last: f64,
    accumulated_volume: f64,
    start_nanos: u64,
}

/// Builder for [`BucketAccumulator`].
#[derive(Debug, Clone)]
pub struct BucketAccumulatorBuilder {
    policy: Option<BucketPolicy>,
}

impl BucketAccumulator {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> BucketAccumulatorBuilder {
        BucketAccumulatorBuilder { policy: None }
    }

    /// Feed an observation (Count policy).
    ///
    /// Returns `Some(summary)` when the bucket closes.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if the value is NaN or infinite.
    #[inline]
    pub fn update(&mut self, value: f64) -> Result<Option<BucketSummary>, crate::DataError> {
        check_finite!(value);
        self.accumulate(value);

        let should_close = match self.policy {
            BucketPolicy::Count(n) => self.count >= n,
            _ => false,
        };

        if should_close {
            Ok(Some(self.close_inner()))
        } else {
            Ok(None)
        }
    }

    /// Feed an observation with volume (Volume policy).
    ///
    /// Returns `Some(summary)` when accumulated volume reaches the threshold.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if the value is NaN or infinite, or if volume
    /// is negative, NaN, or infinite.
    #[inline]
    pub fn update_volume(
        &mut self,
        value: f64,
        volume: f64,
    ) -> Result<Option<BucketSummary>, crate::DataError> {
        check_finite!(value);
        check_finite!(volume);
        if volume < 0.0 {
            return Err(crate::DataError::Negative);
        }
        self.accumulate(value);

        let should_close = match self.policy {
            BucketPolicy::Volume(threshold) => {
                self.accumulated_volume += volume;
                self.accumulated_volume >= threshold
            }
            _ => false,
        };

        if should_close {
            Ok(Some(self.close_inner()))
        } else {
            Ok(None)
        }
    }

    /// Feed an observation stamped with the caller's `u64` ticks (any unit,
    /// the `Ticks` policy).
    ///
    /// Returns `Some(summary)` when elapsed time reaches the threshold.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if the value is NaN or infinite.
    #[inline]
    pub fn update_at(
        &mut self,
        value: f64,
        timestamp: u64,
    ) -> Result<Option<BucketSummary>, crate::DataError> {
        check_finite!(value);
        self.accumulate(value);

        let should_close = match self.policy {
            BucketPolicy::Ticks(duration) => {
                if self.count == 1 {
                    // First observation — record start time.
                    self.start_nanos = timestamp;
                    false
                } else {
                    timestamp.saturating_sub(self.start_nanos) >= duration
                }
            }
            _ => false,
        };

        if should_close {
            Ok(Some(self.close_inner()))
        } else {
            Ok(None)
        }
    }

    /// Force close the current bucket and return its summary.
    /// Returns `None` if the bucket is empty.
    #[inline]
    pub fn close(&mut self) -> Option<BucketSummary> {
        if self.count == 0 {
            return None;
        }
        Some(self.close_inner())
    }

    #[inline]
    fn accumulate(&mut self, value: f64) {
        if self.count == 0 {
            self.first = value;
        }
        self.last = value;
        self.sum += value;
        self.count += 1;
    }

    fn close_inner(&mut self) -> BucketSummary {
        let summary = BucketSummary {
            sum: self.sum,
            count: self.count,
            first: self.first,
            last: self.last,
        };
        self.sum = 0.0;
        self.count = 0;
        self.first = 0.0;
        self.last = 0.0;
        self.accumulated_volume = 0.0;
        self.start_nanos = 0;
        summary
    }

    /// Number of observations in the current (open) bucket.
    #[inline]
    #[must_use]
    pub fn current_count(&self) -> u64 {
        self.count
    }

    /// Sum of observations in the current (open) bucket.
    #[inline]
    #[must_use]
    pub fn current_sum(&self) -> f64 {
        self.sum
    }

    /// Whether the open bucket holds at least one sample.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Reset all state.
    pub fn reset(&mut self) {
        self.sum = 0.0;
        self.count = 0;
        self.first = 0.0;
        self.last = 0.0;
        self.accumulated_volume = 0.0;
        self.start_nanos = 0;
    }
}

impl BucketAccumulatorBuilder {
    /// Set the bucket closure policy. Required.
    #[inline]
    #[must_use]
    pub fn policy(mut self, policy: BucketPolicy) -> Self {
        self.policy = Some(policy);
        self
    }

    /// Build the accumulator.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Missing` if no policy was set.
    #[inline]
    pub fn build(self) -> Result<BucketAccumulator, crate::ConfigError> {
        let policy = self.policy.ok_or(crate::ConfigError::Missing("policy"))?;
        Ok(BucketAccumulator {
            policy,
            sum: 0.0,
            count: 0,
            first: 0.0,
            last: 0.0,
            accumulated_volume: 0.0,
            start_nanos: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn count_policy_closes_every_n() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Count(10))
            .build()
            .unwrap();

        let mut closure_count = 0u32;
        for i in 0..30 {
            if let Ok(Some(s)) = bucket.update(i as f64) {
                closure_count += 1;
                assert_eq!(s.count(), 10);
            }
        }
        assert_eq!(closure_count, 3);
    }

    #[test]
    fn volume_policy() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Volume(100.0))
            .build()
            .unwrap();

        let mut closures = 0;
        // 10 observations with volume 15 each = 150, closes at 100
        for _ in 0..10 {
            if let Ok(Some(_)) = bucket.update_volume(1.0, 15.0) {
                closures += 1;
            }
        }
        assert_eq!(closures, 1); // closed once at 105 cumulative
    }

    #[test]
    fn volume_negative_rejected() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Volume(100.0))
            .build()
            .unwrap();
        assert!(bucket.update_volume(1.0, -5.0).is_err());
    }

    #[test]
    fn wall_time_raw_policy() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Ticks(1_000_000_000)) // 1 second
            .build()
            .unwrap();

        // First observation at t=0
        assert!(bucket.update_at(1.0, 0).unwrap().is_none());
        // At t=500ms — not yet
        assert!(bucket.update_at(2.0, 500_000_000).unwrap().is_none());
        // At t=1.1s — closes
        let s = bucket.update_at(3.0, 1_100_000_000).unwrap().unwrap();
        assert_eq!(s.count(), 3);
        assert!((s.first() - 1.0).abs() < f64::EPSILON);
        assert!((s.last() - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn empty_close_returns_none() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Count(10))
            .build()
            .unwrap();
        assert!(bucket.close().is_none());
    }

    #[test]
    fn force_close() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Count(100))
            .build()
            .unwrap();
        bucket.update(1.0).unwrap();
        bucket.update(2.0).unwrap();
        bucket.update(3.0).unwrap();
        let s = bucket.close().unwrap();
        assert_eq!(s.count(), 3);
        assert!((s.mean() - 2.0).abs() < f64::EPSILON);
        assert!((s.change() - 2.0).abs() < f64::EPSILON);
    }

    #[test]
    fn summary_accessors() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Count(5))
            .build()
            .unwrap();
        let mut s = None;
        for i in 1..=5 {
            if let Ok(Some(summary)) = bucket.update(i as f64) {
                s = Some(summary);
            }
        }
        let s = s.expect("bucket should have closed at count=5");
        assert_eq!(s.count(), 5);
        assert!((s.sum() - 15.0).abs() < f64::EPSILON);
        assert!((s.mean() - 3.0).abs() < f64::EPSILON);
        assert!((s.first() - 1.0).abs() < f64::EPSILON);
        assert!((s.last() - 5.0).abs() < f64::EPSILON);
        assert!((s.change() - 4.0).abs() < f64::EPSILON);
    }

    #[test]
    fn reset_clears_state() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Count(10))
            .build()
            .unwrap();
        bucket.update(42.0).unwrap();
        assert_eq!(bucket.current_count(), 1);
        bucket.reset();
        assert_eq!(bucket.current_count(), 0);
        assert!((bucket.current_sum()).abs() < f64::EPSILON);
    }

    #[test]
    fn nan_rejected() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Count(10))
            .build()
            .unwrap();
        assert!(bucket.update(f64::NAN).is_err());
    }

    #[test]
    fn inf_rejected() {
        let mut bucket = BucketAccumulator::builder()
            .policy(BucketPolicy::Count(10))
            .build()
            .unwrap();
        assert!(bucket.update(f64::INFINITY).is_err());
    }
}
