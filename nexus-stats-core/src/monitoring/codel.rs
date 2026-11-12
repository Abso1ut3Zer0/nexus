use crate::Condition;

// =========================================================================
// Raw (u64 timestamp) variants — no_std compatible
// =========================================================================

/// CoDel standing-queue detector (RFC 8289, Nichols & Jacobson).
///
/// Feed it each item's sojourn time (how long it waited in the queue) with
/// the dequeue timestamp. It reports `Degraded` only once sojourn has stayed
/// above `target` for a whole `window` (the RFC's *interval*): the first
/// sample above target starts the clock, a sample at or below target stops
/// it, and a sample above target a full window or more after the start is a
/// standing queue. A single slow item, or a burst shorter than the window,
/// is `Normal`.
///
/// State is one timestamp. `no_std` compatible.
///
/// # Weighting clock
///
/// Caller's timestamps. Any call rate; the interval is measured in ticks,
/// not samples. Ticks must be monotonic; a counter that wraps is fine as
/// long as the window and any real gap between samples fit in half its
/// range (elapsed time is computed with wrapping subtraction).
#[derive(Debug, Clone)]
pub struct CoDelI64 {
    target: i64,
    interval: u64,
    first_above: Option<u64>,
    elevated: bool,
    count: u64,
    min_samples: u64,
}

/// Builder for [`CoDelI64`].
#[derive(Debug, Clone)]
pub struct CoDelI64Builder {
    target: Option<i64>,
    window: Option<u64>,
    min_samples: u64,
}

impl CoDelI64 {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> CoDelI64Builder {
        CoDelI64Builder {
            target: None,
            window: None,
            min_samples: 1,
        }
    }

    /// Feeds a sojourn time at the given timestamp.
    ///
    /// Returns `Some(Condition)` once primed, `None` before.
    #[inline]
    #[must_use]
    pub fn update(&mut self, timestamp: u64, sojourn: i64) -> Option<Condition> {
        self.count += 1;
        self.elevated = standing_queue(
            &mut self.first_above,
            self.interval,
            timestamp,
            sojourn > self.target,
        );

        if self.count < self.min_samples {
            return None;
        }

        Some(if self.elevated {
            Condition::Degraded
        } else {
            Condition::Normal
        })
    }

    /// Convenience for `i64` timestamps (e.g., wire protocol epoch nanos).
    ///
    /// Timestamps must be non-negative. Negative values wrap to large
    /// `u64` values and will produce incorrect interval arithmetic.
    #[inline]
    #[must_use]
    pub fn update_i64(&mut self, timestamp: i64, sojourn: i64) -> Option<Condition> {
        debug_assert!(timestamp >= 0, "negative timestamp: {timestamp}");
        self.update(timestamp as u64, sojourn)
    }

    /// Whether the last sample found a standing queue (sojourn above target
    /// for a whole interval).
    #[inline]
    #[must_use]
    pub fn is_elevated(&self) -> bool {
        self.elevated
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the monitor has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to empty state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.first_above = None;
        self.elevated = false;
        self.count = 0;
    }
}

impl CoDelI64Builder {
    /// Target sojourn time. Samples above it count toward a standing queue.
    #[inline]
    #[must_use]
    pub fn target(mut self, target: i64) -> Self {
        self.target = Some(target);
        self
    }

    /// Interval (RFC 8289): how long sojourn must stay above target before
    /// the queue counts as standing. Same units as the timestamps.
    #[inline]
    #[must_use]
    pub fn window(mut self, window: u64) -> Self {
        self.window = Some(window);
        self
    }

    /// Minimum samples before monitoring activates. Default: 1.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the CoDel monitor.
    ///
    /// # Errors
    ///
    /// - Target must have been set.
    /// - Window must have been set and be positive.
    #[inline]
    pub fn build(self) -> Result<CoDelI64, crate::ConfigError> {
        let target = self.target.ok_or(crate::ConfigError::Missing("target"))?;
        let window = self.window.ok_or(crate::ConfigError::Missing("window"))?;
        if window == 0 {
            return Err(crate::ConfigError::Invalid("CoDel window must be positive"));
        }

        Ok(CoDelI64 {
            target,
            interval: window,
            first_above: None,
            elevated: false,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

/// CoDel standing-queue detector (RFC 8289, Nichols & Jacobson), `f64` sojourns.
///
/// See [`CoDelI64`] for the rule. Rejects NaN and infinite sojourns.
#[derive(Debug, Clone)]
pub struct CoDelF64 {
    target: f64,
    interval: u64,
    first_above: Option<u64>,
    elevated: bool,
    count: u64,
    min_samples: u64,
}

/// Builder for [`CoDelF64`].
#[derive(Debug, Clone)]
pub struct CoDelF64Builder {
    target: Option<f64>,
    window: Option<u64>,
    min_samples: u64,
}

impl CoDelF64 {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> CoDelF64Builder {
        CoDelF64Builder {
            target: None,
            window: None,
            min_samples: 1,
        }
    }

    /// Feeds a sojourn time at the given timestamp.
    ///
    /// Returns `Some(Condition)` once primed, `None` before.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sojourn is NaN, or
    /// `DataError::Infinite` if the sojourn is infinite.
    #[inline]
    pub fn update(
        &mut self,
        timestamp: u64,
        sojourn: f64,
    ) -> Result<Option<Condition>, crate::DataError> {
        check_finite!(sojourn);
        self.count += 1;
        self.elevated = standing_queue(
            &mut self.first_above,
            self.interval,
            timestamp,
            sojourn > self.target,
        );

        if self.count < self.min_samples {
            return Ok(None);
        }

        Ok(Some(if self.elevated {
            Condition::Degraded
        } else {
            Condition::Normal
        }))
    }

    /// Convenience for `i64` timestamps (e.g., wire protocol epoch nanos).
    ///
    /// Timestamps must be non-negative. Negative values wrap to large
    /// `u64` values and will produce incorrect interval arithmetic.
    #[inline]
    pub fn update_i64(
        &mut self,
        timestamp: i64,
        sojourn: f64,
    ) -> Result<Option<Condition>, crate::DataError> {
        debug_assert!(timestamp >= 0, "negative timestamp: {timestamp}");
        self.update(timestamp as u64, sojourn)
    }

    /// Whether the last sample found a standing queue (sojourn above target
    /// for a whole interval).
    #[inline]
    #[must_use]
    pub fn is_elevated(&self) -> bool {
        self.elevated
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the monitor has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to empty state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.first_above = None;
        self.elevated = false;
        self.count = 0;
    }
}

impl CoDelF64Builder {
    /// Target sojourn time. Samples above it count toward a standing queue.
    #[inline]
    #[must_use]
    pub fn target(mut self, target: f64) -> Self {
        self.target = Some(target);
        self
    }

    /// Interval (RFC 8289): how long sojourn must stay above target before
    /// the queue counts as standing. Same units as the timestamps.
    #[inline]
    #[must_use]
    pub fn window(mut self, window: u64) -> Self {
        self.window = Some(window);
        self
    }

    /// Minimum samples before monitoring activates. Default: 1.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the CoDel monitor.
    ///
    /// # Errors
    ///
    /// - Target must have been set and be finite.
    /// - Window must have been set and be positive.
    #[inline]
    pub fn build(self) -> Result<CoDelF64, crate::ConfigError> {
        let target = self.target.ok_or(crate::ConfigError::Missing("target"))?;
        if !target.is_finite() {
            return Err(crate::ConfigError::Invalid("CoDel target must be finite"));
        }
        let window = self.window.ok_or(crate::ConfigError::Missing("window"))?;
        if window == 0 {
            return Err(crate::ConfigError::Invalid("CoDel window must be positive"));
        }

        Ok(CoDelF64 {
            target,
            interval: window,
            first_above: None,
            elevated: false,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

// =========================================================================
// RFC 8289 standing-queue rule, shared by the I64 and F64 variants
// =========================================================================

/// The `first_above_time` rule from RFC 8289 section 5.6.
///
/// A sojourn at or below target clears the timer. A sojourn above target
/// starts it at `now` if it is not running. Once a sojourn above target
/// arrives a full `interval` or more after it started, the queue is
/// standing. Returns whether the queue is standing after this sample.
///
/// Elapsed time is `now.wrapping_sub(first_above)`, as in the windowed
/// types and the kernel code they port, so a monotonic tick counter that
/// wraps is handled; the only requirement is that `interval` and any real
/// gap between samples fit in half the counter's range.
#[inline]
fn standing_queue(
    first_above: &mut Option<u64>,
    interval: u64,
    now: u64,
    above_target: bool,
) -> bool {
    if !above_target {
        *first_above = None;
        return false;
    }
    if let Some(started) = *first_above {
        return now.wrapping_sub(started) >= interval;
    }
    *first_above = Some(now);
    false
}

#[cfg(test)]
mod raw_tests {
    use super::*;
    use crate::Condition;

    fn codel(target: i64, window: u64) -> CoDelI64 {
        CoDelI64::builder()
            .target(target)
            .window(window)
            .build()
            .unwrap()
    }

    #[test]
    fn raw_codel_normal() {
        let mut cd = codel(100, 1000);
        assert_eq!(cd.update(0, 50), Some(Condition::Normal));
    }

    // Regression for #759: the previous composition fired on one sample.
    #[test]
    fn single_sample_above_target_is_normal() {
        let mut cd = codel(50, 1_000_000);
        assert_eq!(cd.update(0, 200), Some(Condition::Normal));
        assert!(!cd.is_elevated());
    }

    #[test]
    fn above_target_shorter_than_interval_is_normal() {
        let mut cd = codel(50, 1000);
        assert_eq!(cd.update(0, 200), Some(Condition::Normal));
        assert_eq!(cd.update(500, 200), Some(Condition::Normal));
        assert_eq!(cd.update(999, 200), Some(Condition::Normal));
    }

    #[test]
    fn above_target_for_full_interval_is_degraded_and_stays() {
        let mut cd = codel(50, 1000);
        assert_eq!(cd.update(0, 200), Some(Condition::Normal)); // starts the clock at 0
        assert_eq!(cd.update(1000, 200), Some(Condition::Degraded));
        assert!(cd.is_elevated());
        assert_eq!(cd.update(1500, 51), Some(Condition::Degraded)); // still above target
    }

    #[test]
    fn sample_at_or_below_target_clears_and_rearms() {
        let mut cd = codel(50, 1000);
        let _ = cd.update(0, 200);
        assert_eq!(cd.update(1000, 200), Some(Condition::Degraded));
        assert_eq!(cd.update(1100, 50), Some(Condition::Normal)); // at target clears
        assert!(!cd.is_elevated());
        assert_eq!(cd.update(1200, 200), Some(Condition::Normal)); // restarts at 1200
        assert_eq!(cd.update(2199, 200), Some(Condition::Normal));
        assert_eq!(cd.update(2200, 200), Some(Condition::Degraded));
    }

    // The second reproduction from #759: a long healthy history and several
    // quiet windows must not make one slow sample look like a standing queue.
    #[test]
    fn long_quiet_history_then_one_slow_sample_is_normal() {
        let mut cd = codel(50, 100);
        let mut t = 0u64;
        for _ in 0..1000 {
            t += 1;
            assert_eq!(cd.update(t, 5), Some(Condition::Normal));
        }
        t += 5 * 100; // five quiet windows
        assert_eq!(cd.update(t, 200), Some(Condition::Normal));
    }

    #[test]
    fn raw_codel_degraded() {
        let mut cd = codel(50, 1000);
        for t in 0..=10 {
            let _ = cd.update(t * 100, 200);
        }
        assert!(cd.is_elevated());
    }

    #[test]
    fn min_samples_primes() {
        let mut cd = CoDelI64::builder()
            .target(50)
            .window(1000)
            .min_samples(3)
            .build()
            .unwrap();
        assert_eq!(cd.update(0, 200), None);
        assert_eq!(cd.update(100, 200), None);
        assert!(!cd.is_primed());
        assert_eq!(cd.update(200, 200), Some(Condition::Normal));
        assert!(cd.is_primed());
    }

    #[test]
    fn reset_disarms() {
        let mut cd = codel(50, 1000);
        let _ = cd.update(0, 200);
        let _ = cd.update(1000, 200);
        assert!(cd.is_elevated());
        cd.reset();
        assert!(!cd.is_elevated());
        assert_eq!(cd.count(), 0);
        assert_eq!(cd.update(2000, 200), Some(Condition::Normal)); // starts fresh
    }

    // A monotonic tick counter that wraps through u64::MAX must still measure
    // the interval correctly (wrapping subtraction, as in the windowed types).
    #[test]
    fn interval_survives_counter_wraparound() {
        let mut cd = codel(50, 20);
        let start = u64::MAX - 10;
        assert_eq!(cd.update(start, 200), Some(Condition::Normal)); // starts at MAX-10
        assert_eq!(cd.update(5, 200), Some(Condition::Normal)); // elapsed 16 < 20, past the wrap
        assert_eq!(cd.update(9, 200), Some(Condition::Degraded)); // elapsed 20
        assert_eq!(cd.update(15, 10), Some(Condition::Normal)); // clears
    }

    #[test]
    fn raw_codel_f64() {
        let mut cd = CoDelF64::builder()
            .target(0.5)
            .window(1000)
            .build()
            .unwrap();
        assert_eq!(cd.update(0, 0.1).unwrap(), Some(Condition::Normal));
        assert_eq!(cd.update(100, 0.9).unwrap(), Some(Condition::Normal)); // starts at 100
        assert_eq!(cd.update(1099, 0.9).unwrap(), Some(Condition::Normal));
        assert_eq!(cd.update(1100, 0.9).unwrap(), Some(Condition::Degraded));
        assert_eq!(cd.update(1200, 0.5).unwrap(), Some(Condition::Normal)); // at target clears
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut cd = CoDelF64::builder()
            .target(0.5)
            .window(1000)
            .build()
            .unwrap();
        assert!(matches!(
            cd.update(0, f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
        assert!(matches!(
            cd.update(0, f64::INFINITY),
            Err(crate::DataError::Infinite)
        ));
        assert!(
            CoDelF64::builder()
                .target(f64::NAN)
                .window(1000)
                .build()
                .is_err()
        );
    }
}
