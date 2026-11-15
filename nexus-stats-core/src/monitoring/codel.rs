use crate::Condition;
use crate::Sample;

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
/// State is one timestamp. `no_std` compatible. `CoDel<f64>` rejects NaN and
/// infinity and returns `Result`; `CoDel<i64>` cannot fail.
///
/// # Weighting clock
///
/// Caller's timestamps. Any call rate; the interval is measured in ticks,
/// not samples. Ticks must be monotonic; a counter that wraps is fine as
/// long as the window and any real gap between samples fit in half its
/// range (elapsed time is computed with wrapping subtraction).
#[derive(Debug, Clone)]
pub struct CoDel<T: Sample> {
    target: T,
    interval: u64,
    first_above: Option<u64>,
    elevated: bool,
    count: u64,
    min_samples: u64,
}

/// Builder for [`CoDel`].
#[derive(Debug, Clone)]
pub struct CoDelBuilder<T: Sample> {
    target: Option<T>,
    window: Option<u64>,
    min_samples: u64,
}

impl<T: Sample> CoDel<T> {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> CoDelBuilder<T> {
        CoDelBuilder {
            target: None,
            window: None,
            min_samples: 1,
        }
    }

    /// Whether the queue is currently standing (sojourn above target for a
    /// full window).
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

    /// Whether `min_samples` have been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets the detector. Configuration is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.first_above = None;
        self.elevated = false;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, timestamp: u64, above_target: bool) -> Option<Condition> {
        self.count += 1;
        self.elevated = standing_queue(
            &mut self.first_above,
            self.interval,
            timestamp,
            above_target,
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
}

impl CoDel<f64> {
    /// Feeds one item's sojourn at its dequeue `timestamp`. Returns the
    /// condition once primed.
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
        Ok(self.fold(timestamp, sojourn > self.target))
    }
}

impl CoDel<i64> {
    /// Feeds one item's sojourn at its dequeue `timestamp`. Returns the
    /// condition once primed.
    #[inline]
    pub fn update(&mut self, timestamp: u64, sojourn: i64) -> Option<Condition> {
        self.fold(timestamp, sojourn > self.target)
    }
}

impl<T: Sample> CoDelBuilder<T> {
    /// Sojourn above which the queue counts as delayed (the RFC's *target*).
    #[inline]
    #[must_use]
    pub fn target(mut self, target: T) -> Self {
        self.target = Some(target);
        self
    }

    /// How long sojourn must stay above target before the queue is
    /// standing, in ticks (the RFC's *interval*).
    #[inline]
    #[must_use]
    pub fn window(mut self, window: u64) -> Self {
        self.window = Some(window);
        self
    }

    /// Samples required before `update` reports a condition. Default 1.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the detector.
    ///
    /// # Errors
    ///
    /// `ConfigError::Missing` if `target` or `window` was not set;
    /// `ConfigError::Invalid` if `target` is not finite or `window` is zero.
    pub fn build(self) -> Result<CoDel<T>, crate::ConfigError> {
        let target = self.target.ok_or(crate::ConfigError::Missing("target"))?;
        if !target.is_finite() {
            return Err(crate::ConfigError::Invalid("CoDel target must be finite"));
        }
        let window = self.window.ok_or(crate::ConfigError::Missing("window"))?;
        if window == 0 {
            return Err(crate::ConfigError::Invalid("CoDel window must be positive"));
        }
        Ok(CoDel {
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
// RFC 8289 standing-queue rule, shared by every instantiation
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

    fn codel(target: i64, window: u64) -> CoDel<i64> {
        CoDel::<i64>::builder()
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
        let mut cd = CoDel::<i64>::builder()
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
        let mut cd = CoDel::<f64>::builder()
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
        let mut cd = CoDel::<f64>::builder()
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
            CoDel::<f64>::builder()
                .target(f64::NAN)
                .window(1000)
                .build()
                .is_err()
        );
    }
}
