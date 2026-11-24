use core::time::Duration;

use nexus_stats_core::parts::LastTime;
use nexus_stats_core::{Condition, ConfigError, DataError, Timestamp};

/// CoDel standing-queue detector (RFC 8289, Nichols & Jacobson).
///
/// Feed it each item's sojourn time (how long it waited in the queue) with
/// the time it was dequeued. It reports `Degraded` only once the sojourn
/// has stayed at or above `target` for a whole `interval`. The first such
/// sample starts the clock, a sample below target stops it, and a sample
/// at or above target a full interval or more after the start is a
/// standing queue. As in the RFC, only `sojourn < target` is below. A
/// single slow item, or a burst shorter than the interval, is `Normal`.
///
/// The RFC also resets the timer when the queue holds at most one packet
/// (`bytes() <= maxpacket_`). This type sees only sojourn times, so it does
/// not model that. It detects; what to do about a standing queue (the
/// RFC's drop schedule) is the caller's.
///
/// The clock `T` is `i128` nanoseconds or an `Instant`. `no_std`
/// compatible.
///
/// # Time
///
/// Time must not go back. `update` ignores a sample dequeued before the
/// last one taken: it neither starts nor clears the timer and is not
/// counted. `checked_update` reports it as an error.
#[derive(Debug, Clone)]
pub struct CoDel<T: Timestamp> {
    target: Duration,
    interval: Duration,
    /// When the sojourn first reached the target, while it stays there.
    first_above: Option<T>,
    standing: bool,
    count: u64,
    last: LastTime<T>,
}

impl<T: Timestamp> CoDel<T> {
    /// Creates a detector. `target` is the sojourn at which the queue
    /// counts as delayed, and `interval` is how long it must stay there
    /// before the queue is standing. The RFC suggests 5 ms and 100 ms.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `interval` is zero.
    #[inline]
    pub fn new(target: Duration, interval: Duration) -> Result<Self, ConfigError> {
        if interval.is_zero() {
            return Err(ConfigError::Invalid("CoDel interval must be positive"));
        }
        Ok(Self {
            target,
            interval,
            first_above: None,
            standing: false,
            count: 0,
            last: LastTime::new(),
        })
    }

    /// Feeds one item's sojourn at the time it was dequeued and returns
    /// the condition of the queue.
    ///
    /// A sample dequeued before the last one taken is ignored.
    #[inline]
    pub fn update(&mut self, now: T, sojourn: Duration) -> Condition {
        if self.last.would_go_back(now) {
            return self.condition();
        }
        self.last.set(now);
        self.count += 1;
        self.standing = self.is_standing_after(now, sojourn >= self.target);
        self.condition()
    }

    /// Checked update. Feeds the sample, or returns an error and leaves
    /// the detector unchanged if `now` is before the last time taken.
    ///
    /// # Errors
    ///
    /// [`DataError::NonMonotonicTime`] if `now` is before the last time
    /// taken.
    #[inline]
    pub fn checked_update(&mut self, now: T, sojourn: Duration) -> Result<Condition, DataError> {
        self.last.check(now)?;
        Ok(self.update(now, sojourn))
    }

    /// The condition as of the last sample: `Degraded` while the queue is
    /// standing.
    #[inline]
    #[must_use]
    pub fn condition(&self) -> Condition {
        if self.standing {
            return Condition::Degraded;
        }
        Condition::Normal
    }

    /// Whether the queue is standing (sojourn at or above target for a
    /// full interval).
    #[inline]
    #[must_use]
    pub fn is_elevated(&self) -> bool {
        self.standing
    }

    /// The sojourn at which the queue counts as delayed.
    #[inline]
    #[must_use]
    pub fn target(&self) -> Duration {
        self.target
    }

    /// How long the sojourn must stay at or above target.
    #[inline]
    #[must_use]
    pub fn interval(&self) -> Duration {
        self.interval
    }

    /// Number of samples taken.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Resets the detector. Configuration is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.first_above = None;
        self.standing = false;
        self.count = 0;
        self.last.reset();
    }

    /// The `first_above_time` rule from RFC 8289 section 5.6.
    ///
    /// A sojourn below target clears the timer. One at or above target
    /// starts it at `now` if it is not running. Once such a sojourn arrives
    /// a full interval or more after the start, the queue is standing.
    #[inline]
    fn is_standing_after(&mut self, now: T, above_target: bool) -> bool {
        if !above_target {
            self.first_above = None;
            return false;
        }
        let started = *self.first_above.get_or_insert(now);
        // `interval` is positive, so a timer that starts on this sample is
        // not yet standing.
        now.since(started) >= self.interval
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nexus_stats_core::Condition::{Degraded, Normal};
    use nexus_stats_core::DataError::NonMonotonicTime;

    fn ns(n: u64) -> Duration {
        Duration::from_nanos(n)
    }

    /// Target 100 ns, interval 1,000 ns, on nanosecond time.
    fn codel() -> CoDel<i128> {
        CoDel::new(ns(100), ns(1_000)).unwrap()
    }

    #[test]
    fn a_quiet_queue_is_normal() {
        let mut cd = codel();
        for t in 0..100 {
            assert_eq!(cd.update(t * 100, ns(50)), Normal);
        }
        assert_eq!((cd.count(), cd.is_elevated()), (100, false));
    }

    #[test]
    fn one_slow_item_is_normal() {
        let mut cd = codel();
        assert_eq!(cd.update(0, ns(5_000)), Normal);
    }

    #[test]
    fn a_burst_shorter_than_the_interval_is_normal() {
        let mut cd = codel();
        for t in [0, 300, 600, 999] {
            assert_eq!(cd.update(t, ns(500)), Normal);
        }
        assert_eq!(cd.update(1_100, ns(10)), Normal);
    }

    #[test]
    fn above_target_for_a_full_interval_is_degraded_and_stays() {
        let mut cd = codel();
        assert_eq!(cd.update(0, ns(500)), Normal);
        assert_eq!(cd.update(999, ns(500)), Normal);
        // Elapsed equal to the interval counts.
        assert_eq!(cd.update(1_000, ns(500)), Degraded);
        assert_eq!(cd.update(5_000, ns(500)), Degraded);
        assert_eq!(cd.condition(), Degraded);
    }

    #[test]
    fn a_sample_below_target_clears_and_rearms() {
        let mut cd = codel();
        cd.update(0, ns(500));
        assert_eq!(cd.update(1_500, ns(500)), Degraded);
        assert_eq!(cd.update(1_600, ns(99)), Normal);
        // The timer starts again from the next slow sample.
        assert_eq!(cd.update(1_700, ns(500)), Normal);
        assert_eq!(cd.update(2_699, ns(500)), Normal);
        assert_eq!(cd.update(2_700, ns(500)), Degraded);
    }

    #[test]
    fn a_long_quiet_history_then_one_slow_sample_is_normal() {
        let mut cd = codel();
        for t in 0..1_000 {
            cd.update(t * 10, ns(1));
        }
        assert_eq!(cd.update(1_000_000, ns(900)), Normal);
    }

    /// RFC 8289: only `sojourn < target` is below.
    #[test]
    fn a_sojourn_equal_to_the_target_counts_as_above() {
        let mut cd = codel();
        assert_eq!(cd.update(0, ns(100)), Normal);
        assert_eq!(cd.update(1_000, ns(100)), Degraded);

        let mut cd = codel();
        cd.update(0, ns(99));
        assert_eq!(cd.update(1_000, ns(99)), Normal);
        assert_eq!(cd.update(9_000, ns(99)), Normal);
    }

    #[test]
    fn at_target_then_below_clears_the_timer() {
        let mut cd = codel();
        cd.update(0, ns(100));
        cd.update(500, ns(99));
        assert_eq!(cd.update(1_000, ns(100)), Normal);
        assert_eq!(cd.update(1_999, ns(100)), Normal);
        assert_eq!(cd.update(2_000, ns(100)), Degraded);
    }

    /// A target of zero means any wait at all: every sojourn is above.
    #[test]
    fn a_zero_target_treats_every_sojourn_as_above() {
        let mut cd = CoDel::<i128>::new(Duration::ZERO, ns(10)).unwrap();
        assert_eq!(cd.update(0, Duration::ZERO), Normal);
        assert_eq!(cd.update(10, Duration::ZERO), Degraded);
    }

    #[test]
    fn a_zero_interval_is_refused() {
        assert!(CoDel::<i128>::new(ns(100), Duration::ZERO).is_err());
    }

    #[test]
    fn a_late_sample_is_ignored() {
        let mut cd = codel();
        cd.update(0, ns(500));
        cd.update(900, ns(500));
        // A late sample below target does not clear the timer.
        assert_eq!(cd.update(800, ns(1)), Normal);
        assert_eq!(cd.count(), 2);
        assert_eq!(cd.update(1_000, ns(500)), Degraded);
        // A late sample above target changes nothing either.
        let mut cd = codel();
        cd.update(5_000, ns(1));
        assert_eq!(cd.update(0, ns(500)), Normal);
        assert_eq!(cd.update(6_000, ns(500)), Normal);
        assert_eq!(cd.count(), 2);
    }

    #[test]
    fn checked_update_reports_a_late_sample_and_changes_nothing() {
        let mut cd = codel();
        assert_eq!(cd.checked_update(1_000, ns(500)), Ok(Normal));
        assert_eq!(cd.checked_update(999, ns(1)), Err(NonMonotonicTime));
        assert_eq!(cd.checked_update(i128::MIN, ns(1)), Err(NonMonotonicTime));
        assert_eq!(cd.count(), 1);
        // The same time is not late.
        assert_eq!(cd.checked_update(1_000, ns(500)), Ok(Normal));
        assert_eq!(cd.checked_update(2_000, ns(500)), Ok(Degraded));
    }

    #[test]
    fn checked_update_agrees_with_update() {
        let (mut plain, mut checked) = (codel(), codel());
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut t = 0i128;
        for _ in 0..5_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            t += i128::from(state % 400);
            let sojourn = ns((state >> 20) % 180);
            assert_eq!(
                checked.checked_update(t, sojourn),
                Ok(plain.update(t, sojourn))
            );
        }
        assert_eq!(plain.count(), 5_000);
    }

    #[test]
    fn reset_disarms_and_forgets_the_last_time() {
        let mut cd = codel();
        cd.update(5_000, ns(500));
        cd.update(7_000, ns(500));
        assert!(cd.is_elevated());
        cd.reset();
        assert_eq!((cd.count(), cd.condition()), (0, Normal));
        // An earlier time is accepted after a reset.
        assert_eq!(cd.checked_update(0, ns(500)), Ok(Normal));
        assert_eq!(cd.update(999, ns(500)), Normal);
        assert_eq!(cd.update(1_000, ns(500)), Degraded);
    }

    /// The whole range of the clock is usable.
    #[test]
    fn times_at_the_ends_of_the_range_are_only_a_long_gap() {
        let mut cd = codel();
        assert_eq!(cd.update(i128::MIN, ns(500)), Normal);
        assert_eq!(cd.update(i128::MAX, ns(500)), Degraded);
    }

    #[cfg(feature = "std")]
    #[test]
    fn an_instant_and_nanoseconds_agree() {
        use std::time::Instant;
        let start = Instant::now();
        let mut on_instant = CoDel::<Instant>::new(ns(100), ns(1_000)).unwrap();
        let mut on_nanos = codel();
        for (at, sojourn) in [
            (0u64, 500u64),
            (400, 500),
            (1_000, 100),
            (1_200, 99),
            (1_300, 100),
            (2_300, 250),
        ] {
            let a = on_instant.update(start + ns(at), ns(sojourn));
            let b = on_nanos.update(i128::from(at), ns(sojourn));
            assert_eq!(a, b, "at {at}");
        }
        assert_eq!(on_nanos.condition(), Degraded);
    }
}
