use core::marker::PhantomData;
use core::time::Duration;

use nexus_stats_core::Timestamp;
use nexus_stats_core::parts::LastTime;
use nexus_stats_core::storage::Ring;

/// Liveness of a source, from how long it has been silent against how
/// often it usually speaks.
///
/// Feed it the time of each event. It keeps the mean gap between the last
/// `window` events, and [`check`](Self::check) reports the silence so far
/// as a multiple of that gap. It gives a number and no verdict: where to
/// draw the line is the caller's decision, and [`Suspicion`] says how to
/// read it.
///
/// This is the failure detector Apache Cassandra uses for its gossip: the
/// same ratio over a bounded window of intervals, with the option not to
/// record an interval longer than a limit, so that one long outage does
/// not make the next one look normal.
///
/// # Weighting clock
///
/// The caller's timestamps, one per event. Every gap in the window weighs
/// the same.
///
/// # Examples
///
/// ```
/// use nexus_stats_monitoring::Liveness;
///
/// let mut liveness = Liveness::builder().window(100).build().unwrap();
/// // A heartbeat every second, as nanoseconds. An `Instant` works too.
/// for second in 0..10_i128 {
///     liveness.update(second * 1_000_000_000);
/// }
/// // Three seconds after the last one: three typical gaps of silence.
/// let suspicion = liveness.check(12_000_000_000).unwrap();
/// assert_eq!(suspicion.ratio(), 3.0);
/// ```
#[derive(Debug, Clone)]
pub struct Liveness<T: Timestamp> {
    /// The last `window` gaps, in nanoseconds.
    gaps: Ring<u64>,
    /// Their sum, which is exact.
    total: u128,
    /// The longest gap that is recorded.
    longest_recorded: u64,
    last: LastTime<T>,
    count: u64,
}

/// How suspicious a silence is: a [`Liveness`] reading.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Suspicion {
    silence: Duration,
    mean_gap: Duration,
}

/// Builder for [`Liveness`].
#[derive(Debug, Clone)]
pub struct LivenessBuilder<T: Timestamp> {
    window: usize,
    longest_recorded: Option<Duration>,
    clock: PhantomData<T>,
}

/// Cassandra's window: the last 1,000 intervals.
const DEFAULT_WINDOW: usize = 1_000;

impl Suspicion {
    /// How long the source has been silent.
    #[must_use]
    pub fn silence(&self) -> Duration {
        self.silence
    }

    /// The mean gap between its recent events.
    #[must_use]
    pub fn mean_gap(&self) -> Duration {
        self.mean_gap
    }

    /// The silence as a multiple of the mean gap: `1.0` is on schedule,
    /// `3.0` is three typical gaps overdue. NaN if every recorded gap was
    /// zero and there is no silence.
    #[must_use]
    pub fn ratio(&self) -> f64 {
        self.silence.as_secs_f64() / self.mean_gap.as_secs_f64()
    }

    /// The chance that a live source would be silent this long:
    /// `exp(-ratio)`.
    ///
    /// This assumes events arrive at random around a steady rate. A source
    /// that ticks at a fixed interval is far less likely to be late than
    /// this says, so for one the figure is conservative.
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn probability_alive(&self) -> f64 {
        nexus_stats_core::math::exp(-self.ratio())
    }

    /// The same chance on Cassandra's scale: `-log10` of it, so `1.0` is
    /// one chance in ten and `8.0`, Cassandra's default threshold, one in
    /// a hundred million.
    #[must_use]
    pub fn phi(&self) -> f64 {
        self.ratio() * core::f64::consts::LOG10_E
    }
}

impl<T: Timestamp> Liveness<T> {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> LivenessBuilder<T> {
        LivenessBuilder {
            window: DEFAULT_WINDOW,
            longest_recorded: None,
            clock: PhantomData,
        }
    }

    /// Records an event at `time`.
    ///
    /// An event timestamped before the last one taken is ignored. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, time: T) {
        if self.last.would_go_back(time) {
            return;
        }
        // The first event opens no gap.
        if let Some(gap) = self.last.elapsed_to(time) {
            self.record(nanos(gap));
        }
        self.last.set(time);
        self.count += 1;
    }

    /// Checked update. Records an event at `time`, or returns an error and
    /// leaves the state unchanged if `time` is before the last event.
    ///
    /// # Errors
    ///
    /// [`DataError::NonMonotonicTime`](nexus_stats_core::DataError::NonMonotonicTime)
    /// if `time` is before the last event taken.
    #[inline]
    pub fn checked_update(&mut self, time: T) -> Result<(), nexus_stats_core::DataError> {
        self.last.check(time)?;
        self.update(time);
        Ok(())
    }

    /// The silence at `now` against the mean gap, or `None` until a gap
    /// has been recorded. A `now` before the last event reads as no
    /// silence.
    #[must_use]
    pub fn check(&self, now: T) -> Option<Suspicion> {
        let mean_gap = self.mean_gap()?;
        Some(Suspicion {
            silence: self.last.elapsed_to(now)?,
            mean_gap,
        })
    }

    /// The mean of the recorded gaps, or `None` until there is one.
    #[must_use]
    pub fn mean_gap(&self) -> Option<Duration> {
        let recorded = self.gaps.len() as u128;
        if recorded == 0 {
            return None;
        }
        // At most `u64::MAX`: a mean of `u64` gaps.
        Some(Duration::from_nanos((self.total / recorded) as u64))
    }

    /// Events recorded since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether a reading is available: a gap has been recorded.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        !self.gaps.is_empty()
    }

    /// Forgets every event. The configuration is kept.
    pub fn reset(&mut self) {
        self.gaps.clear(0);
        self.total = 0;
        self.last.reset();
        self.count = 0;
    }

    /// Adds a gap to the window, unless it is longer than the limit.
    #[inline]
    fn record(&mut self, gap: u64) {
        if gap > self.longest_recorded {
            return;
        }
        let evicted = self.gaps.push(gap).unwrap_or(0);
        self.total = self.total + u128::from(gap) - u128::from(evicted);
    }
}

impl<T: Timestamp> LivenessBuilder<T> {
    /// How many of the latest gaps the mean is taken over. Default 1,000,
    /// as in Cassandra.
    #[must_use]
    pub fn window(mut self, gaps: usize) -> Self {
        self.window = gaps;
        self
    }

    /// The longest gap to record. A longer one still counts as silence in
    /// [`Liveness::check`], but does not enter the mean. Default: no limit.
    #[must_use]
    pub fn longest_recorded_gap(mut self, limit: Duration) -> Self {
        self.longest_recorded = Some(limit);
        self
    }

    /// Builds the detector.
    ///
    /// # Errors
    ///
    /// `Invalid` if `window` is 0, or the longest recorded gap is zero.
    pub fn build(self) -> Result<Liveness<T>, nexus_stats_core::ConfigError> {
        if self.longest_recorded.is_some_and(|limit| limit.is_zero()) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "longest recorded gap must be above zero",
            ));
        }
        Ok(Liveness {
            gaps: Ring::new(self.window, 0)?,
            total: 0,
            longest_recorded: self.longest_recorded.map_or(u64::MAX, nanos),
            last: LastTime::new(),
            count: 0,
        })
    }
}

/// A span in whole nanoseconds, or `u64::MAX` (584 years) if longer.
#[inline]
fn nanos(span: Duration) -> u64 {
    u64::try_from(span.as_nanos()).unwrap_or(u64::MAX)
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use nexus_stats_core::DataError::NonMonotonicTime;
    use std::time::Instant;

    const SECOND: i128 = 1_000_000_000;

    fn liveness(window: usize) -> Liveness<i128> {
        Liveness::builder().window(window).build().unwrap()
    }

    #[test]
    fn there_is_no_reading_until_a_gap_is_known() {
        let mut l = liveness(10);
        assert_eq!(
            (l.check(0), l.mean_gap(), l.is_primed()),
            (None, None, false)
        );
        l.update(5 * SECOND);
        assert_eq!((l.check(9 * SECOND), l.count()), (None, 1));
        l.update(6 * SECOND);
        assert!(l.is_primed());
        assert_eq!(l.mean_gap(), Some(Duration::from_secs(1)));
    }

    #[test]
    fn the_ratio_is_the_silence_in_mean_gaps() {
        let mut l = liveness(100);
        for second in 0..10 {
            l.update(second * SECOND);
        }
        let on_time = l.check(10 * SECOND).unwrap();
        assert_eq!(
            (on_time.silence(), on_time.mean_gap()),
            (Duration::from_secs(1), Duration::from_secs(1))
        );
        assert_eq!(on_time.ratio(), 1.0);
        assert_eq!(l.check(12 * SECOND).unwrap().ratio(), 3.0);
        // At the last event itself there is no silence.
        assert_eq!(l.check(9 * SECOND).unwrap().ratio(), 0.0);
        // Checking does not change anything.
        assert_eq!(l.check(12 * SECOND).unwrap().ratio(), 3.0);
    }

    #[test]
    fn the_probability_and_phi_follow_from_the_ratio() {
        let mut l = liveness(100);
        l.update(0);
        l.update(SECOND);
        let s = l.check(4 * SECOND).unwrap();
        assert_eq!(s.ratio(), 3.0);
        assert!((s.probability_alive() - (-3.0_f64).exp()).abs() < 1e-15);
        // phi is -log10 of that probability.
        assert!((s.phi() + s.probability_alive().log10()).abs() < 1e-12);
        // Cassandra convicts at phi 8: about 18.4 mean gaps.
        let convicted = l.check(SECOND + 18_420_680_744).unwrap();
        assert!((convicted.phi() - 8.0).abs() < 1e-9);
    }

    #[test]
    fn the_mean_is_over_the_last_window_of_gaps_and_is_exact() {
        let mut l = liveness(3);
        let mut t = 0;
        for gap in [10, 20, 30, 400, 500, 600] {
            t += gap;
            l.update(t);
        }
        // The first sample opens no gap, so five were recorded; three kept.
        assert_eq!(l.mean_gap(), Some(Duration::from_nanos(500)));
        // Against a mean taken directly, over a long random run.
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let (mut l, mut gaps, mut t) = (liveness(64), std::vec::Vec::new(), 0i128);
        l.update(t);
        for _ in 0..5_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let gap = state % 1_000_000_007;
            t += i128::from(gap);
            l.update(t);
            gaps.push(u128::from(gap));
            let kept = &gaps[gaps.len().saturating_sub(64)..];
            let mean = kept.iter().sum::<u128>() / kept.len() as u128;
            assert_eq!(l.mean_gap(), Some(Duration::from_nanos(mean as u64)));
        }
    }

    /// One long outage is silence while it lasts, but with a limit it does
    /// not raise the mean, so the next outage is judged as sharply.
    #[test]
    fn a_gap_over_the_limit_is_not_recorded() {
        let build = |limit: Option<Duration>| {
            let mut builder = Liveness::<i128>::builder().window(4);
            if let Some(limit) = limit {
                builder = builder.longest_recorded_gap(limit);
            }
            builder.build().unwrap()
        };
        let (mut limited, mut unlimited) = (build(Some(Duration::from_secs(5))), build(None));
        for l in [&mut limited, &mut unlimited] {
            for second in 0..4 {
                l.update(second * SECOND);
            }
            // During the outage, both see the same silence.
            assert_eq!(l.check(60 * SECOND).unwrap().ratio(), 57.0);
            l.update(63 * SECOND);
        }
        assert_eq!(limited.mean_gap(), Some(Duration::from_secs(1)));
        assert_eq!(unlimited.mean_gap(), Some(Duration::from_secs(63) / 4));
        // The event itself was taken either way: silence restarts from it.
        assert_eq!(
            limited.check(64 * SECOND).unwrap().silence(),
            Duration::from_secs(1)
        );
        assert_eq!(limited.count(), 5);
    }

    #[test]
    fn an_instant_and_nanoseconds_agree() {
        let start = Instant::now();
        let mut on_instant = Liveness::builder().window(8).build().unwrap();
        let mut on_nanos = liveness(8);
        for millis in [0u64, 100, 250, 251, 900] {
            on_instant.update(start + Duration::from_millis(millis));
            on_nanos.update(i128::from(millis) * 1_000_000);
        }
        let a = on_instant
            .check(start + Duration::from_millis(1_500))
            .unwrap();
        let b = on_nanos.check(1_500_000_000).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn an_event_before_the_last_one_is_ignored() {
        let mut l = liveness(10);
        l.update(10 * SECOND);
        l.update(11 * SECOND);
        let before = (l.mean_gap(), l.count());
        l.update(5 * SECOND);
        assert_eq!((l.mean_gap(), l.count()), before);
        // The last event did not move back.
        assert_eq!(
            l.check(12 * SECOND).unwrap().silence(),
            Duration::from_secs(1)
        );
        // A check before the last event reads as no silence.
        assert_eq!(l.check(0).unwrap().ratio(), 0.0);
    }

    #[test]
    fn checked_update_reports_time_going_back_and_changes_nothing() {
        let mut l = liveness(10);
        assert_eq!(l.checked_update(-3 * SECOND), Ok(()));
        assert_eq!(l.checked_update(2 * SECOND), Ok(()));
        let before = (l.mean_gap(), l.count());
        assert_eq!(l.checked_update(2 * SECOND - 1), Err(NonMonotonicTime));
        assert_eq!((l.mean_gap(), l.count()), before);
        // The same time is not going back: a gap of zero.
        assert_eq!(l.checked_update(2 * SECOND), Ok(()));
        assert_eq!(l.mean_gap(), Some(Duration::from_millis(2_500)));
    }

    /// Events all at one time have a mean gap of zero. Any silence is then
    /// infinitely many gaps, and no silence is undefined.
    #[test]
    fn a_mean_gap_of_zero_gives_what_the_division_gives() {
        let mut l = liveness(4);
        l.update(SECOND);
        l.update(SECOND);
        assert_eq!(l.check(2 * SECOND).unwrap().ratio(), f64::INFINITY);
        assert!(l.check(SECOND).unwrap().ratio().is_nan());
    }

    #[test]
    fn reset_forgets_the_gaps_and_the_clock() {
        let mut l = liveness(4);
        l.update(10 * SECOND);
        l.update(20 * SECOND);
        l.reset();
        assert_eq!((l.mean_gap(), l.count(), l.is_primed()), (None, 0, false));
        assert_eq!(l.checked_update(SECOND), Ok(()));
        assert_eq!(l.checked_update(3 * SECOND), Ok(()));
        assert_eq!(l.mean_gap(), Some(Duration::from_secs(2)));
    }

    #[test]
    fn the_builder_checks_its_configuration() {
        assert!(Liveness::<i128>::builder().window(0).build().is_err());
        let zero = Liveness::<i128>::builder().longest_recorded_gap(Duration::ZERO);
        assert!(zero.build().is_err());
        // The default is Cassandra's window.
        let mut l = Liveness::<i128>::builder().build().unwrap();
        for i in 0..2_500 {
            l.update(i * (SECOND + i));
        }
        assert_eq!(l.gaps.len(), 1_000);
    }
}
