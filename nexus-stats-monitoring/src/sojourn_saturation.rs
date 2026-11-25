// Consumer saturation from per-message queue sojourn: the stamped twin of
// `PollSaturation`. Where that type bounds the wait from poll outcomes, this
// one takes the exact wait (dequeue time minus enqueue time, same clock) and
// summarizes it per period: how many waited past the budget, the floor, the
// worst, the total, and whether the queue ever drained to within budget.
//
// State: the budget, five accumulators and a flag. No clock.

use core::time::Duration;

/// Summary of the sojourns in a period: what [`SojournSaturation::take`]
/// returns for the period it closes, and what
/// [`SojournSaturation::summary`] returns for the period so far.
///
/// Covers every message in the period. When to snap is the caller's
/// decision: a timer (every millisecond, every second), a count (every
/// 1,000 messages), or an event. The type keeps no clock.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SojournSummary {
    messages_seen: u64,
    messages_over_budget: u64,
    /// The shortest and the longest, or `None` for an empty period.
    extremes: Option<(Duration, Duration)>,
    total_sojourn: Duration,
    is_backlogged: bool,
}

impl SojournSummary {
    /// Messages seen in the period.
    #[inline]
    #[must_use]
    pub fn messages_seen(&self) -> u64 {
        self.messages_seen
    }

    /// Of those, the messages whose sojourn exceeded `budget`.
    /// `messages_over_budget / messages_seen` is the fraction that waited
    /// past the budget.
    #[inline]
    #[must_use]
    pub fn messages_over_budget(&self) -> u64 {
        self.messages_over_budget
    }

    /// Shortest sojourn: the floor, transit plus processing. `None` when
    /// no message was seen. **Zero means the two clocks disagree**, because
    /// a real sojourn is never zero.
    #[inline]
    #[must_use]
    pub fn min_sojourn(&self) -> Option<Duration> {
        Some(self.extremes?.0)
    }

    /// Longest sojourn: the worst wait. `None` when no message was seen.
    #[inline]
    #[must_use]
    pub fn max_sojourn(&self) -> Option<Duration> {
        Some(self.extremes?.1)
    }

    /// Sum of all sojourns. It stops at [`Duration::MAX`]. Divided by the
    /// period length it is the mean number of messages waiting (Little's
    /// law), the count form of saturation.
    #[inline]
    #[must_use]
    pub fn total_sojourn(&self) -> Duration {
        self.total_sojourn
    }

    /// Mean sojourn, to the nanosecond below. `None` when no message was
    /// seen.
    #[inline]
    #[must_use]
    pub fn mean_sojourn(&self) -> Option<Duration> {
        if self.messages_seen == 0 {
            return None;
        }
        let nanos = self.total_sojourn.as_nanos() / u128::from(self.messages_seen);
        Some(duration_from_nanos(nanos))
    }

    /// No message within budget for the whole period: the queue stood the
    /// entire time. CoDel's standing queue with the period as the interval.
    /// Vacuously true for an empty period, as for
    /// [`PollSummary`](super::PollSummary).
    #[inline]
    #[must_use]
    pub fn is_backlogged(&self) -> bool {
        self.is_backlogged
    }
}

/// Consumer saturation from per-message queue sojourn.
///
/// Feed it each message's sojourn: the time it was dequeued minus the time
/// it was enqueued, both from the same clock. It answers, per period, how
/// many messages waited past your budget, how long the worst waited, what
/// the floor was, and whether the queue ever drained.
///
/// This is the exact form of what [`PollSaturation`](super::PollSaturation)
/// bounds without stamps. Use this when messages carry an enqueue time on
/// the same clock (our queues and shared memory, or an exchange timestamp
/// for upstream lag); use `PollSaturation` when they do not. The two share
/// vocabulary: `budget`, `messages_seen`, `messages_over_budget`,
/// `is_backlogged`, peek with `summary`, snap with `take`.
///
/// # Reading it
///
/// A sojourn is never zero on a healthy system: there is always transit and
/// processing. What matters is whether it stays near its floor or grows.
///
/// | Reading | Healthy |
/// |---|---|
/// | `messages_over_budget / messages_seen` | near zero |
/// | `min_sojourn()` | small and stable; **zero means the clocks disagree** |
/// | `max_sojourn()` | under budget |
/// | `mean_sojourn()` | close to the minimum |
/// | `is_backlogged()` | false |
///
/// `total_sojourn() / period length` is the mean number of messages
/// waiting (Little's law), so this type also yields the count form of
/// saturation; healthy is well under 1.
///
/// # Clocks and stamps
///
/// The stamp and the dequeue time must come from the same clock. For
/// in-process and same-host producers that is one monotonic or wall clock
/// and the sojourn is exact. Across hosts a wall-clock offset shifts every
/// sojourn by the same amount; the minimum absorbs it and the over-budget
/// count must be read against it.
///
/// Compute the sojourn with [`Tick::since`](nexus_stats_core::Tick::since):
/// `dequeued.since(enqueued)`. It is zero when the dequeue time is not
/// after the enqueue time, which is clock skew, and that then shows up as
/// a zero minimum.
///
/// # Knobs
///
/// `budget`, and when you snap. No interval, no target, no baseline window,
/// no smoothing. [`CoDel`](super::CoDel) stays for callers who want
/// the RFC detector to drive a control decision; this type is the
/// observability summary. Smoothing belongs on the outputs, once per
/// summary.
///
/// # Weighting clock
///
/// Per message. Nothing is weighted by time or by loop iteration.
#[derive(Debug, Clone)]
pub struct SojournSaturation {
    budget: Duration,
    messages_seen: u64,
    messages_over_budget: u64,
    /// `Duration::MAX` until the first message of the period.
    min_sojourn: Duration,
    max_sojourn: Duration,
    total_sojourn: Duration,
    within_budget_seen: bool,
}

impl SojournSaturation {
    /// Creates a monitor.
    ///
    /// `budget` is the sojourn above which a message counts toward
    /// [`SojournSummary::messages_over_budget`]: the wait you consider
    /// late.
    #[inline]
    #[must_use]
    pub const fn new(budget: Duration) -> Self {
        Self {
            budget,
            messages_seen: 0,
            messages_over_budget: 0,
            min_sojourn: Duration::MAX,
            max_sojourn: Duration::ZERO,
            total_sojourn: Duration::ZERO,
            within_budget_seen: false,
        }
    }

    /// One message's sojourn: how long it waited between enqueue and
    /// dequeue, measured on one clock.
    #[inline]
    pub fn update(&mut self, sojourn: Duration) {
        // PERF: straight-line. Whether a message is over budget is
        // unpredictable exactly when it matters.
        let over_budget = sojourn > self.budget;
        self.messages_seen += 1;
        self.messages_over_budget += u64::from(over_budget);
        self.within_budget_seen |= !over_budget;
        self.min_sojourn = self.min_sojourn.min(sojourn);
        self.max_sojourn = self.max_sojourn.max(sojourn);
        self.total_sojourn = self.total_sojourn.saturating_add(sojourn);
    }

    /// The summary of the period so far. Changes nothing, so it can be read
    /// after any number of messages, to alert on, while `take` keeps its
    /// own cadence.
    #[inline]
    #[must_use]
    pub fn summary(&self) -> SojournSummary {
        SojournSummary {
            messages_seen: self.messages_seen,
            messages_over_budget: self.messages_over_budget,
            extremes: (self.messages_seen > 0).then_some((self.min_sojourn, self.max_sojourn)),
            total_sojourn: self.total_sojourn,
            is_backlogged: !self.within_budget_seen,
        }
    }

    /// Returns the summary of the messages since the previous `take` and
    /// starts a new period. When to call it is yours: a timer, a message
    /// count, an event.
    #[inline]
    pub fn take(&mut self) -> SojournSummary {
        let summary = self.summary();
        self.reset();
        summary
    }

    /// As if freshly built. `budget` is kept.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new(self.budget);
    }
}

/// A count of nanoseconds as a `Duration`, or the longest one if it does
/// not fit.
#[inline]
fn duration_from_nanos(nanos: u128) -> Duration {
    const NANOS_PER_SECOND: u128 = 1_000_000_000;
    let Ok(seconds) = u64::try_from(nanos / NANOS_PER_SECOND) else {
        return Duration::MAX;
    };
    Duration::new(seconds, (nanos % NANOS_PER_SECOND) as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    const BUDGET: Duration = Duration::from_nanos(50);

    fn ns(n: u64) -> Duration {
        Duration::from_nanos(n)
    }

    fn fed(sojourns: &[u64]) -> SojournSaturation {
        let mut sat = SojournSaturation::new(BUDGET);
        for &sojourn in sojourns {
            sat.update(ns(sojourn));
        }
        sat
    }

    /// An empty period has no shortest or longest sojourn and no mean.
    #[test]
    fn an_empty_period_has_no_sojourn_to_report() {
        let s = SojournSaturation::new(BUDGET).take();
        assert_eq!((s.messages_seen(), s.messages_over_budget()), (0, 0));
        assert_eq!(
            (s.min_sojourn(), s.max_sojourn(), s.mean_sojourn()),
            (None, None, None)
        );
        assert_eq!(s.total_sojourn(), Duration::ZERO);
        assert!(s.is_backlogged());
    }

    #[test]
    fn a_single_message() {
        let s = fed(&[12]).take();
        assert_eq!((s.messages_seen(), s.messages_over_budget()), (1, 0));
        assert_eq!(
            (s.min_sojourn(), s.max_sojourn(), s.mean_sojourn()),
            (Some(ns(12)), Some(ns(12)), Some(ns(12)))
        );
        assert_eq!(s.total_sojourn(), ns(12));
        assert!(!s.is_backlogged());
    }

    #[test]
    fn the_readings_over_several_messages() {
        let s = fed(&[30, 75, 10, 51]).take();
        assert_eq!((s.messages_seen(), s.messages_over_budget()), (4, 2));
        assert_eq!(
            (s.min_sojourn(), s.max_sojourn()),
            (Some(ns(10)), Some(ns(75)))
        );
        assert_eq!(s.total_sojourn(), ns(166));
        assert_eq!(s.mean_sojourn(), Some(ns(41))); // 166 / 4, to the nanosecond below
        assert!(!s.is_backlogged());
    }

    /// At the budget is within budget; one nanosecond over is over.
    #[test]
    fn over_budget_is_strictly_above() {
        let s = fed(&[50, 51, 49]).take();
        assert_eq!(s.messages_over_budget(), 1);
        assert!(
            !s.is_backlogged(),
            "a message at the budget drained the queue"
        );
    }

    #[test]
    fn backlogged_only_when_nothing_was_within_budget() {
        assert!(fed(&[60, 70, 80]).take().is_backlogged());
        assert!(
            !fed(&[60, 70, 50, 80]).take().is_backlogged(),
            "one message at the budget: the queue drained once"
        );
    }

    /// Clock skew arrives as a zero sojourn (`since` returns zero when the
    /// dequeue time is not after the enqueue time) and shows as a zero
    /// floor.
    #[test]
    fn clock_skew_reads_as_a_zero_floor() {
        use nexus_stats_core::Tick;

        let mut sat = SojournSaturation::new(BUDGET);
        sat.update(130_i64.since(100));
        sat.update(100_i64.since(1_100)); // dequeued "before" it was enqueued
        sat.update(140_i64.since(100));
        let s = sat.take();
        assert_eq!(s.min_sojourn(), Some(Duration::ZERO));
        assert_eq!(s.total_sojourn(), ns(70));
        assert_eq!(s.messages_over_budget(), 0);
    }

    #[test]
    fn the_total_stops_at_the_longest_duration() {
        let mut sat = SojournSaturation::new(BUDGET);
        sat.update(Duration::MAX);
        sat.update(Duration::from_secs(1));
        let s = sat.take();
        assert_eq!(s.total_sojourn(), Duration::MAX);
        assert_eq!(s.max_sojourn(), Some(Duration::MAX));
        assert_eq!(s.messages_over_budget(), 2);
        // The mean of a total that large still fits.
        assert_eq!(
            s.mean_sojourn(),
            Some(duration_from_nanos(Duration::MAX.as_nanos() / 2))
        );
    }

    /// `summary` reads the period so far and changes nothing. `take`
    /// returns the same and starts a new period.
    #[test]
    fn summary_peeks_and_take_snaps() {
        let mut sat = fed(&[20, 90]);
        let peeked = sat.summary();
        assert_eq!(
            (peeked.messages_seen(), peeked.max_sojourn()),
            (2, Some(ns(90)))
        );
        assert_eq!(sat.summary(), peeked);
        sat.update(ns(5));
        let later = sat.summary();
        assert_eq!(
            (later.messages_seen(), later.min_sojourn()),
            (3, Some(ns(5)))
        );
        assert_eq!(sat.take(), later);
        assert_eq!(sat.summary().messages_seen(), 0);
        assert_eq!(sat.summary().min_sojourn(), None);
    }

    #[test]
    fn take_starts_a_new_period_and_reset_does_too() {
        let mut sat = fed(&[60, 70]);
        let first = sat.take();
        assert!(first.is_backlogged());
        sat.update(ns(10));
        let second = sat.take();
        assert_eq!(
            (second.messages_seen(), second.max_sojourn()),
            (1, Some(ns(10)))
        );
        sat.update(ns(99));
        sat.reset();
        assert_eq!(sat.take().messages_seen(), 0);
    }

    /// Reading a long period in pieces loses nothing: the pieces add up to
    /// the whole.
    #[test]
    fn periods_split_anywhere_add_up_to_the_whole() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut sojourns = [0u64; 400];
        for sojourn in &mut sojourns {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *sojourn = state % 120;
        }
        let whole = fed(&sojourns).take();
        for cut in [1, 7, 133, 399] {
            let (a, b) = sojourns.split_at(cut);
            let (a, b) = (fed(a).take(), fed(b).take());
            assert_eq!(a.messages_seen() + b.messages_seen(), whole.messages_seen());
            assert_eq!(
                a.messages_over_budget() + b.messages_over_budget(),
                whole.messages_over_budget()
            );
            assert_eq!(a.total_sojourn() + b.total_sojourn(), whole.total_sojourn());
            assert_eq!(a.min_sojourn().min(b.min_sojourn()), whole.min_sojourn());
            assert_eq!(a.max_sojourn().max(b.max_sojourn()), whole.max_sojourn());
            assert_eq!(
                a.is_backlogged() && b.is_backlogged(),
                whole.is_backlogged()
            );
        }
    }
}
