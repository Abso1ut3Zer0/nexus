// Consumer saturation from per-message queue sojourn: the stamped twin of
// `PollSaturation`. Where that type bounds the wait from poll outcomes, this
// one takes the exact wait (dequeue tick minus enqueue tick, same clock) and
// summarizes it per period: how many waited past the budget, the floor, the
// worst, the total, and whether the queue ever drained to within budget.
//
// State: the budget, five accumulators and a flag. No clock.

/// Summary of the sojourns seen since the previous
/// [`SojournSaturation::take`].
///
/// Covers every message in that period. When to snap is the caller's
/// decision: a timer (every millisecond, every second), a count (every
/// 1,000 messages), or an event; the type keeps no clock.
///
/// Merges exactly as a plain fold: counts and totals add, `min` takes the
/// min, `max` the max, `is_backlogged` ANDs. A period with no messages is
/// the identity of every field (`u64::MAX` minimum, zero maximum and
/// total, `true` flag) and carries no information in them: read
/// `messages_seen` first.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SojournSummary {
    /// Messages seen in the period.
    pub messages_seen: u64,
    /// Of those, the messages whose sojourn exceeded `budget`.
    /// `messages_over_budget / messages_seen` is the fraction that waited
    /// past the budget.
    pub messages_over_budget: u64,
    /// Shortest sojourn, in the caller's tick unit: the floor, transit plus
    /// processing. `u64::MAX` when no message was seen. **Zero means the
    /// two clocks disagree**, because a real sojourn is never zero.
    pub min_sojourn_ticks: u64,
    /// Longest sojourn: the worst wait. Zero when no message was seen.
    pub max_sojourn_ticks: u64,
    /// Sum of all sojourns, saturating. [`mean_sojourn_ticks`] divides it by
    /// the count; divided by the period length it is the mean number of
    /// messages waiting (Little's law), the count form of saturation.
    ///
    /// [`mean_sojourn_ticks`]: Self::mean_sojourn_ticks
    pub total_sojourn_ticks: u64,
    /// No message within budget for the whole period: the queue stood the
    /// entire time. CoDel's standing queue with the period as the interval.
    /// Vacuously true for an empty period, as for
    /// [`PollSummary`](super::PollSummary).
    pub is_backlogged: bool,
}

impl SojournSummary {
    /// Mean sojourn in ticks (integer division), `None` when no message was
    /// seen.
    #[inline]
    #[must_use]
    pub fn mean_sojourn_ticks(&self) -> Option<u64> {
        self.total_sojourn_ticks.checked_div(self.messages_seen)
    }
}

/// Consumer saturation from per-message queue sojourn.
///
/// Feed it each message's sojourn: the tick it was dequeued minus the tick
/// it was enqueued, both from the same clock. Integer ticks in any unit. It
/// answers, per period, how many messages waited past your budget, how long
/// the worst waited, what the floor was, and whether the queue ever drained.
///
/// This is the exact form of what [`PollSaturation`](super::PollSaturation)
/// bounds without stamps. Use this when messages carry an enqueue tick on
/// the same clock (our queues and shared memory, or an exchange timestamp
/// for upstream lag); use `PollSaturation` when they do not. The two share
/// vocabulary: `budget`, `messages_seen`, `messages_over_budget`,
/// `is_backlogged`, snap by `take`.
///
/// # Reading it
///
/// A sojourn is never zero on a healthy system: there is always transit and
/// processing. What matters is whether it stays near its floor or grows.
///
/// | Field | Healthy |
/// |---|---|
/// | `messages_over_budget / messages_seen` | near zero |
/// | `min_sojourn_ticks` | small and stable; **zero means the clocks disagree** |
/// | `max_sojourn_ticks` | under budget |
/// | `mean_sojourn_ticks()` | close to the minimum |
/// | `is_backlogged` | false |
///
/// `total_sojourn_ticks / period length` is the mean number of messages
/// waiting (Little's law), so this type also yields the count form of
/// saturation; healthy is well under 1.
///
/// # Clocks and stamps
///
/// The stamp and the dequeue tick must come from the same clock. For
/// in-process and same-host producers that is one monotonic or wall clock
/// and the sojourn is exact. Across hosts a wall-clock offset shifts every
/// sojourn by the same amount; the minimum absorbs it and the over-budget
/// count must be read against it. Subtract in a signed type and pass the
/// difference: with `i128` wall-clock nanoseconds, `(now - enqueued) as
/// i64` (the difference fits `i64` for 292 years); with `u64` ticks,
/// `now.wrapping_sub(enqueued) as i64`, which is the signed difference.
/// Never a plain `u64` subtraction, which underflows on skew into a huge
/// positive wait. A negative difference is clock skew; it is clamped to
/// zero, which then shows up as a zero minimum.
///
/// # Knobs
///
/// `budget`, and when you snap. No interval, no target, no baseline window,
/// no smoothing. [`CoDelI64`](super::CoDelI64) stays for callers who want
/// the RFC detector to drive a control decision; this type is the
/// observability summary. Smoothing belongs on the outputs, once per
/// summary.
///
/// # Weighting clock
///
/// Per message. Nothing is weighted by time or by loop iteration.
#[derive(Debug, Clone)]
pub struct SojournSaturation {
    budget: u64,
    messages_seen: u64,
    messages_over_budget: u64,
    /// `u64::MAX` until the first message of the period.
    min_sojourn: u64,
    max_sojourn: u64,
    total_sojourn: u64,
    within_budget_seen: bool,
}

impl SojournSaturation {
    /// Creates a monitor.
    ///
    /// `budget` is the sojourn, in ticks, above which a message counts
    /// toward [`SojournSummary::messages_over_budget`]: the wait you
    /// consider late.
    #[inline]
    #[must_use]
    pub const fn new(budget: u64) -> Self {
        Self {
            budget,
            messages_seen: 0,
            messages_over_budget: 0,
            min_sojourn: u64::MAX,
            max_sojourn: 0,
            total_sojourn: 0,
            within_budget_seen: false,
        }
    }

    /// One message's sojourn: dequeue tick minus enqueue tick, same clock.
    ///
    /// A negative value is clock skew and is clamped to zero.
    #[inline]
    pub fn update(&mut self, sojourn: i64) {
        // Straight-line: a clamp, a count, a compare folded into each of the
        // over-budget count and the drained flag, a min, a max, a saturating
        // add. No branch; whether a message is over budget is unpredictable
        // exactly when it matters.
        let sojourn = sojourn.max(0) as u64;
        self.messages_seen += 1;
        self.messages_over_budget += (sojourn > self.budget) as u64;
        self.within_budget_seen |= sojourn <= self.budget;
        self.min_sojourn = self.min_sojourn.min(sojourn);
        self.max_sojourn = self.max_sojourn.max(sojourn);
        self.total_sojourn = self.total_sojourn.saturating_add(sojourn);
    }

    /// Returns the summary of the messages since the previous `take` and
    /// starts a new period. When to call it is yours: a timer, a message
    /// count, an event.
    #[inline]
    pub fn take(&mut self) -> SojournSummary {
        let summary = SojournSummary {
            messages_seen: self.messages_seen,
            messages_over_budget: self.messages_over_budget,
            min_sojourn_ticks: self.min_sojourn,
            max_sojourn_ticks: self.max_sojourn,
            total_sojourn_ticks: self.total_sojourn,
            is_backlogged: !self.within_budget_seen,
        };
        self.messages_seen = 0;
        self.messages_over_budget = 0;
        self.min_sojourn = u64::MAX;
        self.max_sojourn = 0;
        self.total_sojourn = 0;
        self.within_budget_seen = false;
        summary
    }

    /// As if freshly built. `budget` is kept.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new(self.budget);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const BUDGET: u64 = 50;

    // An empty period is the identity of every field: merging it into any
    // other summary changes nothing. It carries no information; readers
    // check `messages_seen` first.
    #[test]
    fn empty_period_is_the_merge_identity() {
        let mut sat = SojournSaturation::new(BUDGET);
        let s = sat.take();
        assert_eq!(s.messages_seen, 0);
        assert_eq!(s.messages_over_budget, 0);
        assert_eq!(s.min_sojourn_ticks, u64::MAX);
        assert_eq!(s.max_sojourn_ticks, 0);
        assert_eq!(s.total_sojourn_ticks, 0);
        assert_eq!(s.mean_sojourn_ticks(), None);
        assert!(s.is_backlogged);
    }

    #[test]
    fn single_sample() {
        let mut sat = SojournSaturation::new(BUDGET);
        sat.update(12);
        let s = sat.take();
        assert_eq!(s.messages_seen, 1);
        assert_eq!(s.messages_over_budget, 0);
        assert_eq!(s.min_sojourn_ticks, 12);
        assert_eq!(s.max_sojourn_ticks, 12);
        assert_eq!(s.total_sojourn_ticks, 12);
        assert_eq!(s.mean_sojourn_ticks(), Some(12));
        assert!(!s.is_backlogged);
    }

    // At the budget is within budget; one tick over is over.
    #[test]
    fn over_budget_is_strictly_above() {
        let mut sat = SojournSaturation::new(BUDGET);
        sat.update(50);
        sat.update(51);
        sat.update(49);
        let s = sat.take();
        assert_eq!(s.messages_over_budget, 1);
        assert!(
            !s.is_backlogged,
            "a message at the budget drained the queue"
        );
    }

    #[test]
    fn backlogged_only_when_nothing_was_within_budget() {
        let mut sat = SojournSaturation::new(BUDGET);
        for s in [60, 70, 80] {
            sat.update(s);
        }
        assert!(sat.take().is_backlogged);
        for s in [60, 70, 50, 80] {
            sat.update(s);
        }
        assert!(
            !sat.take().is_backlogged,
            "one message at the budget: the queue drained once"
        );
    }

    // Clock skew: a negative difference is clamped, and shows up as a zero
    // floor rather than poisoning the total.
    #[test]
    fn negative_sojourn_is_clock_skew_and_reads_as_a_zero_floor() {
        let mut sat = SojournSaturation::new(BUDGET);
        sat.update(30);
        sat.update(-1_000);
        sat.update(40);
        let s = sat.take();
        assert_eq!(s.min_sojourn_ticks, 0);
        assert_eq!(s.total_sojourn_ticks, 70);
        assert_eq!(s.messages_over_budget, 0);
    }

    #[test]
    fn mean_is_integer_division() {
        let mut sat = SojournSaturation::new(BUDGET);
        sat.update(10);
        sat.update(11);
        sat.update(11);
        assert_eq!(sat.take().mean_sojourn_ticks(), Some(10)); // 32 / 3
    }

    #[test]
    fn total_saturates_instead_of_wrapping() {
        let mut sat = SojournSaturation::new(BUDGET);
        sat.update(i64::MAX);
        sat.update(i64::MAX);
        sat.update(i64::MAX);
        let s = sat.take();
        assert_eq!(s.total_sojourn_ticks, u64::MAX);
        assert_eq!(s.max_sojourn_ticks, i64::MAX as u64);
    }

    #[test]
    fn take_starts_a_new_period() {
        let mut sat = SojournSaturation::new(BUDGET);
        sat.update(100);
        let _ = sat.take();
        sat.update(5);
        let s = sat.take();
        assert_eq!(s.min_sojourn_ticks, 5);
        assert_eq!(s.max_sojourn_ticks, 5);
        assert_eq!(s.messages_over_budget, 0);
        assert!(!s.is_backlogged);
    }

    #[test]
    fn reset_equals_fresh() {
        let mut sat = SojournSaturation::new(BUDGET);
        sat.update(100);
        sat.update(200);
        sat.reset();
        let mut fresh = SojournSaturation::new(BUDGET);
        sat.update(7);
        fresh.update(7);
        assert_eq!(sat.take(), fresh.take());
    }

    #[test]
    fn budget_zero_means_every_message_is_over() {
        let mut sat = SojournSaturation::new(0);
        sat.update(1);
        sat.update(0);
        let s = sat.take();
        assert_eq!(s.messages_over_budget, 1);
        assert!(
            !s.is_backlogged,
            "the zero sojourn was within a zero budget"
        );
    }

    #[test]
    fn layout() {
        // budget + five u64 accumulators + flag, natural alignment.
        let a = core::mem::align_of::<u64>();
        assert_eq!(
            core::mem::size_of::<SojournSaturation>(),
            (6usize * 8 + 1).next_multiple_of(a)
        );
        // two counts, min, max, total, flag.
        assert_eq!(
            core::mem::size_of::<SojournSummary>(),
            (5usize * 8 + 1).next_multiple_of(a)
        );
    }
}

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;

    const BUDGET: u64 = 50;

    /// The merge rule the docs promise: a plain fold, no special cases.
    fn merge(a: SojournSummary, b: SojournSummary) -> SojournSummary {
        SojournSummary {
            messages_seen: a.messages_seen + b.messages_seen,
            messages_over_budget: a.messages_over_budget + b.messages_over_budget,
            min_sojourn_ticks: a.min_sojourn_ticks.min(b.min_sojourn_ticks),
            max_sojourn_ticks: a.max_sojourn_ticks.max(b.max_sojourn_ticks),
            total_sojourn_ticks: a.total_sojourn_ticks.saturating_add(b.total_sojourn_ticks),
            is_backlogged: a.is_backlogged && b.is_backlogged,
        }
    }

    fn sojourns() -> impl Strategy<Value = Vec<i64>> {
        // Mostly near a floor of ~10 with occasional long waits and rare skew.
        prop::collection::vec(
            prop_oneof![6 => 8i64..=20, 3 => 20i64..=400, 1 => -50i64..=0],
            0..300,
        )
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        #[test]
        fn merge_is_exact(samples in sojourns(), cuts in prop::collection::btree_set(0usize..300, 0..5)) {
            let mut single = SojournSaturation::new(BUDGET);
            let mut split = SojournSaturation::new(BUDGET);
            let mut parts = Vec::new();
            for (i, &s) in samples.iter().enumerate() {
                if cuts.contains(&i) {
                    parts.push(split.take());
                }
                single.update(s);
                split.update(s);
            }
            parts.push(split.take());
            let merged = parts.into_iter().reduce(merge).unwrap();
            prop_assert_eq!(merged, single.take());
        }

        #[test]
        fn invariants(samples in sojourns()) {
            let mut sat = SojournSaturation::new(BUDGET);
            for &s in &samples {
                sat.update(s);
            }
            let s = sat.take();
            let clamped: Vec<u64> = samples.iter().map(|&x| x.max(0) as u64).collect();
            prop_assert_eq!(s.messages_seen, clamped.len() as u64);
            prop_assert_eq!(s.messages_over_budget, clamped.iter().filter(|&&x| x > BUDGET).count() as u64);
            prop_assert!(s.messages_over_budget <= s.messages_seen);
            prop_assert_eq!(s.min_sojourn_ticks, clamped.iter().copied().min().unwrap_or(u64::MAX));
            prop_assert_eq!(s.max_sojourn_ticks, clamped.iter().copied().max().unwrap_or(0));
            prop_assert_eq!(s.total_sojourn_ticks, clamped.iter().sum::<u64>());
            prop_assert_eq!(s.is_backlogged, clamped.iter().all(|&x| x > BUDGET));
            if let Some(mean) = s.mean_sojourn_ticks() {
                prop_assert!(s.min_sojourn_ticks <= mean && mean <= s.max_sojourn_ticks);
            }
        }
    }
}
