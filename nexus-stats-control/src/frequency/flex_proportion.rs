//! Flexible proportions: each local's share of a decaying global count,
//! after the Linux kernel's `lib/flex_proportions.c`.

use nexus_stats_core::ConfigError;

/// The global side of a flexible-proportion pair: a decaying event count and
/// the current decay period. One per population; it drives every
/// [`FlexProportionLocal`] that belongs to it.
///
/// After the Linux kernel's `fprop_global` (`lib/flex_proportions.c`), where
/// it apportions dirty pages among cgroups. Every `half_life_events` updates
/// the period advances and the global count halves; a local halves the same
/// number of times, lazily, the next time it is touched. `local / global` is
/// therefore each local's share of *recent* events, and the shares of all
/// locals sum to one (up to the integer halving). The kernel advances the
/// period from a timer; here the period is event-driven, which keeps the type
/// clock-free and deterministic.
///
/// # Protocol
///
/// One call per event, on the global, naming the local it belongs to; queries
/// go through the local with a reference to its global:
///
/// ```
/// use nexus_stats_control::frequency::{FlexProportionGlobal, FlexProportionLocal};
///
/// let mut global = FlexProportionGlobal::new(1_000).unwrap(); // half-life: 1000 events
/// let mut venue_a = FlexProportionLocal::new();
/// let mut venue_b = FlexProportionLocal::new();
///
/// for _ in 0..300 {
///     global.update(&mut venue_a);
/// }
/// global.update(&mut venue_b);
///
/// let share_a = venue_a.fraction(&global); // about 300 / 301
/// let share_b = venue_b.fraction(&global); // about 1 / 301
/// assert!((share_a + share_b - 1.0).abs() < 1e-9);
/// ```
///
/// Store locals wherever the keys live (a map, an array, a struct field);
/// they borrow nothing from the global. 40 bytes for the global, 16 per
/// local; O(1) per update and per query; no allocation; `no_std`.
///
/// # Weighting clock
///
/// Per `update` call: the half-life is counted in events, not time. A quiet
/// population keeps its last shares until events arrive.
#[derive(Debug, Clone)]
pub struct FlexProportionGlobal {
    /// Decayed event count: halved once per period.
    events: u64,
    /// Current decay period.
    period: u64,
    /// Events per period.
    half_life: u64,
    /// Events recorded since the period last advanced.
    since_period: u64,
    /// Updates ever recorded (not decayed).
    count: u64,
}

/// The local side of a flexible-proportion pair: one per tracked key (a
/// venue, a shard, a client). Holds its decayed event count and the period
/// it was last reconciled to.
///
/// After the kernel's `fprop_local_single`. Plain data (`Copy`): keep it in
/// a map or an array; it holds no reference to the global. Feed events
/// through [`FlexProportionGlobal::update`] and read the share with
/// [`fraction`](Self::fraction).
#[derive(Debug, Clone, Copy, Default)]
pub struct FlexProportionLocal {
    /// Decayed event count as of `period`.
    events: u64,
    /// Period `events` was last reconciled to.
    period: u64,
}

impl FlexProportionGlobal {
    /// Creates a global with the given half-life in events: every
    /// `half_life_events` updates, every count in the population halves.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `half_life_events` is zero.
    #[inline]
    pub fn new(half_life_events: u64) -> Result<Self, ConfigError> {
        if half_life_events == 0 {
            return Err(ConfigError::Invalid("half_life_events must be positive"));
        }
        Ok(Self {
            events: 0,
            period: 0,
            half_life: half_life_events,
            since_period: 0,
            count: 0,
        })
    }

    /// Records one event attributed to `local`.
    ///
    /// Reconciles the local to the current period, counts the event on both
    /// sides, and advances the period (halving the global count) once
    /// `half_life_events` events have been recorded in it. The kernel's
    /// `__fprop_inc_single` plus an event-driven `fprop_new_period`.
    #[inline]
    pub fn update(&mut self, local: &mut FlexProportionLocal) {
        local.reflect(self.period);
        local.events += 1;
        self.events += 1;
        self.count += 1;
        self.since_period += 1;
        if self.since_period == self.half_life {
            self.events >>= 1;
            self.period += 1;
            self.since_period = 0;
        }
    }

    /// Decayed event count of the whole population: the denominator of every
    /// local's fraction.
    #[inline]
    #[must_use]
    pub fn events(&self) -> u64 {
        self.events
    }

    /// Current decay period: how many times the counts have halved. `reset`
    /// advances it by 64, so locals from before the reset read as zero.
    #[inline]
    #[must_use]
    pub fn period(&self) -> u64 {
        self.period
    }

    /// Events per period, as configured.
    #[inline]
    #[must_use]
    pub fn half_life_events(&self) -> u64 {
        self.half_life
    }

    /// Updates recorded since construction or the last `reset`, undecayed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one event has been recorded.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Clears the population. Locals that belonged to it read as zero until
    /// they are updated again, and should be reset or dropped alongside.
    ///
    /// The period jumps forward by 64 rather than back to zero: a local
    /// reads `events >> (global.period - local.period)` and zero once that
    /// gap reaches 64, so every existing local is zero by construction, and
    /// no later growth of the global can land on a stale local's period.
    #[inline]
    pub fn reset(&mut self) {
        self.events = 0;
        self.period += u64::from(u64::BITS);
        self.since_period = 0;
        self.count = 0;
    }
}

impl FlexProportionLocal {
    /// Creates an empty local.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            events: 0,
            period: 0,
        }
    }

    /// This local's share of `global`'s recent events, `0.0` to `1.0`; `0.0`
    /// while the population is empty.
    ///
    /// The kernel's `fprop_fraction_single`: the local's count, decayed to
    /// the global's period, over the global's count, clamped so that integer
    /// halving can never report more than one.
    #[inline]
    #[must_use]
    pub fn fraction(&self, global: &FlexProportionGlobal) -> f64 {
        let den = global.events;
        if den == 0 {
            return 0.0;
        }
        let num = self.events_at(global.period).min(den);
        num as f64 / den as f64
    }

    /// This local's decayed event count, as of `global`'s current period.
    #[inline]
    #[must_use]
    pub fn events(&self, global: &FlexProportionGlobal) -> u64 {
        self.events_at(global.period)
    }

    /// Clears this local.
    #[inline]
    pub fn reset(&mut self) {
        self.events = 0;
        self.period = 0;
    }

    /// The count this local would hold once reconciled to `period`: halved
    /// once per elapsed period, zero past 63 of them. A local that is
    /// *ahead* of the period belongs to a population that was reset since it
    /// was last touched; its count is stale and reads as zero. The kernel's
    /// `fprop_reflect_period_single`, without the write.
    #[inline]
    fn events_at(&self, period: u64) -> u64 {
        match period.checked_sub(self.period) {
            Some(elapsed) if elapsed < u64::BITS as u64 => self.events >> elapsed,
            _ => 0,
        }
    }

    /// Reconciles this local to `period`.
    #[inline]
    fn reflect(&mut self, period: u64) {
        if self.period != period {
            self.events = self.events_at(period);
            self.period = period;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn feed(global: &mut FlexProportionGlobal, local: &mut FlexProportionLocal, n: usize) {
        for _ in 0..n {
            global.update(local);
        }
    }

    #[test]
    fn rejects_zero_half_life() {
        assert!(FlexProportionGlobal::new(0).is_err());
    }

    #[test]
    fn empty_population_reads_zero() {
        let global = FlexProportionGlobal::new(10).unwrap();
        let local = FlexProportionLocal::new();
        assert_eq!(local.fraction(&global), 0.0);
        assert_eq!(local.events(&global), 0);
        assert!(!global.is_primed());
    }

    #[test]
    fn sole_local_holds_the_whole_share_across_many_half_lives() {
        // The defect in the previous implementation: the global never decayed,
        // so this read 0.5 after one half-life and 0.01 after a hundred.
        let mut global = FlexProportionGlobal::new(100).unwrap();
        let mut only = FlexProportionLocal::new();
        for half_lives in 1..=200 {
            feed(&mut global, &mut only, 100);
            assert_eq!(global.period(), half_lives);
            assert_eq!(only.fraction(&global), 1.0, "after {half_lives} half-lives");
        }
        assert_eq!(global.count(), 20_000);
        assert!(
            global.events() < 400,
            "the global count stays bounded: {}",
            global.events()
        );
    }

    #[test]
    fn equal_locals_split_evenly_and_sum_to_one() {
        let mut global = FlexProportionGlobal::new(64).unwrap();
        let mut a = FlexProportionLocal::new();
        let mut b = FlexProportionLocal::new();
        for _ in 0..5_000 {
            global.update(&mut a);
            global.update(&mut b);
        }
        let (fa, fb) = (a.fraction(&global), b.fraction(&global));
        assert!((fa - 0.5).abs() < 0.02, "a = {fa}");
        assert!((fb - 0.5).abs() < 0.02, "b = {fb}");
        assert!(fa + fb <= 1.0 && fa + fb > 0.97, "sum = {}", fa + fb);
    }

    #[test]
    fn idle_local_decays_while_the_active_one_takes_over() {
        let mut global = FlexProportionGlobal::new(100).unwrap();
        let mut a = FlexProportionLocal::new();
        let mut b = FlexProportionLocal::new();
        feed(&mut global, &mut a, 1_000); // a owns the first ten half-lives
        assert_eq!(a.fraction(&global), 1.0);
        feed(&mut global, &mut b, 1_000); // then b owns the next ten
        assert!(a.fraction(&global) < 0.01, "a = {}", a.fraction(&global));
        assert!(b.fraction(&global) > 0.99, "b = {}", b.fraction(&global));
        // a was never touched during b's run: its count was decayed on read only.
        assert!(a.events(&global) <= 1);
    }

    #[test]
    fn ramp_up_is_gradual_and_monotone() {
        let mut global = FlexProportionGlobal::new(100).unwrap();
        let mut old = FlexProportionLocal::new();
        let mut new = FlexProportionLocal::new();
        feed(&mut global, &mut old, 1_000);
        let mut last = 0.0;
        for step in 0..10 {
            feed(&mut global, &mut new, 100);
            let f = new.fraction(&global);
            assert!(f >= last, "share must not shrink: {f} after {last}");
            if step < 5 {
                assert!(f > last, "share must grow early on: {f} after {last}");
            }
            last = f;
        }
        // After ten half-lives the old local's count has halved to nothing.
        assert!(last > 0.95 && last <= 1.0, "new = {last}");
    }

    #[test]
    fn a_local_left_for_64_periods_reads_zero() {
        let mut global = FlexProportionGlobal::new(1).unwrap(); // one event per period
        let mut a = FlexProportionLocal::new();
        let mut b = FlexProportionLocal::new();
        feed(&mut global, &mut a, 1_000);
        feed(&mut global, &mut b, 70);
        assert_eq!(a.events(&global), 0);
        assert_eq!(a.fraction(&global), 0.0);
    }

    #[test]
    fn reset_clears_both_sides() {
        let mut global = FlexProportionGlobal::new(10).unwrap();
        let mut a = FlexProportionLocal::new();
        feed(&mut global, &mut a, 25);
        global.reset();
        a.reset();
        assert_eq!(global.count(), 0);
        assert_eq!(global.events(), 0);
        assert_eq!(a.fraction(&global), 0.0);
        global.update(&mut a);
        assert_eq!(a.fraction(&global), 1.0);
    }

    #[test]
    fn local_from_before_a_global_reset_reads_zero_and_restarts() {
        let mut global = FlexProportionGlobal::new(10).unwrap();
        let mut stale = FlexProportionLocal::new();
        let mut fresh = FlexProportionLocal::new();
        feed(&mut global, &mut stale, 55); // period 5
        global.reset();
        // Not touched since the reset: zero, not a clamped 1.0.
        assert_eq!(stale.events(&global), 0);
        assert_eq!(stale.fraction(&global), 0.0);
        feed(&mut global, &mut fresh, 3);
        assert_eq!(stale.fraction(&global), 0.0);
        assert_eq!(fresh.fraction(&global), 1.0);
        // Its first update after the reset starts it from scratch.
        global.update(&mut stale);
        assert_eq!(stale.events(&global), 1);
        assert_eq!(global.events(), 4);
    }

    /// A reset taken before the first halving used to leave the stale
    /// local on the same period as the fresh global, handing its old count
    /// straight back as current.
    #[test]
    fn reset_inside_period_zero_does_not_hand_back_stale_counts() {
        let mut global = FlexProportionGlobal::new(10).unwrap();
        let mut stale = FlexProportionLocal::new();
        let mut fresh = FlexProportionLocal::new();
        feed(&mut global, &mut stale, 5); // still period 0
        global.reset();
        feed(&mut global, &mut fresh, 3);
        assert_eq!(stale.events(&global), 0);
        assert_eq!(stale.fraction(&global), 0.0);
        assert_eq!(fresh.fraction(&global), 1.0);
    }

    /// The global regrowing to the stale local's old period number must
    /// not revive it either.
    #[test]
    fn stale_local_stays_zero_when_the_global_regrows() {
        let mut global = FlexProportionGlobal::new(10).unwrap();
        let mut stale = FlexProportionLocal::new();
        let mut fresh = FlexProportionLocal::new();
        feed(&mut global, &mut stale, 55); // period 5
        global.reset();
        feed(&mut global, &mut fresh, 55); // five more halvings
        assert_eq!(stale.events(&global), 0);
        assert_eq!(stale.fraction(&global), 0.0);
        assert_eq!(fresh.fraction(&global), 1.0);
    }

    #[test]
    fn default_local_is_empty() {
        let global = FlexProportionGlobal::new(10).unwrap();
        assert_eq!(FlexProportionLocal::default().events(&global), 0);
    }
}
