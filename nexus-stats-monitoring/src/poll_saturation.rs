// Consumer-side saturation from poll outcomes: the arrival-floor model.
//
// A consumer thread cannot see its input's depth on every transport, and
// its messages do not always carry a timestamp. What it can always do is
// prove the input empty: a poll that returned nothing, or a batch poll that
// returned fewer than it asked for. Every message taken after such a proof
// arrived after it, so "now minus the latest proof" bounds how long any
// message in a poll waited for this thread. That time is the floor and that
// difference is `behind`. Everything reported is a count, a maximum or a
// flag over `behind`, accumulated until the owner's timer calls `take`.

use core::hint::select_unpredictable;
use core::time::Duration;

use nexus_stats_core::Timestamp;

/// Summary of the polls in a period: what [`PollSaturation::take`] returns
/// for the period it closes, and what [`PollSaturation::summary`] returns
/// for the period so far.
///
/// Covers every poll in the period, not one poll. When to snap is the
/// caller's decision: on a timer (every millisecond, every second), on a
/// count (every 1,000 messages), or on an event (the end of a burst).
///
/// A healthy thread reads `max_messages_per_poll() <= 1` and
/// `max_backlog_messages() == 0`: no message ever queued behind another.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PollSummary {
    messages_seen: u64,
    messages_waited: u64,
    messages_over_budget: u64,
    max_backlog_messages: u64,
    max_behind: Duration,
    max_messages_per_poll: u64,
    is_fully_utilized: bool,
    is_backlogged: bool,
}

impl PollSummary {
    /// Messages taken in the period.
    #[inline]
    #[must_use]
    pub fn messages_seen(&self) -> u64 {
        self.messages_seen
    }

    /// Of those, the messages that waited for this thread: every message
    /// except the first unit of work after an empty poll. Non-zero is
    /// saturation.
    #[inline]
    #[must_use]
    pub fn messages_waited(&self) -> u64 {
        self.messages_waited
    }

    /// Of those, the messages taken with `behind > budget`.
    /// `messages_over_budget / messages_seen` is the fraction that waited
    /// past the budget, weighted by message.
    #[inline]
    #[must_use]
    pub fn messages_over_budget(&self) -> u64 {
        self.messages_over_budget
    }

    /// Most messages that waited without the thread once catching up
    /// (between two proofs of emptiness). Zero is healthy: nothing queued.
    /// Under a poll limit this is the depth measure, an upper bound on how
    /// many messages stood behind the one being processed.
    #[inline]
    #[must_use]
    pub fn max_backlog_messages(&self) -> u64 {
        self.max_backlog_messages
    }

    /// Largest `behind` returned by an `on_work` with `n > 0`: the longest
    /// stretch without catching up.
    #[inline]
    #[must_use]
    pub fn max_behind(&self) -> Duration {
        self.max_behind
    }

    /// Most messages returned by one poll. With polls that drain the input
    /// this is the queue-length high-water mark, and `<= 1` is healthy.
    /// Under a poll limit it pins at the limit and means "at least this
    /// deep".
    #[inline]
    #[must_use]
    pub fn max_messages_per_poll(&self) -> u64 {
        self.max_messages_per_poll
    }

    /// No empty poll in the period: the thread never waited for input, so
    /// utilization was 100%. Exact, not a heuristic.
    #[inline]
    #[must_use]
    pub fn is_fully_utilized(&self) -> bool {
        self.is_fully_utilized
    }

    /// The input was never proven empty in the period, so the consumer never
    /// caught up and the whole period lay inside one backlog. This is CoDel's
    /// "standing queue" with the period as the interval. A batch poller can be
    /// fully utilized without being backlogged: its short polls prove it
    /// caught up at each poll.
    #[inline]
    #[must_use]
    pub fn is_backlogged(&self) -> bool {
        self.is_backlogged
    }
}

/// Consumer-side saturation from poll outcomes and the caller's clock.
///
/// For one thread that polls an input, answers "is work waiting behind my
/// processing, and for how long at most?" using only what each poll
/// returned and a time the caller reads when work begins. No producer
/// cooperation, no message timestamps, no queue depth, no clock read on an
/// idle spin. The input can be anything you poll: a ring buffer, an
/// in-process channel, a shared-memory slot, a non-blocking socket, a
/// message-bus subscription.
///
/// # Saturation
///
/// Saturation of a consumer thread is work that has arrived for it and is
/// waiting because the thread is busy (the USE method's "extra work which
/// it can't service, often queued"). It has a count, how many are waiting,
/// and a duration, how long each waited. This type reports both per
/// `take` period: [`PollSummary::max_messages_per_poll`] and [`PollSummary::max_backlog_messages`]
/// for the count; `behind`, [`PollSummary::max_behind`],
/// [`PollSummary::messages_waited`] and [`PollSummary::messages_over_budget`] for the duration. Read
/// it beside the other two USE columns for the same thread:
///
/// | Column | Measure |
/// |---|---|
/// | Utilization | your sum of service time over the period; [`PollSummary::is_fully_utilized`] is exactly 100% |
/// | Saturation | this type |
/// | Errors | the transport's own counters: drops, gaps, disconnects |
///
/// When messages carry an enqueue stamp on the same clock, the duration is
/// exact and [`SojournSaturation`](super::SojournSaturation) measures it;
/// this type still supplies the count form and the idle flag.
///
/// # Model: the arrival floor
///
/// The one internal quantity is the floor: the latest time at which the
/// input was proven empty. Only two things move it:
///
/// - An empty poll ([`on_idle`](Self::on_idle)). The input had nothing, so
///   the floor becomes the stamp of the next unit of work. No clock is read.
/// - A short poll ([`on_drained`](Self::on_drained)). A batch poll that
///   returned fewer than its limit found the input empty when it finished.
///
/// A full poll (`n == limit`) proves nothing: the input may hold one more
/// message or a million. Every message taken arrived after the floor, so
/// `behind = now - floor` at a working poll is an upper bound on how long
/// any message in it waited. Zero is exact: the previous poll was empty and
/// nothing waited. RFC 8289 states the same observation with timestamps
/// (one packet with zero sojourn means no persistent queue); an empty poll
/// is that observation made without one.
///
/// Under a backlog with a poll limit every poll comes back full, no proof
/// arrives, and `behind` and `max_backlog_messages` grow until a short poll proves the
/// consumer caught up. That growth is the signal.
///
/// # Reading a summary
///
/// With utilization from the caller beside it:
///
/// | Utilization | Saturation | Meaning |
/// |---|---|---|
/// | low | `messages_over_budget == 0`, `max_messages_per_poll <= 1` | healthy |
/// | low | `messages_over_budget > 0` | bursts, hidden by averaging: absorb them (batch, defer non-critical work) |
/// | `is_fully_utilized` | `messages_over_budget > 0` | capacity: split the consumer, move work off the thread |
/// | not pegged | `is_backlogged` | service-time spikes keep a queue standing: find the slow path |
/// | any | `behind == 0` on a message that was late | the delay was upstream, before it reached this input |
///
/// The period is whatever you snap on: a timer, a message count, an event.
/// Maxima survive any period length; the `messages_over_budget / messages_seen` fraction is diluted
/// by a long one. Snap at the alert cadence (a second or less) and merge
/// for publishing. Smoothing, if wanted, goes on the outputs once per
/// summary, not inside.
///
/// # Call-site rules
///
/// 1. One monitor per consumer thread. With several inputs: `on_work` for
///    each poll that returned work, `on_idle` only after a pass in which
///    every input was polled and every one was empty.
/// 2. Stamp `on_work` when processing of what it reports begins. Inline
///    handlers call it per message with that message's own stamp, which is
///    the tighter form. One call per batch under-reports the later messages
///    of the batch by the batch's processing time.
/// 3. Report messages before the proof: `on_drained` describes the input
///    after the messages already reported.
/// 4. `on_drained` only on a real proof, with a stamp no later than the
///    moment the input was found empty. A stamp taken before the poll is
///    always safe; the last handler-entry stamp is safe when the transport
///    consumes a message, runs the handler, then checks for the next. Some
///    transports return short for reasons other than emptiness (the end of a
///    buffer segment, a fragment limit): there, treat an empty poll as a
///    proof only when the poll before it was also empty, and never a short
///    one.
/// 5. Report work that is not a message with `on_work(start, 0)`, or accept
///    the slack it leaves.
/// 6. `take` from the owner's timer, on the same thread.
///
/// Blocking consumers have the same bit, hidden: a blocking receive that
/// blocked saw an empty input (`on_idle` before the work), one that returned
/// immediately did not. Recover it with a non-blocking attempt first
/// (`Empty`, `WouldBlock`, `Pending` is the empty poll) or by timing the
/// call. Executor scheduling delay after a wake is a different resource and
/// does not appear here.
///
/// # Guarantees
///
/// Every error is in the direction of over-reporting:
///
/// - If `on_work` returns 0, no message it reports waited behind an earlier
///   poll's work (it arrived within one idle iteration of `now`).
/// - If it returns `b`, every message from that poll arrived at most `b`
///   plus that slack before `now`.
/// - Every message that arrived while the thread was working is in
///   `messages_waited`; every message older than `budget` plus slack at its
///   `on_work` is in `messages_over_budget`.
/// - Splitting any call sequence into periods and merging the summaries
///   gives the same `PollSummary` as one `take` at the end.
/// - `on_idle` reads no clock and performs one store.
///
/// What it cannot do: `behind` is a bound, not the wait (with one message
/// per poll it is the busy period so far, loose under sustained high
/// utilization; batch polls with `on_drained` tighten it, a same-clock
/// stamp makes it exact). It cannot see delay before a message became
/// visible to this poll. A false proof under-reports until the next true
/// one. Time must not go back: after a backwards step every bound reads zero
/// and every proof is ignored until the clock passes the floor again.
///
/// # Weighting clock
///
/// Counts are per message, maxima are over working polls. Nothing is
/// weighted by loop iteration: a detector sampled once per spin reads
/// "fine" through a second where most messages were late, because almost
/// every spin is empty.
#[derive(Debug, Clone)]
pub struct PollSaturation<T: Timestamp> {
    state: u8,
    /// The latest time the input was proven empty. `None` until the first
    /// work is stamped.
    floor: Option<T>,
    budget: Duration,
    /// Messages that have waited since the latest proof.
    backlog: u64,
    period: Period,
}

/// What a period has accumulated.
#[derive(Debug, Clone, Copy, Default)]
struct Period {
    messages_seen: u64,
    messages_waited: u64,
    messages_over_budget: u64,
    max_backlog_messages: u64,
    max_behind: Duration,
    max_messages_per_poll: u64,
}

impl<T: Timestamp> PollSaturation<T> {
    /// The floor is pending: an empty poll happened and no work has been
    /// stamped since. The next `on_work` stamp becomes the floor.
    const FRESH: u8 = 0b001;
    /// An empty poll happened in this period.
    const IDLE_SEEN: u8 = 0b010;
    /// The input was proven empty in this period.
    const PROOF_SEEN: u8 = 0b100;
    /// State right after an empty poll.
    const AFTER_IDLE: u8 = Self::FRESH | Self::IDLE_SEEN | Self::PROOF_SEEN;

    /// Creates a monitor.
    ///
    /// `budget` is the `behind` above which a message counts toward
    /// [`PollSummary::messages_over_budget`]: the wait you consider late.
    /// Starts as if an empty poll had just happened.
    #[inline]
    #[must_use]
    pub fn new(budget: Duration) -> Self {
        Self {
            state: Self::AFTER_IDLE,
            floor: None,
            budget,
            backlog: 0,
            period: Period::default(),
        }
    }

    /// The poll returned nothing. Reads no clock; one store.
    ///
    /// Asserts that every input this monitor covers was polled and was
    /// empty. The floor becomes the stamp of the next unit of work.
    #[inline]
    pub fn on_idle(&mut self) {
        self.state = Self::AFTER_IDLE;
    }

    /// `n` messages start processing at `now`. Returns `behind`.
    ///
    /// `behind` is an upper bound on how long any of them waited for this
    /// thread. Zero means the previous poll was empty: nothing waited. A
    /// `now` before the floor (a clock that went back) reads zero.
    ///
    /// `n == 0` records work that is not a message (a timer, a publish). It
    /// consumes the first-after-idle exemption and can start a run, but
    /// never changes `max_behind` or `max_messages_per_poll`.
    #[inline]
    pub fn on_work(&mut self, now: T, n: u64) -> Duration {
        // PERF: no branch in here. Whether the floor is pending is a coin
        // flip under mixed load, and a mispredict there cost more than the
        // whole function when measured.
        let fresh = self.state & Self::FRESH != 0;

        // A pending floor becomes this stamp and starts a new backlog.
        let floor = select_unpredictable(fresh, now, self.floor.unwrap_or(now));
        // The first unit of work after an empty poll did not wait; every
        // other message did.
        let waited = n.saturating_sub(u64::from(fresh));
        let backlog = select_unpredictable(fresh, 0, self.backlog) + waited;
        self.state &= !Self::FRESH;
        self.floor = Some(floor);
        self.backlog = backlog;
        let behind = now.since(floor);

        let period = &mut self.period;
        period.messages_seen += n;
        period.messages_waited += waited;
        period.messages_over_budget += select_unpredictable(behind > self.budget, n, 0);

        // Non-message work (`n == 0`) never moves the maxima.
        let message_behind = select_unpredictable(n > 0, behind, Duration::ZERO);
        period.max_backlog_messages = period.max_backlog_messages.max(backlog);
        period.max_behind = period.max_behind.max(message_behind);
        period.max_messages_per_poll = period.max_messages_per_poll.max(n);
        behind
    }

    /// The input was empty at `at`: a short batch poll.
    ///
    /// Asserts that every message taken from now on arrived after `at`.
    /// Call it after the `on_work` calls for that poll, with a stamp no
    /// later than the moment the input was found empty (see the call-site
    /// rules). An `at` before the current floor is ignored and does not
    /// count as a proof for [`PollSummary::is_backlogged`]. While the floor is
    /// pending after an empty poll, the pending floor is the later proof
    /// and `at` is ignored. Never calling this is sound; it only loosens
    /// the bound.
    #[inline]
    pub fn on_drained(&mut self, at: T) {
        if self.state & Self::FRESH != 0 {
            return;
        }
        if self.floor.is_some_and(|floor| at >= floor) {
            self.floor = Some(at);
            self.backlog = 0;
            self.state |= Self::PROOF_SEEN;
        }
    }

    /// The summary of the period so far. Changes nothing, so it can be read
    /// after any series of polls, to alert on, while `take` keeps its own
    /// cadence.
    #[inline]
    #[must_use]
    pub fn summary(&self) -> PollSummary {
        PollSummary {
            messages_seen: self.period.messages_seen,
            messages_waited: self.period.messages_waited,
            messages_over_budget: self.period.messages_over_budget,
            max_backlog_messages: self.period.max_backlog_messages,
            max_behind: self.period.max_behind,
            max_messages_per_poll: self.period.max_messages_per_poll,
            is_fully_utilized: self.state & Self::IDLE_SEEN == 0,
            is_backlogged: self.state & Self::PROOF_SEEN == 0,
        }
    }

    /// Returns the summary of the polls since the previous `take` and
    /// starts a new period. When to call it is yours: a timer, a message
    /// count, an event. The floor and the current run carry over. A period
    /// that begins with the floor pending counts as having seen idle.
    #[inline]
    pub fn take(&mut self) -> PollSummary {
        let summary = self.summary();
        self.period = Period::default();
        self.state = if self.state & Self::FRESH != 0 {
            Self::AFTER_IDLE
        } else {
            0
        };
        summary
    }

    /// As if freshly built. `budget` is kept.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new(self.budget);
    }
}

/// `on_work` returning nanoseconds, for tests written in integer times.
#[cfg(test)]
fn work(sat: &mut PollSaturation<i128>, now: u64, n: u64) -> u64 {
    u64::try_from(sat.on_work(i128::from(now), n).as_nanos()).unwrap()
}

/// `on_drained` at an integer time.
#[cfg(test)]
fn drained(sat: &mut PollSaturation<i128>, at: u64) {
    sat.on_drained(i128::from(at));
}

/// A span of `n` nanoseconds.
#[cfg(test)]
fn ns(n: u64) -> Duration {
    Duration::from_nanos(n)
}

#[cfg(test)]
mod tests {
    use super::*;

    const BUDGET: u64 = 50;

    /// `summary!(seen, waited, over_budget, max_backlog, max_behind, max_per_poll, fully_utilized, backlogged)`
    macro_rules! summary {
        ($m:expr, $q:expr, $o:expr, $r:expr, $b:expr, $n:expr, $ni:expr, $ne:expr) => {
            PollSummary {
                messages_seen: $m,
                messages_waited: $q,
                messages_over_budget: $o,
                max_backlog_messages: $r,
                max_behind: ns($b),
                max_messages_per_poll: $n,
                is_fully_utilized: $ni,
                is_backlogged: $ne,
            }
        };
    }

    // The worked trace from the ticket, field by field.
    #[test]
    fn worked_trace() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        assert_eq!(work(&mut sat, 100, 1), 0); // first after an empty poll: did not wait
        assert_eq!(work(&mut sat, 103, 1), 3); // arrived while the first was processed
        assert_eq!(work(&mut sat, 106, 1), 6);
        sat.on_idle(); // caught up
        assert_eq!(work(&mut sat, 200, 3), 0); // three at once: two count as queued
        assert_eq!(work(&mut sat, 209, 2), 9);
        drained(&mut sat, 209); // that poll was short
        assert_eq!(work(&mut sat, 290, 4), 81); // over the budget: all four count

        let a = sat.take();
        assert_eq!(a, summary!(12, 10, 4, 4, 81, 4, false, false));

        assert_eq!(work(&mut sat, 300, 1), 91); // the run carried across the window
        let b = sat.take();
        assert_eq!(b, summary!(1, 1, 1, 5, 91, 1, true, true));
    }

    /// One message per poll, each after an empty poll: nothing queued, so
    /// the backlog is zero and no poll held more than one.
    #[test]
    fn a_healthy_thread_reads_one_per_poll_and_no_backlog() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        for at in [100, 250, 400, 900] {
            sat.on_idle();
            assert_eq!(work(&mut sat, at, 1), 0);
        }
        let w = sat.take();
        assert_eq!(w, summary!(4, 0, 0, 0, 0, 1, false, false));
        assert_eq!(
            (w.max_messages_per_poll(), w.max_backlog_messages()),
            (1, 0)
        );
    }

    /// `summary` reads the period so far and changes nothing. `take`
    /// returns the same and starts a new period.
    #[test]
    fn summary_peeks_and_take_snaps() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        work(&mut sat, 100, 3);
        let first = sat.summary();
        assert_eq!(first, summary!(3, 2, 0, 2, 0, 3, false, false));
        assert_eq!(sat.summary(), first);
        // The period goes on after a peek.
        assert_eq!(work(&mut sat, 180, 2), 80);
        let peeked = sat.summary();
        assert_eq!(peeked, summary!(5, 4, 2, 4, 80, 3, false, false));
        assert_eq!(sat.take(), peeked);
        // A new period: the counts start over and the run carries on.
        assert_eq!(sat.summary(), summary!(0, 0, 0, 0, 0, 0, true, true));
        assert_eq!(work(&mut sat, 190, 1), 90);
        assert_eq!(sat.summary().max_backlog_messages(), 5);
    }

    /// Every reading through its accessor.
    #[test]
    fn the_accessors_read_the_summary() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        work(&mut sat, 100, 3);
        work(&mut sat, 180, 2);
        let w = sat.take();
        assert_eq!(
            (
                w.messages_seen(),
                w.messages_waited(),
                w.messages_over_budget()
            ),
            (5, 4, 2)
        );
        assert_eq!(
            (
                w.max_backlog_messages(),
                w.max_behind(),
                w.max_messages_per_poll()
            ),
            (4, ns(80), 3)
        );
        assert_eq!((w.is_fully_utilized(), w.is_backlogged()), (false, false));
    }

    #[cfg(feature = "std")]
    #[test]
    fn an_instant_and_nanoseconds_agree() {
        use std::time::Instant;
        let start = Instant::now();
        let mut on_instant = PollSaturation::<Instant>::new(ns(BUDGET));
        let mut on_nanos = PollSaturation::<i128>::new(ns(BUDGET));
        for (at, n, idle_first, proof) in [
            (100u64, 1u64, true, false),
            (103, 1, false, false),
            (200, 3, true, false),
            (209, 2, false, true),
            (290, 4, false, false),
            (40, 1, false, false), // the clock went back: reads zero
        ] {
            if idle_first {
                on_instant.on_idle();
                on_nanos.on_idle();
            }
            let a = on_instant.on_work(start + ns(at), n);
            let b = on_nanos.on_work(i128::from(at), n);
            assert_eq!(a, b, "at {at}");
            if proof {
                on_instant.on_drained(start + ns(at));
                on_nanos.on_drained(i128::from(at));
            }
        }
        assert_eq!(on_instant.take(), on_nanos.take());
    }

    #[test]
    fn first_after_idle_reads_zero_for_any_batch() {
        for n in [1u64, 2, 100] {
            let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
            sat.on_idle();
            assert_eq!(work(&mut sat, 1_000, n), 0);
            let w = sat.take();
            assert_eq!(w.messages_seen, n);
            assert_eq!(
                w.messages_waited,
                n - 1,
                "only the first of the batch did not wait"
            );
            assert_eq!(w.messages_over_budget, 0);
            assert_eq!(w.max_backlog_messages, n - 1);
            assert_eq!(w.max_messages_per_poll, n);
            assert_eq!(w.max_behind, ns(0));
        }
    }

    // Non-message work consumes the exemption: the message after it waited.
    #[test]
    fn other_work_starts_a_run() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        assert_eq!(work(&mut sat, 10, 0), 0);
        assert_eq!(work(&mut sat, 70, 1), 60);
        let w = sat.take();
        assert_eq!(w, summary!(1, 1, 1, 1, 60, 1, false, false));
    }

    #[test]
    fn non_message_work_never_moves_the_maxima() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        assert_eq!(work(&mut sat, 10, 0), 0);
        assert_eq!(work(&mut sat, 500, 0), 490);
        let w = sat.take();
        assert_eq!(w.max_behind, ns(0));
        assert_eq!(w.max_messages_per_poll, 0);
        assert_eq!(w.messages_seen, 0);
        assert_eq!(w.messages_over_budget, 0);
    }

    #[test]
    fn stale_proof_is_ignored() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        assert_eq!(work(&mut sat, 100, 1), 0);
        drained(&mut sat, 40); // older than the floor
        assert_eq!(work(&mut sat, 130, 1), 30, "floor stayed at 100");
    }

    // The pending floor after an empty poll is a later proof than any stamp
    // the caller can hold, so a drained proof while fresh changes nothing.
    #[test]
    fn proof_while_fresh_does_not_move_the_floor() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        drained(&mut sat, 50);
        assert_eq!(work(&mut sat, 100, 1), 0);
        assert_eq!(work(&mut sat, 110, 1), 10, "floor is 100, not 50");
    }

    #[test]
    fn short_poll_proof_tightens_the_bound() {
        let mut with = PollSaturation::<i128>::new(ns(BUDGET));
        let mut without = with.clone();
        for sat in [&mut with, &mut without] {
            sat.on_idle();
            work(sat, 200, 3);
            work(sat, 209, 2);
        }
        drained(&mut with, 209);
        assert_eq!(work(&mut without, 290, 4), 90);
        assert_eq!(work(&mut with, 290, 4), 81);
        assert_eq!(with.take().max_backlog_messages, 4);
        assert_eq!(
            without.take().max_backlog_messages,
            8,
            "no proof: one run, eight of the nine waited"
        );
    }

    // A proof stamped exactly at the floor adds no floor information but
    // is still a proof: the run restarts and the window has seen one.
    #[test]
    fn proof_at_the_floor_counts() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        work(&mut sat, 100, 1);
        let _ = sat.take(); // new window, floor 100, not fresh
        drained(&mut sat, 100);
        assert_eq!(work(&mut sat, 150, 1), 50);
        let w = sat.take();
        assert!(!w.is_backlogged);
        assert_eq!(w.max_backlog_messages, 1, "run restarted at the proof");
    }

    #[test]
    fn idle_is_idempotent() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        sat.on_idle();
        sat.on_idle();
        assert_eq!(work(&mut sat, 100, 1), 0);
        let w = sat.take();
        assert!(!w.is_fully_utilized);
        assert!(!w.is_backlogged);
    }

    // A backwards clock reads 0 and ignores proofs until it passes the
    // floor again. Blind, never a huge bound.
    #[test]
    fn backwards_clock_reads_zero_and_ignores_proofs() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        assert_eq!(work(&mut sat, 100, 1), 0);
        assert_eq!(work(&mut sat, 50, 1), 0);
        drained(&mut sat, 60); // behind the floor: ignored
        assert_eq!(work(&mut sat, 70, 1), 0);
        assert_eq!(work(&mut sat, 150, 1), 50, "measured from the floor of 100");
        assert_eq!(sat.take().max_behind, ns(50));
    }

    #[test]
    fn empty_period() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        work(&mut sat, 100, 1);
        let _ = sat.take();
        let w = sat.take();
        assert_eq!(w, summary!(0, 0, 0, 0, 0, 0, true, true));
    }

    // A window that begins with the floor pending counts as having seen
    // idle, so a consumer that is simply quiet never reads as pegged.
    #[test]
    fn window_beginning_idle_has_seen_idle() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        let _ = sat.take();
        let w = sat.take();
        assert!(!w.is_fully_utilized);
        assert!(!w.is_backlogged);
        // Once work has been stamped, a window without an empty poll is pegged.
        work(&mut sat, 30, 1);
        let _ = sat.take();
        let w = sat.take();
        assert!(w.is_fully_utilized);
        assert!(w.is_backlogged);
    }

    // Documents the per-message accounting trap: the proof stamp must not be
    // earlier than the work it follows, or it is stale and the window shows
    // a standing queue.
    #[test]
    fn earlier_proof_stamp_is_the_r7_trap() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        work(&mut sat, 101, 1);
        let _ = sat.take();
        drained(&mut sat, 100); // stamped before the work it describes
        let w = sat.take();
        assert!(w.is_backlogged);
        assert!(w.is_fully_utilized);
    }

    #[test]
    fn max_batch_pins_at_the_limit_and_max_run_keeps_growing() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        assert_eq!(work(&mut sat, 0, 10), 0);
        assert_eq!(work(&mut sat, 10, 10), 10);
        assert_eq!(work(&mut sat, 20, 10), 20);
        let w = sat.take();
        assert_eq!(w.max_messages_per_poll, 10);
        assert_eq!(w.max_backlog_messages, 29);
        assert_eq!(w.messages_waited, 29);
    }

    #[test]
    fn reset_equals_fresh() {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        sat.on_idle();
        work(&mut sat, 100, 5);
        work(&mut sat, 200, 5);
        sat.reset();
        let mut fresh = PollSaturation::<i128>::new(ns(BUDGET));
        assert_eq!(work(&mut sat, 600, 2), work(&mut fresh, 600, 2));
        assert_eq!(work(&mut sat, 700, 2), work(&mut fresh, 700, 2));
        assert_eq!(sat.take(), fresh.take());
    }

    #[test]
    fn false_proof_breaks_the_bound() {
        // Message 0 arrives at 0, message 1 at 5; service time 10.
        let mut honest = PollSaturation::<i128>::new(ns(BUDGET));
        let mut lying = honest.clone();
        assert_eq!(work(&mut honest, 0, 1), 0);
        assert_eq!(work(&mut lying, 0, 1), 0);
        drained(&mut lying, 9); // false: message 1 has been waiting since 5
        let age = 10 - 5;
        assert!(work(&mut honest, 10, 1) >= age);
        assert!(
            work(&mut lying, 10, 1) < age,
            "the false proof under-reports"
        );
    }
}

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::VecDeque;

    const BUDGET: u64 = 50;
    const IDLE_COST: u64 = 1;

    /// One recorded call, replayable into any number of monitors.
    #[derive(Clone, Copy, Debug)]
    enum Call {
        Idle,
        Work { now: u64, n: u64 },
        Drained { at: u64 },
    }

    /// One message at the moment its `on_work` ran. `slack` is the unstamped
    /// gap from the last empty poll to this stamp, zero when the floor was
    /// not pending.
    #[derive(Clone, Copy, Debug)]
    struct Obs {
        age: u64,
        behind: u64,
        slack: u64,
    }

    #[derive(Clone, Copy, Debug)]
    enum Shape {
        /// One message per poll.
        Single,
        /// Batch poll with a limit, one `on_work` per batch, `on_drained` on
        /// a short poll.
        Batch { limit: u64 },
        /// Inline handler: consume one, run it, check for the next. One
        /// `on_work` per message, `on_drained` at the last handler stamp.
        Inline { limit: u64 },
    }

    struct Run {
        calls: Vec<Call>,
        obs: Vec<Obs>,
        summary: PollSummary,
    }

    /// A single FIFO server over one input. `arrivals` are absolute ticks,
    /// non-decreasing; `service[i]` is message `i`'s processing time.
    fn simulate(arrivals: &[u64], service: &[u64], shape: Shape, proofs: bool) -> Run {
        let total = arrivals.len();
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        let mut calls = Vec::new();
        let mut obs = Vec::new();
        let mut queue: VecDeque<usize> = VecDeque::new();
        let mut next = 0usize; // first arrival not yet visible
        let mut t = 0u64; // consumer clock
        let mut last_empty = Some(0u64); // tick of the last empty check while the floor is pending

        let deliver = |t: u64, next: &mut usize, queue: &mut VecDeque<usize>| {
            while *next < total && arrivals[*next] <= t {
                queue.push_back(*next);
                *next += 1;
            }
        };

        loop {
            deliver(t, &mut next, &mut queue);
            if queue.is_empty() {
                if next == total {
                    break;
                }
                sat.on_idle();
                calls.push(Call::Idle);
                last_empty = Some(t);
                t += IDLE_COST;
                continue;
            }
            match shape {
                Shape::Single => {
                    let i = queue.pop_front().unwrap();
                    let now = t;
                    let behind = work(&mut sat, now, 1);
                    calls.push(Call::Work { now, n: 1 });
                    let slack = last_empty.take().map_or(0, |te| now - te);
                    obs.push(Obs {
                        age: now - arrivals[i],
                        behind,
                        slack,
                    });
                    t = now + service[i];
                }
                Shape::Batch { limit } => {
                    let n = queue.len().min(limit as usize);
                    let now = t;
                    let behind = work(&mut sat, now, n as u64);
                    calls.push(Call::Work { now, n: n as u64 });
                    let slack = last_empty.take().map_or(0, |te| now - te);
                    let mut busy = 0;
                    for _ in 0..n {
                        let i = queue.pop_front().unwrap();
                        obs.push(Obs {
                            age: now - arrivals[i],
                            behind,
                            slack,
                        });
                        busy += service[i];
                    }
                    if proofs && (n as u64) < limit {
                        // Everything visible at `now` was taken: empty at `now`.
                        drained(&mut sat, now);
                        calls.push(Call::Drained { at: now });
                    }
                    t = now + busy;
                }
                Shape::Inline { limit } => {
                    let mut taken = 0u64;
                    let mut last = t;
                    while taken < limit {
                        deliver(t, &mut next, &mut queue);
                        let Some(i) = queue.pop_front() else { break };
                        let now = t;
                        let behind = work(&mut sat, now, 1);
                        calls.push(Call::Work { now, n: 1 });
                        let slack = last_empty.take().map_or(0, |te| now - te);
                        obs.push(Obs {
                            age: now - arrivals[i],
                            behind,
                            slack,
                        });
                        last = now;
                        taken += 1;
                        t = now + service[i];
                    }
                    if proofs && taken < limit {
                        // The loop ended on an empty check after the last
                        // handler: nothing arrived since that handler began.
                        drained(&mut sat, last);
                        calls.push(Call::Drained { at: last });
                    }
                }
            }
        }
        let summary = sat.take();
        Run {
            calls,
            obs,
            summary,
        }
    }

    /// Replays `calls` into a fresh monitor, taking a summary before each
    /// call index in `takes` (sorted) and once more at the end.
    fn replay(calls: &[Call], takes: &[usize]) -> Vec<PollSummary> {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        let mut out = Vec::new();
        let mut ti = 0usize;
        for (i, call) in calls.iter().enumerate() {
            while ti < takes.len() && takes[ti] == i {
                out.push(sat.take());
                ti += 1;
            }
            match *call {
                Call::Idle => sat.on_idle(),
                Call::Work { now, n } => {
                    let _ = work(&mut sat, now, n);
                }
                Call::Drained { at } => drained(&mut sat, at),
            }
        }
        out.push(sat.take());
        out
    }

    /// The merge rule the docs promise: sums add, maxima max, flags AND.
    fn merge(a: PollSummary, b: PollSummary) -> PollSummary {
        PollSummary {
            messages_seen: a.messages_seen + b.messages_seen,
            messages_waited: a.messages_waited + b.messages_waited,
            messages_over_budget: a.messages_over_budget + b.messages_over_budget,
            max_backlog_messages: a.max_backlog_messages.max(b.max_backlog_messages),
            max_behind: a.max_behind.max(b.max_behind),
            max_messages_per_poll: a.max_messages_per_poll.max(b.max_messages_per_poll),
            is_fully_utilized: a.is_fully_utilized && b.is_fully_utilized,
            is_backlogged: a.is_backlogged && b.is_backlogged,
        }
    }

    /// A source that delivers in segments of `seg` messages and never reads
    /// across a segment end: the poll that lands on the boundary consumes it
    /// and returns 0 even when the next segment has data. Returns the number
    /// of bound violations under the chosen idle rule.
    fn simulate_segmented(
        arrivals: &[u64],
        service: &[u64],
        seg: usize,
        limit: usize,
        idle_after_two_empty: bool,
    ) -> usize {
        let total = arrivals.len();
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        let mut violations = 0usize;
        let mut pos = 0usize; // messages consumed
        let mut boundary_passed = 0usize; // boundaries already consumed
        let mut t = 0u64;
        let mut prev_empty = true;
        let mut last_empty = Some(0u64);
        loop {
            let visible = arrivals.iter().take_while(|&&a| a <= t).count();
            if pos == total {
                break;
            }
            // At a segment end: the boundary poll consumes the segment end and
            // returns 0, whether or not data is waiting beyond it.
            if pos > 0 && pos.is_multiple_of(seg) && boundary_passed < pos / seg {
                boundary_passed = pos / seg;
                if !idle_after_two_empty || prev_empty {
                    sat.on_idle();
                    last_empty = Some(t);
                }
                prev_empty = true;
                t += IDLE_COST;
                continue;
            }
            if visible == pos {
                if !idle_after_two_empty || prev_empty {
                    sat.on_idle();
                    last_empty = Some(t);
                }
                prev_empty = true;
                t += IDLE_COST;
                continue;
            }
            // Read within the segment, up to the limit.
            let seg_end = (pos / seg + 1) * seg;
            let n = (visible - pos).min(limit).min(seg_end - pos);
            let now = t;
            let behind = work(&mut sat, now, n as u64);
            let slack = last_empty.take().map_or(0, |te| now - te);
            let mut busy = 0;
            for i in pos..pos + n {
                if now - arrivals[i] > behind + slack {
                    violations += 1;
                }
                busy += service[i];
            }
            pos += n;
            prev_empty = false;
            t = now + busy;
        }
        violations
    }

    /// Two inputs on one monitor. Input A is polled every pass, input B
    /// every `k`-th pass; `on_idle` only after a pass that polled both and
    /// found both empty (`idle_rule_full_pass`), or after any empty A poll
    /// (the wrong rule). Returns bound violations.
    ///
    /// With inputs on different cadences the floor set by one input's work
    /// is not a proof for the other, so the bound is allowed the spec's
    /// "one polling cycle of slack": the time from the found input's last
    /// empty check to the floor stamp. The wrong rule exceeds that.
    fn simulate_two_inputs(
        a: &[u64],
        b: &[u64],
        service: u64,
        k: usize,
        idle_rule_full_pass: bool,
    ) -> usize {
        let mut sat = PollSaturation::<i128>::new(ns(BUDGET));
        let mut violations = 0usize;
        let (mut ia, mut ib) = (0usize, 0usize);
        let mut t = 0u64;
        let mut pass = 0usize;
        let mut last_idle = Some(0u64); // the floor is pending since this tick
        let mut floor_at = 0u64; // stamp of the first work after the last idle
        let (mut checked_a, mut checked_b) = (0u64, 0u64); // last empty check per input

        let found_on = |sat: &mut PollSaturation<i128>,
                        now: u64,
                        arrived: u64,
                        checked: u64,
                        last_idle: &mut Option<u64>,
                        floor_at: &mut u64,
                        violations: &mut usize| {
            let behind = work(sat, now, 1);
            let (slack, allowance) = match last_idle.take() {
                Some(te) => {
                    *floor_at = now;
                    (now - te, 0)
                }
                None => (0, floor_at.saturating_sub(checked)),
            };
            if now - arrived > behind + slack + allowance {
                *violations += 1;
            }
        };

        while ia < a.len() || ib < b.len() {
            let polls_b = pass.is_multiple_of(k);
            let mut found = false;
            // Poll A.
            t += 1;
            if ia < a.len() && a[ia] <= t {
                let now = t;
                found_on(
                    &mut sat,
                    now,
                    a[ia],
                    checked_a,
                    &mut last_idle,
                    &mut floor_at,
                    &mut violations,
                );
                ia += 1;
                found = true;
                t = now + service;
            } else {
                checked_a = t;
            }
            // Poll B on its cadence.
            let mut b_empty = true;
            if polls_b {
                t += 1;
                if ib < b.len() && b[ib] <= t {
                    let now = t;
                    found_on(
                        &mut sat,
                        now,
                        b[ib],
                        checked_b,
                        &mut last_idle,
                        &mut floor_at,
                        &mut violations,
                    );
                    ib += 1;
                    found = true;
                    b_empty = false;
                    t = now + service;
                } else {
                    checked_b = t;
                }
            }
            if !found && (!idle_rule_full_pass || (polls_b && b_empty)) {
                sat.on_idle();
                last_idle = Some(t);
            }
            pass += 1;
        }
        violations
    }

    fn arrivals_from_gaps(gaps: &[u64]) -> Vec<u64> {
        let mut t = 0u64;
        gaps.iter()
            .map(|g| {
                t += g;
                t
            })
            .collect()
    }

    fn traffic() -> impl Strategy<Value = (Vec<u64>, Vec<u64>)> {
        // Gaps: mostly bursts (0..=2) with occasional long pauses; service 1..=12.
        prop::collection::vec(
            (prop_oneof![3 => 0u64..=2, 1 => 0u64..=120], 1u64..=12),
            1..200,
        )
        .prop_map(|pairs| {
            let gaps: Vec<u64> = pairs.iter().map(|p| p.0).collect();
            let service: Vec<u64> = pairs.iter().map(|p| p.1).collect();
            (arrivals_from_gaps(&gaps), service)
        })
    }

    fn shape() -> impl Strategy<Value = Shape> {
        prop_oneof![
            Just(Shape::Single),
            (1u64..=8).prop_map(|limit| Shape::Batch { limit }),
            (1u64..=8).prop_map(|limit| Shape::Inline { limit }),
        ]
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(400))]

        // P1 bound, P2 zero, P3 counts.
        #[test]
        fn bound_zero_and_counts_hold((arrivals, service) in traffic(), shape in shape(), proofs in any::<bool>()) {
            let run = simulate(&arrivals, &service, shape, proofs);
            let mut truth_queued = 0u64;
            let mut truth_over = 0u64;
            for o in &run.obs {
                prop_assert!(o.age <= o.behind + o.slack, "age {} > behind {} + slack {}", o.age, o.behind, o.slack);
                if o.behind == 0 {
                    prop_assert!(o.age <= o.slack);
                }
                if o.age > o.slack { truth_queued += 1; }
                if o.age > BUDGET + o.slack { truth_over += 1; }
            }
            let w = run.summary;
            prop_assert_eq!(w.messages_seen, run.obs.len() as u64);
            prop_assert!(w.messages_waited >= truth_queued);
            prop_assert!(w.messages_over_budget >= truth_over);
            prop_assert!(w.messages_waited <= w.messages_seen);
            prop_assert!(w.messages_over_budget <= w.messages_seen);
            prop_assert!(w.max_messages_per_poll <= w.messages_seen.max(1));
        }

        // P4 merge: any split, merged, equals one take.
        #[test]
        fn windows_merge_exactly((arrivals, service) in traffic(), shape in shape(), cuts in prop::collection::btree_set(0usize..400, 0..6)) {
            let run = simulate(&arrivals, &service, shape, true);
            let takes: Vec<usize> = cuts.into_iter().filter(|&c| c < run.calls.len()).collect();
            let single = replay(&run.calls, &[]);
            let split = replay(&run.calls, &takes);
            let merged = split.into_iter().reduce(merge).unwrap();
            prop_assert_eq!(merged, single[0]);
        }

        // P5 proofs only tighten.
        #[test]
        fn proofs_only_tighten((arrivals, service) in traffic(), limit in 1u64..=8, inline in any::<bool>()) {
            let shape = if inline { Shape::Inline { limit } } else { Shape::Batch { limit } };
            let with = simulate(&arrivals, &service, shape, true);
            let without = simulate(&arrivals, &service, shape, false);
            prop_assert_eq!(with.obs.len(), without.obs.len());
            for (a, b) in with.obs.iter().zip(&without.obs) {
                prop_assert!(b.behind >= a.behind);
            }
            prop_assert!(without.summary.max_backlog_messages >= with.summary.max_backlog_messages);
        }

        // P7 segmented source: idle only after two consecutive empty polls.
        #[test]
        fn segmented_source_holds_under_the_two_empty_rule((arrivals, service) in traffic(), seg in 1usize..=5, limit in 1usize..=8) {
            prop_assert_eq!(simulate_segmented(&arrivals, &service, seg, limit, true), 0);
        }

        // P8 several inputs: idle only after a pass that polled every input.
        #[test]
        fn two_inputs_hold_when_idle_follows_a_full_pass(
            ga in prop::collection::vec(0u64..=40, 0..60),
            gb in prop::collection::vec(0u64..=40, 0..60),
            service in 1u64..=10,
            k in 1usize..=4,
        ) {
            let a = arrivals_from_gaps(&ga);
            let b = arrivals_from_gaps(&gb);
            prop_assert_eq!(simulate_two_inputs(&a, &b, service, k, true), 0);
        }
    }

    // The wrong rules fail, for the right reason.
    #[test]
    fn segmented_source_breaks_when_every_empty_poll_is_a_proof() {
        // Four messages at once, segments of two, service 10: the boundary
        // poll returns 0 with two messages still waiting.
        let arrivals = [0, 0, 0, 0];
        let service = [10, 10, 10, 10];
        assert_eq!(simulate_segmented(&arrivals, &service, 2, 10, true), 0);
        assert!(simulate_segmented(&arrivals, &service, 2, 10, false) > 0);
    }

    #[test]
    fn two_inputs_break_when_idle_follows_an_empty_a_poll_alone() {
        // Two B messages arrive after B's first check. The second waits
        // through a whole B cycle during which A-only passes were empty; the
        // wrong rule calls those idle and reads the wait as zero.
        let a: [u64; 0] = [];
        let b = [3u64, 3];
        assert_eq!(simulate_two_inputs(&a, &b, 5, 4, true), 0);
        assert!(simulate_two_inputs(&a, &b, 5, 4, false) > 0);
    }
}
