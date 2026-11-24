use core::time::Duration;

use nexus_stats_core::Timestamp;
use nexus_stats_core::parts::LastTime;

/// Event rate: how many events arrived in a window, and the load averaged
/// over one, five and fifteen minutes.
///
/// Count events with [`update`](Self::update), which reads no clock. On
/// your own cadence, [`take`](Self::take) closes the window: it reports the
/// events and the exact rate since the previous `take`, and folds that
/// rate into three exponentially weighted averages.
///
/// The averages are the UNIX load average applied to an event rate, as in
/// Dropwizard's `Meter`: each window's rate enters with weight
/// `1 - exp(-elapsed / horizon)`, for horizons of 1, 5 and 15 minutes.
/// Those sources tick on a fixed 5 seconds. Here the caller's `take` is
/// the tick, and the weight uses the time that really elapsed, so the
/// averages are right at any cadence, even or not.
///
/// For a session this is the demand on it. Read it beside the saturation
/// monitors and an error count.
///
/// # Weighting clock
///
/// Events are counted, one per `update`. Time enters only at `take`.
///
/// # Examples
///
/// ```
/// use nexus_stats_monitoring::EventRate;
///
/// // Start the first window at time zero, in nanoseconds.
/// let mut rate = EventRate::starting_at(0_i128);
/// rate.update_n(12_500);
/// let window = rate.take(250_000_000); // a quarter of a second later
/// assert_eq!(window.events(), 12_500);
/// assert_eq!(window.rate(), Some(50_000.0)); // events per second
/// // The first window sets each average to its rate.
/// assert_eq!(rate.load().unwrap().one_minute, 50_000.0);
/// ```
#[derive(Debug, Clone)]
pub struct EventRate<T: Timestamp> {
    /// Events since the last `take`.
    pending: u64,
    /// Events since the start, up to the last `take`.
    total: u64,
    start: Option<T>,
    last_take: LastTime<T>,
    load: Option<Load>,
}

/// Event rates, in events per second, exponentially weighted over one,
/// five and fifteen minutes. The short one above the long one means the
/// rate is rising.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Load {
    /// Weighted over one minute.
    pub one_minute: f64,
    /// Weighted over five minutes.
    pub five_minutes: f64,
    /// Weighted over fifteen minutes.
    pub fifteen_minutes: f64,
}

/// One window of an [`EventRate`]: what [`EventRate::take`] returns.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RateSummary {
    events: u64,
    elapsed: Option<Duration>,
    total_events: u64,
    since_start: Option<Duration>,
    load: Option<Load>,
}

impl Load {
    const HORIZONS: [f64; 3] = [60.0, 300.0, 900.0];

    /// Every average at the first window's rate, as Dropwizard starts.
    const fn starting_at(rate: f64) -> Self {
        Self {
            one_minute: rate,
            five_minutes: rate,
            fifteen_minutes: rate,
        }
    }

    /// The averages after a window of `elapsed` seconds at `rate`.
    fn after(self, rate: f64, elapsed: f64) -> Self {
        let [one, five, fifteen] = Self::HORIZONS.map(|horizon| weight(elapsed, horizon));
        Self {
            one_minute: blend(self.one_minute, rate, one),
            five_minutes: blend(self.five_minutes, rate, five),
            fifteen_minutes: blend(self.fifteen_minutes, rate, fifteen),
        }
    }
}

impl RateSummary {
    /// Events in the window.
    #[must_use]
    pub fn events(&self) -> u64 {
        self.events
    }

    /// The length of the window, or `None` for the `take` that started the
    /// clock.
    #[must_use]
    pub fn elapsed(&self) -> Option<Duration> {
        self.elapsed
    }

    /// Events per second over the window, or `None` if the window has no
    /// length.
    #[must_use]
    pub fn rate(&self) -> Option<f64> {
        per_second(self.events, self.elapsed?)
    }

    /// Events since the start.
    #[must_use]
    pub fn total_events(&self) -> u64 {
        self.total_events
    }

    /// Events per second since the start, or `None` if no time has passed.
    #[must_use]
    pub fn mean_rate(&self) -> Option<f64> {
        per_second(self.total_events, self.since_start?)
    }

    /// The load averages after this window, or `None` until a window with
    /// a length has closed.
    #[must_use]
    pub fn load(&self) -> Option<Load> {
        self.load
    }
}

impl<T: Timestamp> EventRate<T> {
    /// Creates a meter whose clock starts at the first `take`. That `take`
    /// has no window to report.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pending: 0,
            total: 0,
            start: None,
            last_take: LastTime::new(),
            load: None,
        }
    }

    /// Creates a meter whose first window starts at `start`, so the first
    /// `take` already has a rate.
    #[must_use]
    pub const fn starting_at(start: T) -> Self {
        Self {
            pending: 0,
            total: 0,
            start: Some(start),
            last_take: LastTime::starting_at(start),
            load: None,
        }
    }

    /// Counts one event. Reads no clock.
    #[inline]
    pub fn update(&mut self) {
        self.pending += 1;
    }

    /// Counts `events` events at once, as after a batch poll.
    #[inline]
    pub fn update_n(&mut self, events: u64) {
        self.pending += events;
    }

    /// Closes the window at `now` and returns it.
    ///
    /// A `now` that is not after the previous `take` closes nothing: the
    /// summary has no rate and the events stay counted for the next
    /// window. See [`checked_take`](Self::checked_take).
    pub fn take(&mut self, now: T) -> RateSummary {
        let Some(elapsed) = self.last_take.elapsed_to(now) else {
            self.start = Some(now);
            self.last_take.set(now);
            return self.summary(self.pending, None, now);
        };
        if elapsed.is_zero() {
            return self.summary(self.pending, Some(elapsed), now);
        }
        let events = self.pending;
        self.pending = 0;
        self.total += events;
        self.last_take.set(now);
        self.load = Some(self.next_load(events, elapsed));
        self.summary(events, Some(elapsed), now)
    }

    /// Checked take. Closes the window at `now`, or returns an error and
    /// leaves the meter unchanged if `now` is before the previous `take`.
    ///
    /// # Errors
    ///
    /// [`DataError::NonMonotonicTime`](nexus_stats_core::DataError::NonMonotonicTime)
    /// if `now` is before the previous `take`.
    pub fn checked_take(&mut self, now: T) -> Result<RateSummary, nexus_stats_core::DataError> {
        self.last_take.check(now)?;
        Ok(self.take(now))
    }

    /// The load averages as of the last window, or `None` until a window
    /// with a length has closed. They change only at a `take`.
    #[must_use]
    pub fn load(&self) -> Option<Load> {
        self.load
    }

    /// Events counted since construction or `reset`, the open window
    /// included.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total + self.pending
    }

    /// Whether the load averages are available.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.load.is_some()
    }

    /// Forgets every count, the averages and the clock.
    pub fn reset(&mut self) {
        *self = Self::new();
    }

    /// The averages after a window of `events` over `elapsed`.
    fn next_load(&self, events: u64, elapsed: Duration) -> Load {
        let seconds = elapsed.as_secs_f64();
        let rate = events as f64 / seconds;
        self.load
            .map_or_else(|| Load::starting_at(rate), |load| load.after(rate, seconds))
    }

    /// The summary of a window, as of `now`.
    fn summary(&self, events: u64, elapsed: Option<Duration>, now: T) -> RateSummary {
        RateSummary {
            events,
            elapsed,
            total_events: self.total,
            since_start: self.start.map(|start| now.since(start)),
            load: self.load,
        }
    }
}

impl<T: Timestamp> Default for EventRate<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// `events` per second over `elapsed`, or `None` over no time.
fn per_second(events: u64, elapsed: Duration) -> Option<f64> {
    if elapsed.is_zero() {
        return None;
    }
    Some(events as f64 / elapsed.as_secs_f64())
}

/// The weight of a window of `elapsed` seconds in an average over
/// `horizon` seconds: `1 - exp(-elapsed / horizon)`.
fn weight(elapsed: f64, horizon: f64) -> f64 {
    1.0 - nexus_stats_core::math::exp(-elapsed / horizon)
}

/// Dropwizard's step: `average + weight * (rate - average)`.
// PERF: unfused, as the source writes it.
#[allow(clippy::suboptimal_flops)]
fn blend(average: f64, rate: f64, weight: f64) -> f64 {
    average + weight * (rate - average)
}

#[cfg(test)]
#[allow(clippy::suboptimal_flops)]
mod tests {
    extern crate std;
    use super::*;
    use nexus_stats_core::DataError::NonMonotonicTime;
    use std::time::Instant;

    const SECOND: i128 = 1_000_000_000;

    /// Dropwizard's `EWMA`, as its source: `tick` every `interval` seconds
    /// with `alpha = 1 - exp(-interval / horizon)`.
    struct Ewma {
        alpha: f64,
        interval: f64,
        rate: f64,
        initialized: bool,
    }

    impl Ewma {
        fn new(horizon: f64, interval: f64) -> Self {
            Self {
                alpha: 1.0 - (-interval / horizon).exp(),
                interval,
                rate: 0.0,
                initialized: false,
            }
        }

        fn tick(&mut self, count: u64) {
            let instant_rate = count as f64 / self.interval;
            if self.initialized {
                self.rate += self.alpha * (instant_rate - self.rate);
            } else {
                self.rate = instant_rate;
                self.initialized = true;
            }
        }
    }

    #[test]
    fn a_window_reports_its_events_and_exact_rate() {
        let mut rate = EventRate::starting_at(0_i128);
        rate.update_n(12_500);
        let window = rate.take(SECOND / 4);
        assert_eq!(
            (window.events(), window.elapsed()),
            (12_500, Some(Duration::from_millis(250)))
        );
        assert_eq!(window.rate(), Some(50_000.0));
        // The next window counts only what came after.
        for _ in 0..30 {
            rate.update();
        }
        let window = rate.take(SECOND / 4 + 3 * SECOND);
        assert_eq!((window.events(), window.rate()), (30, Some(10.0)));
        assert_eq!(window.total_events(), 12_530);
        assert_eq!(rate.count(), 12_530);
    }

    #[test]
    fn matches_dropwizard_on_an_even_five_second_tick() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut reference = [60.0, 300.0, 900.0].map(|horizon| Ewma::new(horizon, 5.0));
        let mut rate = EventRate::starting_at(0_i128);
        for tick in 1..=2_000_i128 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            // Busy and quiet spells.
            let count = if (tick / 200) % 2 == 0 {
                state % 5_000
            } else {
                state % 50
            };
            rate.update_n(count);
            let load = rate.take(tick * 5 * SECOND).load().unwrap();
            for ewma in &mut reference {
                ewma.tick(count);
            }
            let got = [load.one_minute, load.five_minutes, load.fifteen_minutes];
            for (got, want) in got.iter().zip(&reference) {
                assert_eq!(got.to_bits(), want.rate.to_bits(), "tick {tick}");
            }
        }
    }

    /// One long window weighs the same as the even ticks it spans, when
    /// the rate is steady: the weight uses the time that elapsed.
    #[test]
    fn an_uneven_cadence_gives_the_same_averages_at_a_steady_rate() {
        let (mut even, mut uneven) = (
            EventRate::starting_at(0_i128),
            EventRate::starting_at(0_i128),
        );
        even.update_n(100);
        even.take(SECOND);
        uneven.update_n(100);
        uneven.take(SECOND);
        // Then the rate drops to 20 per second for a minute.
        for second in 2..=61 {
            even.update_n(20);
            even.take(second * SECOND);
        }
        uneven.update_n(20 * 60);
        uneven.take(61 * SECOND);
        let (a, b) = (even.load().unwrap(), uneven.load().unwrap());
        for (a, b) in [
            (a.one_minute, b.one_minute),
            (a.five_minutes, b.five_minutes),
            (a.fifteen_minutes, b.fifteen_minutes),
        ] {
            assert!((a - b).abs() < 1e-9 * a, "{a} vs {b}");
        }
        // After one horizon, 1/e of the old rate is left in the short one.
        let want = 20.0 + 80.0 * (-1.0_f64).exp();
        assert!((b.one_minute - want).abs() < 1e-9);
    }

    #[test]
    fn the_short_average_leads_the_long_one() {
        let mut rate = EventRate::starting_at(0_i128);
        rate.update_n(10);
        rate.take(SECOND);
        for second in 2..=120 {
            rate.update_n(1_000);
            rate.take(second * SECOND);
        }
        let load = rate.load().unwrap();
        assert!(load.one_minute > load.five_minutes && load.five_minutes > load.fifteen_minutes);
        assert!(load.one_minute < 1_000.0 && load.fifteen_minutes > 10.0);
    }

    #[test]
    fn without_a_start_the_first_take_only_starts_the_clock() {
        let mut rate = EventRate::new();
        rate.update_n(7);
        let first = rate.take(10 * SECOND);
        assert_eq!(
            (first.events(), first.elapsed(), first.rate()),
            (7, None, None)
        );
        assert_eq!(
            (first.load(), rate.load(), rate.is_primed()),
            (None, None, false)
        );
        // Those events belong to the first real window.
        rate.update_n(3);
        let window = rate.take(12 * SECOND);
        assert_eq!((window.events(), window.rate()), (10, Some(5.0)));
        assert_eq!(window.mean_rate(), Some(5.0));
        assert!(rate.is_primed());
    }

    #[test]
    fn the_mean_rate_is_over_the_whole_run() {
        let mut rate = EventRate::starting_at(0_i128);
        rate.update_n(100);
        rate.take(SECOND);
        rate.update_n(20);
        let window = rate.take(4 * SECOND);
        assert_eq!(
            (window.rate(), window.mean_rate()),
            (Some(20.0 / 3.0), Some(30.0))
        );
    }

    #[test]
    fn an_empty_window_has_a_rate_of_zero() {
        let mut rate = EventRate::starting_at(0_i128);
        let window = rate.take(SECOND);
        assert_eq!((window.events(), window.rate()), (0, Some(0.0)));
        assert_eq!(rate.load().unwrap().one_minute, 0.0);
    }

    #[test]
    fn a_take_at_the_same_time_closes_nothing() {
        let mut rate = EventRate::starting_at(0_i128);
        rate.update_n(50);
        rate.take(SECOND);
        let load = rate.load();
        rate.update_n(9);
        let same = rate.take(SECOND);
        assert_eq!(
            (same.events(), same.elapsed(), same.rate()),
            (9, Some(Duration::ZERO), None)
        );
        assert_eq!(rate.load(), load);
        // The events are still there for the window that does close.
        assert_eq!(rate.take(2 * SECOND).events(), 9);
    }

    #[test]
    fn a_take_before_the_last_one_closes_nothing_and_checked_take_says_so() {
        let mut rate = EventRate::starting_at(5 * SECOND);
        rate.update_n(4);
        rate.take(6 * SECOND);
        rate.update_n(2);
        let before = (rate.load(), rate.count());
        assert_eq!(rate.take(3 * SECOND).rate(), None);
        assert_eq!(rate.checked_take(3 * SECOND), Err(NonMonotonicTime));
        assert_eq!((rate.load(), rate.count()), before);
        // The same time is not going back, and a later one closes it.
        assert!(rate.checked_take(6 * SECOND).is_ok());
        assert_eq!(rate.checked_take(7 * SECOND).unwrap().events(), 2);
    }

    #[test]
    fn checked_take_gives_the_same_result_as_take() {
        let (mut checked, mut plain) = (
            EventRate::starting_at(0_i128),
            EventRate::starting_at(0_i128),
        );
        for (events, now) in [
            (5, SECOND),
            (0, 2 * SECOND),
            (900, 2 * SECOND + 1),
            (3, 90 * SECOND),
        ] {
            checked.update_n(events);
            plain.update_n(events);
            assert_eq!(checked.checked_take(now), Ok(plain.take(now)));
        }
    }

    #[test]
    fn an_instant_and_nanoseconds_agree() {
        let start = Instant::now();
        let (mut on_instant, mut on_nanos) = (
            EventRate::starting_at(start),
            EventRate::starting_at(0_i128),
        );
        for (events, millis) in [(40u64, 500u64), (900, 750), (0, 4_000), (12, 61_000)] {
            on_instant.update_n(events);
            on_nanos.update_n(events);
            let a = on_instant.take(start + Duration::from_millis(millis));
            let b = on_nanos.take(i128::from(millis) * 1_000_000);
            assert_eq!(a, b);
        }
    }

    #[test]
    fn reset_forgets_the_counts_the_averages_and_the_clock() {
        let mut rate = EventRate::starting_at(0_i128);
        rate.update_n(10);
        rate.take(SECOND);
        rate.update();
        rate.reset();
        assert_eq!((rate.count(), rate.load()), (0, None));
        // The clock starts again at the next take, even at an earlier time.
        assert_eq!(rate.checked_take(-SECOND).unwrap().elapsed(), None);
    }
}
