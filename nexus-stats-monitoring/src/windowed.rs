// Windowed extrema: Kathleen Nichols' 3-sample algorithm, a literal port of
// the Linux kernel's `lib/win_minmax.c` (used by TCP BBR).
//
// Three samples are kept: the best, 2nd best and 3rd best in the window,
// with the invariant that the n-th best is at least as recent as the
// (n-1)-th. A new extremum forgets everything earlier. By age, a choice is
// only replaced while no distinct choice has been found yet: the 2nd after a
// quarter of the window, the 3rd after half. When the best ages out, the
// 2nd is promoted (twice if needed; the 3rd is checked on entry).
//
// The algorithm is approximate by design: constant space and time, and the
// kernel's own header says it "almost always" matches an exact window. Every
// error is in one direction: the reported maximum is never above the true
// windowed maximum, the minimum never below, because the reported value is
// always a real sample from inside the window.
//
// State: 3 × (timestamp, value) + u64 window + u64 count + u64 last tick.

use nexus_stats_core::Sample;

/// Internal sample stored per sub-window.
#[derive(Debug, Clone, Copy)]
struct Stamped<T: Copy> {
    timestamp: u64,
    value: T,
}

impl<T: Sample> Stamped<T> {
    /// Placeholder for an empty window; never read before the first value.
    const EMPTY: Self = Self {
        timestamp: 0,
        value: T::ZERO,
    };
}

/// Streaming windowed maximum over a sliding time window (Nichols' algorithm).
///
/// Tracks the maximum value within a `u64` timestamp window using only
/// 3 stored samples. O(1) amortized per update, `no_std` compatible.
/// A NaN is ignored, as [`f64::max`] ignores one; infinity is a value
/// like any other.
///
/// # Use Cases
/// - Max throughput tracking
/// - BBR-style bandwidth estimation
/// - Peak detection within a time window
///
/// # Weighting clock
///
/// Caller's timestamps. Any call rate; the window is measured in ticks, not
/// samples. The accessor reflects the input as of the last `update`: a quiet
/// input keeps returning its last extremum until a later `update` ages it
/// out. A periodic reader that needs the window to expire without new data
/// should feed the current tick with a neutral value or treat the result as
/// stale by its own clock.
///
/// Ticks must be non-decreasing. A sample timestamped before the previous
/// accepted one is ignored: the state and the count stay as they were and
/// `update` returns the current extremum, so a late extreme value is dropped
/// too. Elapsed time is computed with wrapping subtraction, so a counter
/// that wraps is fine as long as the window and any real gap between
/// samples fit in half its range.
#[derive(Debug, Clone)]
pub struct WindowedMax<T: Sample> {
    window: Window<T>,
}

impl<T: Sample> WindowedMax<T> {
    /// Creates a tracker over a window of `window` ticks.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `window` is zero or is 2^63 ticks
    /// or more.
    #[inline]
    pub fn new(window: u64) -> Result<Self, nexus_stats_core::ConfigError> {
        Ok(Self {
            window: Window::new(window)?,
        })
    }

    /// Current windowed maximum, or `None` before the first sample.
    #[inline]
    #[must_use]
    pub fn max(&self) -> Option<T> {
        self.window.best()
    }

    /// The window length in ticks.
    #[inline]
    #[must_use]
    pub fn window(&self) -> u64 {
        self.window.span
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.window.count
    }

    /// Whether at least one sample has been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.window.count > 0
    }

    /// Resets to empty state. The window is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.window.reset();
    }

    /// Feeds a value at `timestamp` and returns the maximum over the
    /// window, or `None` if no value has been taken yet.
    ///
    /// A NaN is ignored, as [`f64::max`] ignores one, and so is a value
    /// timestamped before the last one taken: the window and the count stay
    /// as they were. Infinity is a value like any other.
    #[inline]
    pub fn update(&mut self, timestamp: u64, value: T) -> Option<T> {
        self.window.update(timestamp, value, |a, b| a >= b)
    }
}

/// Streaming windowed minimum over a sliding time window (Nichols' algorithm).
///
/// Tracks the minimum value within a `u64` timestamp window using only
/// 3 stored samples. O(1) amortized per update, `no_std` compatible.
/// A NaN is ignored, as [`f64::min`] ignores one; infinity is a value
/// like any other.
///
/// # Use Cases
/// - Min RTT tracking (BBR)
/// - Minimum price in a window
/// - Best-case latency estimation
/// - Deterministic replay with raw tick counters
///
/// # Weighting clock
///
/// Caller's timestamps. Any call rate; the window is measured in ticks, not
/// samples. The accessor reflects the input as of the last `update`: a quiet
/// input keeps returning its last extremum until a later `update` ages it
/// out. A periodic reader that needs the window to expire without new data
/// should feed the current tick with a neutral value or treat the result as
/// stale by its own clock.
///
/// Ticks must be non-decreasing. A sample timestamped before the previous
/// accepted one is ignored: the state and the count stay as they were and
/// `update` returns the current extremum, so a late extreme value is dropped
/// too. Elapsed time is computed with wrapping subtraction, so a counter
/// that wraps is fine as long as the window and any real gap between
/// samples fit in half its range.
#[derive(Debug, Clone)]
pub struct WindowedMin<T: Sample> {
    window: Window<T>,
}

impl<T: Sample> WindowedMin<T> {
    /// Creates a tracker over a window of `window` ticks.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `window` is zero or is 2^63 ticks
    /// or more.
    #[inline]
    pub fn new(window: u64) -> Result<Self, nexus_stats_core::ConfigError> {
        Ok(Self {
            window: Window::new(window)?,
        })
    }

    /// Current windowed minimum, or `None` before the first sample.
    #[inline]
    #[must_use]
    pub fn min(&self) -> Option<T> {
        self.window.best()
    }

    /// The window length in ticks.
    #[inline]
    #[must_use]
    pub fn window(&self) -> u64 {
        self.window.span
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.window.count
    }

    /// Whether at least one sample has been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.window.count > 0
    }

    /// Resets to empty state. The window is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.window.reset();
    }

    /// Feeds a value at `timestamp` and returns the minimum over the
    /// window, or `None` if no value has been taken yet.
    ///
    /// A NaN is ignored, as [`f64::min`] ignores one, and so is a value
    /// timestamped before the last one taken: the window and the count stay
    /// as they were. Infinity is a value like any other.
    #[inline]
    pub fn update(&mut self, timestamp: u64, value: T) -> Option<T> {
        self.window.update(timestamp, value, |a, b| a <= b)
    }
}

/// The longest window: half the range of the tick counter.
const MAX_WINDOW: u64 = i64::MAX as u64;

/// The three choices and the clock, shared by the maximum and the minimum.
#[derive(Debug, Clone)]
struct Window<T: Sample> {
    span: u64,
    samples: [Stamped<T>; 3],
    count: u64,
    /// Timestamp of the newest value taken.
    last: u64,
}

impl<T: Sample> Window<T> {
    #[inline]
    fn new(span: u64) -> Result<Self, nexus_stats_core::ConfigError> {
        if span == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "window must be positive",
            ));
        }
        // An age of 2^63 ticks or more reads as a late timestamp.
        if span > MAX_WINDOW {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "window must be below 2^63 ticks",
            ));
        }
        Ok(Self {
            span,
            samples: [Stamped::EMPTY; 3],
            count: 0,
            last: 0,
        })
    }

    #[inline]
    fn reset(&mut self) {
        self.samples = [Stamped::EMPTY; 3];
        self.count = 0;
    }

    /// The best choice, or `None` before the first value.
    #[inline]
    fn best(&self) -> Option<T> {
        if self.count == 0 {
            return None;
        }
        Some(self.samples[0].value)
    }

    /// Whether a value is skipped: a NaN, or one timestamped before the
    /// last value taken.
    #[inline]
    fn skips(&self, timestamp: u64, value: T) -> bool {
        value.is_nan() || (self.count > 0 && is_late(timestamp, self.last))
    }

    /// Takes a value and returns the best choice. `better(a, b)` says
    /// whether `a` beats or ties `b`.
    #[inline]
    fn update(&mut self, timestamp: u64, value: T, better: impl Fn(T, T) -> bool) -> Option<T> {
        if self.skips(timestamp, value) {
            return self.best();
        }
        self.last = timestamp;
        self.count += 1;
        // The first value is the best, whatever it is.
        if self.count == 1 {
            self.samples = [Stamped { timestamp, value }; 3];
            return Some(value);
        }
        Some(running(
            &mut self.samples,
            self.span,
            timestamp,
            value,
            better,
        ))
    }
}

/// Whether `timestamp` is before `last` on a wrapping tick counter: the
/// signed difference, so a forward step across the wrap is not late.
#[inline]
fn is_late(timestamp: u64, last: u64) -> bool {
    (timestamp.wrapping_sub(last) as i64) < 0
}

/// `minmax_running_max` / `minmax_running_min` from `lib/win_minmax.c`.
///
/// `better(a, b)` is `a >= b` for a maximum and `a <= b` for a minimum.
/// Returns the current extremum, `s[0].value`. Timestamps must be
/// non-decreasing (the callers drop late samples); subtraction wraps, as in
/// the kernel's `u32` arithmetic.
#[inline]
fn running<T: Copy>(
    s: &mut [Stamped<T>; 3],
    win: u64,
    timestamp: u64,
    value: T,
    better: impl Fn(T, T) -> bool,
) -> T {
    let val = Stamped { timestamp, value };

    // Found a new extremum, or nothing left in the window: forget earlier
    // samples (`minmax_reset`).
    if better(value, s[0].value) || timestamp.wrapping_sub(s[2].timestamp) > win {
        *s = [val; 3];
        return value;
    }

    if better(value, s[1].value) {
        s[2] = val;
        s[1] = val;
    } else if better(value, s[2].value) {
        s[2] = val;
    }

    subwin_update(s, win, val)
}

/// `minmax_subwin_update` from `lib/win_minmax.c`: as time advances, update
/// the 1st, 2nd and 3rd choices.
#[inline]
fn subwin_update<T: Copy>(s: &mut [Stamped<T>; 3], win: u64, val: Stamped<T>) -> T {
    let dt = val.timestamp.wrapping_sub(s[0].timestamp);

    if dt > win {
        // Passed the entire window without a new extremum: the 2nd choice
        // becomes the best, the 3rd becomes 2nd, the new sample becomes 3rd.
        // The 2nd choice may also be outside the window (only the 3rd was
        // checked on entry), so this may have to run twice.
        s[0] = s[1];
        s[1] = s[2];
        s[2] = val;
        if val.timestamp.wrapping_sub(s[0].timestamp) > win {
            s[0] = s[1];
            s[1] = s[2];
            s[2] = val;
        }
    } else if s[1].timestamp == s[0].timestamp && dt > win / 4 {
        // A quarter of the window passed without a distinct 2nd choice:
        // take one from the 2nd quarter.
        s[2] = val;
        s[1] = val;
    } else if s[2].timestamp == s[1].timestamp && dt > win / 2 {
        // Half the window passed without a distinct 3rd choice: take one
        // from the last half.
        s[2] = val;
    }

    s[0].value
}

#[cfg(test)]
mod raw_tests {
    use super::*;

    #[test]
    fn raw_max_basic() {
        let mut wm = WindowedMax::<f64>::new(100).unwrap();
        assert_eq!(wm.update(0, 10.0).unwrap(), 10.0);
        assert_eq!(wm.update(50, 20.0).unwrap(), 20.0);
    }

    #[test]
    fn raw_max_expires() {
        let mut wm = WindowedMax::<f64>::new(10).unwrap();
        let _ = wm.update(0, 100.0).unwrap();
        assert_eq!(
            wm.update(5, 50.0).unwrap(),
            100.0,
            "100 still inside the window"
        );
        // t = 11: the 100 at t = 0 has aged out; 60 beats the surviving 50.
        assert_eq!(wm.update(11, 60.0).unwrap(), 60.0);
    }

    #[test]
    fn raw_min_basic() {
        let mut wm = WindowedMin::<i64>::new(100).unwrap();
        assert_eq!(wm.update(0, 100), Some(100));
        assert_eq!(wm.update(1, 50), Some(50));
    }

    #[test]
    fn raw_rejects_zero_window() {
        assert!(WindowedMax::<f64>::new(0).is_err());
    }

    #[test]
    fn a_window_of_half_the_counter_range_is_refused() {
        let longest = i64::MAX as u64;
        assert!(WindowedMax::<i64>::new(longest).is_ok());
        assert!(WindowedMin::<i64>::new(longest).is_ok());
        for window in [longest + 1, u64::MAX] {
            assert!(WindowedMax::<i64>::new(window).is_err());
            assert!(WindowedMin::<f64>::new(window).is_err());
        }
    }

    #[test]
    fn nothing_is_reported_before_the_first_value() {
        let wm = WindowedMax::<f64>::new(100).unwrap();
        assert_eq!(wm.max(), None);
        let wn = WindowedMin::<i64>::new(100).unwrap();
        assert_eq!(wn.min(), None);
    }

    #[test]
    fn a_nan_is_ignored_and_changes_nothing() {
        let mut wm = WindowedMax::<f64>::new(100).unwrap();
        let mut wn = WindowedMin::<f64>::new(100).unwrap();
        // Before any value there is nothing to report.
        assert_eq!(wm.update(0, f64::NAN), None);
        assert_eq!(wn.update(0, f64::NAN), None);
        assert_eq!((wm.count(), wn.count()), (0, 0));

        assert_eq!(wm.update(10, 5.0), Some(5.0));
        assert_eq!(wn.update(10, 5.0), Some(5.0));
        // Later, even at a timestamp far ahead: the window does not move.
        assert_eq!(wm.update(10_000, f64::NAN), Some(5.0));
        assert_eq!(wn.update(10_000, f64::NAN), Some(5.0));
        assert_eq!((wm.count(), wn.count()), (1, 1));
        // So a value at an earlier timestamp than the NaN's is still taken.
        assert_eq!(wm.update(20, 7.0), Some(7.0));
        assert_eq!(wn.update(20, 3.0), Some(3.0));
    }

    #[test]
    fn infinity_is_a_value_like_any_other() {
        let mut wm = WindowedMax::<f64>::new(10).unwrap();
        assert_eq!(wm.update(0, 1.0), Some(1.0));
        assert_eq!(wm.update(1, f64::INFINITY), Some(f64::INFINITY));
        assert_eq!(wm.update(5, 2.0), Some(f64::INFINITY));
        // And it ages out of the window like one.
        assert_eq!(wm.update(12, 3.0), Some(3.0));

        // An infinity is the extreme even as the very first value.
        let mut low = WindowedMax::<f64>::new(10).unwrap();
        assert_eq!(low.update(0, f64::NEG_INFINITY), Some(f64::NEG_INFINITY));
        assert_eq!(low.max(), Some(f64::NEG_INFINITY));
        let mut high = WindowedMin::<f64>::new(10).unwrap();
        assert_eq!(high.update(0, f64::INFINITY), Some(f64::INFINITY));
        assert_eq!(high.min(), Some(f64::INFINITY));
    }

    /// Floats with infinities and NaNs mixed in, against the window kept
    /// in full: a NaN changes nothing, and what is reported is always a
    /// value from inside the window that does not beat the true extreme.
    #[test]
    fn floats_with_nans_and_infinities_stay_inside_the_window() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for win in [1u64, 7, 50, 400] {
            let mut wm = WindowedMax::<f64>::new(win).unwrap();
            let mut wn = WindowedMin::<f64>::new(win).unwrap();
            let mut kept: Vec<(u64, f64)> = Vec::new();
            let mut t = 0u64;
            for _ in 0..20_000 {
                t += next() % 5;
                let draw = next() % 100;
                let v = match draw {
                    0..=7 => f64::NAN,
                    8 => f64::INFINITY,
                    9 => f64::NEG_INFINITY,
                    _ => (next() % 2001) as f64 - 1000.0,
                };
                let before = (wm.max(), wn.min(), wm.count(), wn.count());
                let (got_max, got_min) = (wm.update(t, v), wn.update(t, v));
                if v.is_nan() {
                    assert_eq!((got_max, got_min, wm.count(), wn.count()), before, "t {t}");
                    continue;
                }
                kept.push((t, v));
                kept.retain(|&(ts, _)| t - ts <= win);
                let inside = || kept.iter().map(|&(_, v)| v);
                let exact_max = inside().fold(f64::NEG_INFINITY, f64::max);
                let exact_min = inside().fold(f64::INFINITY, f64::min);
                let (got_max, got_min) = (got_max.unwrap(), got_min.unwrap());
                assert!(
                    got_max <= exact_max && got_min >= exact_min,
                    "win {win} t {t}"
                );
                assert!(inside().any(|v| v == got_max), "win {win} t {t}: {got_max}");
                assert!(inside().any(|v| v == got_min), "win {win} t {t}: {got_min}");
                // The newest value is always in the window.
                assert!(got_max >= v && got_min <= v, "win {win} t {t}");
            }
        }
    }

    // The four-sample counterexample from #758: window 100, samples (t, v).
    // At t = 101 the window covers ages <= 100, so (0, 100) has aged out and the
    // true maximum is 90. The previous port returned 10.
    #[test]
    fn kernel_port_counterexample_max() {
        let mut wm = WindowedMax::<i64>::new(100).unwrap();
        for (t, v) in [(0u64, 100i64), (40, 90), (80, 10), (101, 5)] {
            let _ = wm.update(t, v);
        }
        assert_eq!(wm.max(), Some(90));

        let mut wf = WindowedMax::<f64>::new(100).unwrap();
        for (t, v) in [(0u64, 100.0f64), (40, 90.0), (80, 10.0), (101, 5.0)] {
            let _ = wf.update(t, v).unwrap();
        }
        assert_eq!(wf.max(), Some(90.0));
    }

    // The mirror case, which is the CoDel sojourn input: true minimum 20, the
    // previous port returned 100.
    #[test]
    fn kernel_port_counterexample_min() {
        let mut wm = WindowedMin::<i64>::new(100).unwrap();
        for (t, v) in [(0u64, 10i64), (40, 20), (80, 100), (101, 105)] {
            let _ = wm.update(t, v);
        }
        assert_eq!(wm.min(), Some(20));

        let mut wf = WindowedMin::<f64>::new(100).unwrap();
        for (t, v) in [(0u64, 10.0f64), (40, 20.0), (80, 100.0), (101, 105.0)] {
            let _ = wf.update(t, v).unwrap();
        }
        assert_eq!(wf.min(), Some(20.0));
    }

    /// Exact windowed extremum over all samples with age <= window, inclusive,
    /// matching the kernel's `t - s.t > win` expiry test.
    struct ExactWindow {
        win: u64,
        samples: std::collections::VecDeque<(u64, i64)>,
    }

    impl ExactWindow {
        fn push(&mut self, t: u64, v: i64) {
            self.samples.push_back((t, v));
            while let Some(&(ts, _)) = self.samples.front() {
                if t.wrapping_sub(ts) > self.win {
                    self.samples.pop_front();
                } else {
                    break;
                }
            }
        }
        fn max(&self) -> i64 {
            self.samples.iter().map(|&(_, v)| v).max().unwrap()
        }
        fn min(&self) -> i64 {
            self.samples.iter().map(|&(_, v)| v).min().unwrap()
        }
    }

    /// xorshift64*: deterministic, no dependency, good enough for a stream shape.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Runs `n` updates of a stream against the exact window. Asserts the error
    /// direction on every update (the port is a real in-window sample, so the
    /// reported max is never above the truth and the min never below) and
    /// returns the fraction of updates where the port disagreed with the truth.
    fn mismatch_rate(win: u64, n: usize, mut value: impl FnMut(&mut Rng) -> i64) -> (f64, f64) {
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        let mut pmax = WindowedMax::<i64>::new(win).unwrap();
        let mut pmin = WindowedMin::<i64>::new(win).unwrap();
        let mut exact = ExactWindow {
            win,
            samples: std::collections::VecDeque::new(),
        };
        let (mut t, mut bad_max, mut bad_min) = (0u64, 0usize, 0usize);
        for _ in 0..n {
            t += 1 + rng.below(4); // 1..=4 ticks apart
            let v = value(&mut rng);
            exact.push(t, v);
            let got_max = pmax.update(t, v).unwrap();
            let got_min = pmin.update(t, v).unwrap();
            assert!(
                got_max <= exact.max(),
                "max over-reported at t={t}: {got_max} > {}",
                exact.max()
            );
            assert!(
                got_min >= exact.min(),
                "min under-reported at t={t}: {got_min} < {}",
                exact.min()
            );
            bad_max += usize::from(got_max != exact.max());
            bad_min += usize::from(got_min != exact.min());
        }
        (bad_max as f64 / n as f64, bad_min as f64 / n as f64)
    }

    // Stationary inputs at ~40 samples per window: the kernel algorithm is wrong
    // on 1% to 2% of updates (the previous port: 12% to 14%). Assert under 3%.
    #[test]
    fn kernel_port_tracks_exact_window_on_stationary_input() {
        let (bad_max, bad_min) = mismatch_rate(100, 200_000, |r| r.below(1_000) as i64);
        assert!(bad_max < 0.03, "uniform max mismatch rate {bad_max}");
        assert!(bad_min < 0.03, "uniform min mismatch rate {bad_min}");

        // Latency-like: steady with rare spikes.
        let (bad_max, bad_min) = mismatch_rate(100, 200_000, |r| {
            let base = 100 + r.below(5) as i64;
            if r.below(100) == 0 {
                base + 50 + r.below(500) as i64
            } else {
                base
            }
        });
        assert!(bad_max < 0.03, "latency-like max mismatch rate {bad_max}");
        assert!(bad_min < 0.03, "latency-like min mismatch rate {bad_min}");
    }

    // Trending input is the algorithm's documented weak case. No rate bound is
    // asserted; the direction assertions inside `mismatch_rate` still apply.
    #[test]
    fn kernel_port_error_direction_holds_on_random_walk() {
        let mut level = 0i64;
        let _ = mismatch_rate(100, 200_000, |r| {
            level += r.below(21) as i64 - 10;
            level
        });
    }
}

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(400))]

        /// The reported extremum is always a real sample inside the window, so
        /// the max is never above the exact windowed max and the min never
        /// below the exact windowed min, for any non-decreasing timestamps.
        #[test]
        fn extremum_is_never_on_the_wrong_side_of_the_truth(
            win in 1u64..200,
            steps in proptest::collection::vec((0u64..50, -1_000i64..1_000), 1..300),
        ) {
            let mut pmax = WindowedMax::<i64>::new(win).unwrap();
            let mut pmin = WindowedMin::<i64>::new(win).unwrap();
            let mut hist: Vec<(u64, i64)> = Vec::new();
            let mut t = 0u64;
            for (gap, v) in steps {
                t += gap;
                hist.push((t, v));
                let exact_max = hist.iter().filter(|&&(ts, _)| t - ts <= win).map(|&(_, v)| v).max().unwrap();
                let exact_min = hist.iter().filter(|&&(ts, _)| t - ts <= win).map(|&(_, v)| v).min().unwrap();
                prop_assert!(pmax.update(t, v).unwrap() <= exact_max);
                prop_assert!(pmin.update(t, v).unwrap() >= exact_min);
            }
        }
    }
}

#[cfg(test)]
mod late_sample_tests {
    use super::*;
    use proptest::prelude::*;

    // A late sample used to read as a gap longer than the window and reset
    // the tracker to itself: max 1 here, with 50 still in the window.
    #[test]
    fn late_sample_does_not_reset_the_window() {
        let mut wm = WindowedMax::<i64>::new(100).unwrap();
        let _ = wm.update(1000, 50);
        let _ = wm.update(1030, 40);
        assert_eq!(wm.update(1020, 1), Some(50));
        assert_eq!(wm.max(), Some(50));
        assert_eq!(wm.count(), 2);

        let mut wn = WindowedMin::<i64>::new(100).unwrap();
        let _ = wn.update(1000, 5);
        let _ = wn.update(1030, 6);
        assert_eq!(wn.update(1020, 99), Some(5));
        assert_eq!(wn.min(), Some(5));
        assert_eq!(wn.count(), 2);
    }

    // The documented cost of ignoring: a late extreme value is dropped.
    #[test]
    fn late_extreme_value_is_dropped() {
        let mut wm = WindowedMax::<f64>::new(100).unwrap();
        let _ = wm.update(1000, 10.0).unwrap();
        let _ = wm.update(1030, 20.0).unwrap();
        assert_eq!(wm.update(1020, 99.0).unwrap(), 20.0);

        let mut wn = WindowedMin::<f64>::new(100).unwrap();
        let _ = wn.update(1000, 10.0).unwrap();
        let _ = wn.update(1030, 5.0).unwrap();
        assert_eq!(wn.update(1020, -99.0).unwrap(), 5.0);
        assert_eq!(wn.count(), 2);
    }

    #[test]
    fn equal_timestamp_is_accepted() {
        let mut wm = WindowedMax::<i64>::new(100).unwrap();
        let _ = wm.update(1000, 10);
        assert_eq!(wm.update(1000, 30), Some(30));
        assert_eq!(wm.count(), 2);
    }

    #[test]
    fn lateness_follows_the_wrapping_counter() {
        let mut wm = WindowedMax::<i64>::new(100).unwrap();
        let _ = wm.update(u64::MAX - 5, 10);
        assert_eq!(wm.update(3, 5), Some(10)); // forward across the wrap: 10 still in window
        assert_eq!(wm.update(u64::MAX - 1, 99), Some(10)); // late across the wrap: ignored
        assert_eq!(wm.count(), 2);

        let mut wn = WindowedMin::<i64>::new(100).unwrap();
        let _ = wn.update(u64::MAX - 5, 10);
        assert_eq!(wn.update(3, 20), Some(10));
        assert_eq!(wn.update(u64::MAX - 1, -99), Some(10));
        assert_eq!(wn.count(), 2);
    }

    #[test]
    fn reset_forgets_the_last_timestamp() {
        // 5 is before 1000: late without the reset, taken after it.
        let mut wm = WindowedMax::<i64>::new(100).unwrap();
        assert_eq!(wm.update(1000, 7), Some(7));
        assert_eq!(wm.update(5, 9), Some(7));
        wm.reset();
        assert_eq!(wm.update(5, 3), Some(3));
        assert_eq!(wm.count(), 1);

        let mut wn = WindowedMin::<i64>::new(100).unwrap();
        assert_eq!(wn.update(1000, 7), Some(7));
        assert_eq!(wn.update(5, 1), Some(7));
        wn.reset();
        assert_eq!(wn.update(5, 9), Some(9));
        assert_eq!(wn.count(), 1);
    }

    #[test]
    fn the_integer_limits_are_values_like_any_other() {
        let mut wm = WindowedMax::<i64>::new(10).unwrap();
        assert_eq!(wm.update(0, i64::MIN), Some(i64::MIN));
        assert_eq!(wm.update(1, i64::MAX), Some(i64::MAX));
        assert_eq!(wm.update(12, i64::MIN), Some(i64::MIN));

        let mut wn = WindowedMin::<i64>::new(10).unwrap();
        assert_eq!(wn.update(0, i64::MAX), Some(i64::MAX));
        assert_eq!(wn.update(1, i64::MIN), Some(i64::MIN));
        assert_eq!(wn.update(12, i64::MAX), Some(i64::MAX));
    }

    #[test]
    fn equal_timestamps_are_taken_by_the_minimum_too() {
        let mut wn = WindowedMin::<i64>::new(100).unwrap();
        assert_eq!(wn.update(10, 5), Some(5));
        assert_eq!(wn.update(10, 3), Some(3));
        assert_eq!(wn.count(), 2);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(400))]

        /// With some timestamps stepping backwards, the trackers behave as if
        /// only the in-order samples had been fed: the error direction holds
        /// against the exact window over those samples, and only they count.
        #[test]
        fn out_of_order_input_acts_like_the_in_order_samples(
            win in 1u64..200,
            steps in proptest::collection::vec((-60i64..50, -1_000i64..1_000), 1..300),
        ) {
            let mut pmax = WindowedMax::<i64>::new(win).unwrap();
            let mut pmin = WindowedMin::<i64>::new(win).unwrap();
            let mut ref_max = WindowedMax::<i64>::new(win).unwrap();
            let mut ref_min = WindowedMin::<i64>::new(win).unwrap();
            let mut kept: Vec<(u64, i64)> = Vec::new();
            let mut t = 1_000_000u64; // far from the wrap: plain `>=` is the reference
            for (step, v) in steps {
                t = t.wrapping_add_signed(step);
                let got_max = pmax.update(t, v).unwrap();
                let got_min = pmin.update(t, v).unwrap();
                let last = kept.last().map(|&(ts, _)| ts);
                if last.is_none_or(|l| t >= l) {
                    kept.push((t, v));
                    let _ = ref_max.update(t, v);
                    let _ = ref_min.update(t, v);
                }
                let now = kept.last().unwrap().0;
                let exact_max = kept.iter().filter(|&&(ts, _)| now - ts <= win).map(|&(_, v)| v).max().unwrap();
                let exact_min = kept.iter().filter(|&&(ts, _)| now - ts <= win).map(|&(_, v)| v).min().unwrap();
                prop_assert_eq!(got_max, ref_max.max().unwrap());
                prop_assert_eq!(got_min, ref_min.min().unwrap());
                prop_assert!(got_max <= exact_max);
                prop_assert!(got_min >= exact_min);
                prop_assert_eq!(pmax.count(), kept.len() as u64);
                prop_assert_eq!(pmin.count(), kept.len() as u64);
            }
        }
    }
}
