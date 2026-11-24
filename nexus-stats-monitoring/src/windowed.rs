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

use core::time::Duration;

use nexus_stats_core::parts::LastTime;
use nexus_stats_core::{Sample, Timestamp};

/// Streaming windowed maximum over a sliding time window (Nichols' algorithm).
///
/// Tracks the maximum value within a window of time using only 3 stored
/// samples. O(1) per update, `no_std` compatible. A NaN is ignored, as
/// [`f64::max`] ignores one; infinity is a value like any other.
///
/// The clock `C` is `i128` nanoseconds or an `Instant`, and the window is a
/// [`Duration`].
///
/// # Use Cases
/// - Max throughput tracking
/// - BBR-style bandwidth estimation
/// - Peak detection within a time window
///
/// # Time
///
/// The reading is as of the last `update`. A quiet input keeps returning
/// its last extremum until a later `update` ages it out. A reader that
/// needs the window to expire without new data should treat the result as
/// stale by its own clock.
///
/// Time must not go back. `update` ignores a sample timed before the last
/// one taken, so a late extreme value is dropped too. One time far ahead
/// of the real clock therefore makes every later sample late until
/// [`reset`](Self::reset). `checked_update` reports a late sample as an
/// error, which is how a caller finds out.
#[derive(Debug, Clone)]
pub struct WindowedMax<T: Sample, C: Timestamp> {
    window: Window<T, C>,
}

impl<T: Sample, C: Timestamp> WindowedMax<T, C> {
    /// Creates a windowed maximum tracker over `window` of time.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `window` is zero.
    #[inline]
    pub fn new(window: Duration) -> Result<Self, nexus_stats_core::ConfigError> {
        Ok(Self {
            window: Window::new(window)?,
        })
    }

    /// Current maximum in the window, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn max(&self) -> Option<T> {
        self.window.best()
    }

    /// The window length.
    #[inline]
    #[must_use]
    pub fn window(&self) -> Duration {
        self.window.span
    }

    /// Number of samples taken.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.window.count
    }

    /// Whether at least one sample has been taken.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.window.count > 0
    }

    /// Resets to empty. The window length is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.window.reset();
    }

    /// Feeds a value at `time` and returns the maximum over the window, or
    /// `None` if no value has been taken yet.
    ///
    /// A NaN is ignored, as [`f64::max`] ignores one, and so is a value timed
    /// before the last one taken. Infinity is a value like any other.
    #[inline]
    pub fn update(&mut self, time: C, value: T) -> Option<T> {
        self.window.update(time, value, |a, b| a >= b)
    }

    /// Checked update. Feeds `value`, or returns an error and leaves the
    /// tracker unchanged if `value` is NaN or `time` is before the last
    /// one taken.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `value` is NaN.
    /// - [`DataError::NonMonotonicTime`](nexus_stats_core::DataError::NonMonotonicTime)
    ///   if `time` is before the last one taken.
    #[inline]
    pub fn checked_update(
        &mut self,
        time: C,
        value: T,
    ) -> Result<Option<T>, nexus_stats_core::DataError> {
        self.window.check(time, value)?;
        Ok(self.update(time, value))
    }
}

/// Streaming windowed minimum over a sliding time window (Nichols' algorithm).
///
/// Tracks the minimum value within a window of time using only 3 stored
/// samples. O(1) per update, `no_std` compatible. A NaN is ignored, as
/// [`f64::min`] ignores one; infinity is a value like any other.
///
/// The clock `C` is `i128` nanoseconds or an `Instant`, and the window is a
/// [`Duration`].
///
/// # Use Cases
/// - Min RTT tracking (BBR)
/// - Minimum price in a window
/// - Best-case latency estimation
///
/// # Time
///
/// The reading is as of the last `update`. A quiet input keeps returning
/// its last extremum until a later `update` ages it out. A reader that
/// needs the window to expire without new data should treat the result as
/// stale by its own clock.
///
/// Time must not go back. `update` ignores a sample timed before the last
/// one taken, so a late extreme value is dropped too. One time far ahead
/// of the real clock therefore makes every later sample late until
/// [`reset`](Self::reset). `checked_update` reports a late sample as an
/// error, which is how a caller finds out.
#[derive(Debug, Clone)]
pub struct WindowedMin<T: Sample, C: Timestamp> {
    window: Window<T, C>,
}

impl<T: Sample, C: Timestamp> WindowedMin<T, C> {
    /// Creates a windowed minimum tracker over `window` of time.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `window` is zero.
    #[inline]
    pub fn new(window: Duration) -> Result<Self, nexus_stats_core::ConfigError> {
        Ok(Self {
            window: Window::new(window)?,
        })
    }

    /// Current minimum in the window, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn min(&self) -> Option<T> {
        self.window.best()
    }

    /// The window length.
    #[inline]
    #[must_use]
    pub fn window(&self) -> Duration {
        self.window.span
    }

    /// Number of samples taken.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.window.count
    }

    /// Whether at least one sample has been taken.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.window.count > 0
    }

    /// Resets to empty. The window length is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.window.reset();
    }

    /// Feeds a value at `time` and returns the minimum over the window, or
    /// `None` if no value has been taken yet.
    ///
    /// A NaN is ignored, as [`f64::min`] ignores one, and so is a value timed
    /// before the last one taken. Infinity is a value like any other.
    #[inline]
    pub fn update(&mut self, time: C, value: T) -> Option<T> {
        self.window.update(time, value, |a, b| a <= b)
    }

    /// Checked update. Feeds `value`, or returns an error and leaves the
    /// tracker unchanged if `value` is NaN or `time` is before the last
    /// one taken.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `value` is NaN.
    /// - [`DataError::NonMonotonicTime`](nexus_stats_core::DataError::NonMonotonicTime)
    ///   if `time` is before the last one taken.
    #[inline]
    pub fn checked_update(
        &mut self,
        time: C,
        value: T,
    ) -> Result<Option<T>, nexus_stats_core::DataError> {
        self.window.check(time, value)?;
        Ok(self.update(time, value))
    }
}

/// The state the maximum and the minimum share.
#[derive(Debug, Clone)]
struct Window<T: Sample, C: Timestamp> {
    span: Duration,
    /// `None` until the first value.
    choices: Option<Choices<T, C>>,
    count: u64,
    last: LastTime<C>,
}

impl<T: Sample, C: Timestamp> Window<T, C> {
    #[inline]
    fn new(span: Duration) -> Result<Self, nexus_stats_core::ConfigError> {
        if span.is_zero() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "window must be positive",
            ));
        }
        Ok(Self {
            span,
            choices: None,
            count: 0,
            last: LastTime::new(),
        })
    }

    #[inline]
    fn reset(&mut self) {
        self.choices = None;
        self.count = 0;
        self.last.reset();
    }

    /// The best choice, or `None` before the first value.
    #[inline]
    fn best(&self) -> Option<T> {
        Some(self.choices.as_ref()?.best())
    }

    /// Why a value would be skipped, if it would be.
    #[inline]
    fn check(&self, time: C, value: T) -> Result<(), nexus_stats_core::DataError> {
        if value.is_nan() {
            return Err(nexus_stats_core::DataError::NotANumber);
        }
        self.last.check(time)
    }

    /// Takes a value and returns the best choice. `better(a, b)` says
    /// whether `a` beats or ties `b`. A NaN and a late value are skipped.
    #[inline]
    fn update(&mut self, time: C, value: T, better: impl Fn(T, T) -> bool) -> Option<T> {
        if value.is_nan() || self.last.would_go_back(time) {
            return self.best();
        }
        self.last.set(time);
        self.count += 1;
        let sample = Stamped { time, value };
        let Some(choices) = &mut self.choices else {
            // The first value is the best, whatever it is.
            self.choices = Some(Choices::all(sample));
            return Some(value);
        };
        Some(choices.take(sample, self.span, better))
    }
}

/// A value and the time it was taken.
#[derive(Debug, Clone, Copy)]
struct Stamped<T, C> {
    time: C,
    value: T,
}

impl<T: Copy, C: Timestamp> Stamped<T, C> {
    /// How long before `now` this was taken.
    #[inline]
    fn age_at(&self, now: C) -> Duration {
        now.since(self.time)
    }
}

/// The best, 2nd best and 3rd best samples in the window, each at least
/// as recent as the one before it. The functions are named for the ones
/// they port from `lib/win_minmax.c`.
#[derive(Debug, Clone, Copy)]
struct Choices<T, C>([Stamped<T, C>; 3]);

impl<T: Copy, C: Timestamp> Choices<T, C> {
    /// Every choice is `sample` (`minmax_reset`).
    #[inline]
    fn all(sample: Stamped<T, C>) -> Self {
        Self([sample; 3])
    }

    #[inline]
    fn best(&self) -> T {
        self.0[0].value
    }

    /// `minmax_running_max` / `minmax_running_min`. Takes a sample and
    /// returns the best choice. `better(a, b)` is `a >= b` for a maximum
    /// and `a <= b` for a minimum. Times must not go back (the caller drops
    /// late samples), so no age is negative.
    #[inline]
    fn take(&mut self, sample: Stamped<T, C>, span: Duration, better: impl Fn(T, T) -> bool) -> T {
        let [first, second, third] = &mut self.0;
        // A new extremum, or nothing left in the window: forget the rest.
        if better(sample.value, first.value) || third.age_at(sample.time) > span {
            *self = Self::all(sample);
            return sample.value;
        }
        if better(sample.value, second.value) {
            *third = sample;
            *second = sample;
        } else if better(sample.value, third.value) {
            *third = sample;
        }
        self.age(sample, span);
        self.best()
    }

    /// `minmax_subwin_update`: as time advances, replaces the choices that
    /// have aged.
    #[inline]
    fn age(&mut self, sample: Stamped<T, C>, span: Duration) {
        let [first, second, third] = self.0;
        let age = first.age_at(sample.time);

        if age > span {
            // The best aged out. The 2nd may have too (only the 3rd was
            // checked on entry), so this may have to run twice.
            self.promote(sample);
            if self.0[0].age_at(sample.time) > span {
                self.promote(sample);
            }
        } else if second.time == first.time && age > span / 4 {
            // A quarter of the window passed without a distinct 2nd
            // choice: take one from the 2nd quarter.
            self.0[1] = sample;
            self.0[2] = sample;
        } else if third.time == second.time && age > span / 2 {
            // Half the window passed without a distinct 3rd choice: take
            // one from the last half.
            self.0[2] = sample;
        }
    }

    /// The 2nd becomes the best, the 3rd the 2nd, and `sample` the 3rd.
    #[inline]
    fn promote(&mut self, sample: Stamped<T, C>) {
        self.0 = [self.0[1], self.0[2], sample];
    }
}

/// A window of `n` nanoseconds.
#[cfg(test)]
fn ns(n: u64) -> Duration {
    Duration::from_nanos(n)
}

#[cfg(test)]
mod raw_tests {
    use super::*;

    #[test]
    fn raw_max_basic() {
        let mut wm = WindowedMax::<f64, i128>::new(ns(100)).unwrap();
        assert_eq!(wm.update(0, 10.0).unwrap(), 10.0);
        assert_eq!(wm.update(50, 20.0).unwrap(), 20.0);
    }

    #[test]
    fn raw_max_expires() {
        let mut wm = WindowedMax::<f64, i128>::new(ns(10)).unwrap();
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
        let mut wm = WindowedMin::<i64, i128>::new(ns(100)).unwrap();
        assert_eq!(wm.update(0, 100), Some(100));
        assert_eq!(wm.update(1, 50), Some(50));
    }

    #[test]
    fn raw_rejects_zero_window() {
        assert!(WindowedMax::<f64, i128>::new(ns(0)).is_err());
    }

    #[test]
    fn any_window_and_any_forward_jump_are_taken() {
        let mut wm = WindowedMax::<i64, i128>::new(Duration::MAX).unwrap();
        assert_eq!(wm.update(i128::MIN, 5), Some(5));
        assert_eq!(wm.update(i128::MAX, 3), Some(5));

        // A jump of any size is only a long gap.
        let mut wn = WindowedMin::<i64, i128>::new(ns(100)).unwrap();
        assert_eq!(wn.update(0, 5), Some(5));
        assert_eq!(wn.update(1 << 63, 9), Some(9));
        assert_eq!(wn.update(i128::MAX, 7), Some(7));
        assert_eq!(wn.count(), 3);
    }

    #[test]
    fn checked_update_reports_what_update_skips() {
        use nexus_stats_core::DataError::{NonMonotonicTime, NotANumber};

        let mut wm = WindowedMax::<f64, i128>::new(ns(100)).unwrap();
        // Nothing is late before the first value, whatever its timestamp.
        assert_eq!(wm.checked_update(1000, f64::NAN), Err(NotANumber));
        assert_eq!(wm.checked_update(1000, 4.0), Ok(Some(4.0)));
        assert_eq!(wm.checked_update(999, 9.0), Err(NonMonotonicTime));
        assert_eq!(wm.checked_update(1001, f64::NAN), Err(NotANumber));
        assert_eq!((wm.max(), wm.count()), (Some(4.0), 1));
        // An equal timestamp and an infinity are both taken.
        assert_eq!(
            wm.checked_update(1000, f64::INFINITY),
            Ok(Some(f64::INFINITY))
        );

        let mut wn = WindowedMin::<i64, i128>::new(ns(100)).unwrap();
        assert_eq!(wn.checked_update(50, 4), Ok(Some(4)));
        assert_eq!(wn.checked_update(49, -9), Err(NonMonotonicTime));
        assert_eq!((wn.min(), wn.count()), (Some(4), 1));
    }

    /// One tick far ahead makes later samples late: `update` drops them in
    /// silence, `checked_update` says so, and `reset` recovers.
    #[test]
    fn a_tick_far_ahead_is_found_through_checked_update() {
        use nexus_stats_core::DataError::NonMonotonicTime;

        let mut wm = WindowedMax::<i64, i128>::new(ns(100)).unwrap();
        wm.update(10, 1);
        wm.update(i128::MAX - 1, 2);
        assert_eq!(wm.update(11, 50), Some(2));
        assert_eq!(wm.checked_update(12, 50), Err(NonMonotonicTime));
        wm.reset();
        assert_eq!(wm.checked_update(12, 50), Ok(Some(50)));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let (mut checked_max, mut plain_max) = (
            WindowedMax::<f64, i128>::new(ns(20)).unwrap(),
            WindowedMax::<f64, i128>::new(ns(20)).unwrap(),
        );
        let (mut checked_min, mut plain_min) = (
            WindowedMin::<i64, i128>::new(ns(20)).unwrap(),
            WindowedMin::<i64, i128>::new(ns(20)).unwrap(),
        );
        let mut t = 0i128;
        for _ in 0..20_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            t += i128::from(state % 7);
            let v = (state >> 8) % 1000;
            assert_eq!(
                checked_max.checked_update(t, v as f64),
                Ok(plain_max.update(t, v as f64))
            );
            assert_eq!(
                checked_min.checked_update(t, v as i64),
                Ok(plain_min.update(t, v as i64))
            );
        }
    }

    #[test]
    fn nothing_is_reported_before_the_first_value() {
        let wm = WindowedMax::<f64, i128>::new(ns(100)).unwrap();
        assert_eq!(wm.max(), None);
        let wn = WindowedMin::<i64, i128>::new(ns(100)).unwrap();
        assert_eq!(wn.min(), None);
    }

    #[test]
    fn a_nan_is_ignored_and_changes_nothing() {
        let mut wm = WindowedMax::<f64, i128>::new(ns(100)).unwrap();
        let mut wn = WindowedMin::<f64, i128>::new(ns(100)).unwrap();
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
        let mut wm = WindowedMax::<f64, i128>::new(ns(10)).unwrap();
        assert_eq!(wm.update(0, 1.0), Some(1.0));
        assert_eq!(wm.update(1, f64::INFINITY), Some(f64::INFINITY));
        assert_eq!(wm.update(5, 2.0), Some(f64::INFINITY));
        // And it ages out of the window like one.
        assert_eq!(wm.update(12, 3.0), Some(3.0));

        // An infinity is the extreme even as the very first value.
        let mut low = WindowedMax::<f64, i128>::new(ns(10)).unwrap();
        assert_eq!(low.update(0, f64::NEG_INFINITY), Some(f64::NEG_INFINITY));
        assert_eq!(low.max(), Some(f64::NEG_INFINITY));
        let mut high = WindowedMin::<f64, i128>::new(ns(10)).unwrap();
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
            let mut wm = WindowedMax::<f64, i128>::new(ns(win)).unwrap();
            let mut wn = WindowedMin::<f64, i128>::new(ns(win)).unwrap();
            let mut kept: Vec<(i128, f64)> = Vec::new();
            let mut t = 0i128;
            for _ in 0..20_000 {
                t += i128::from(next() % 5);
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
                kept.retain(|&(ts, _)| t - ts <= i128::from(win));
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
        let mut wm = WindowedMax::<i64, i128>::new(ns(100)).unwrap();
        for (t, v) in [(0i128, 100i64), (40, 90), (80, 10), (101, 5)] {
            let _ = wm.update(t, v);
        }
        assert_eq!(wm.max(), Some(90));

        let mut wf = WindowedMax::<f64, i128>::new(ns(100)).unwrap();
        for (t, v) in [(0i128, 100.0f64), (40, 90.0), (80, 10.0), (101, 5.0)] {
            let _ = wf.update(t, v).unwrap();
        }
        assert_eq!(wf.max(), Some(90.0));
    }

    // The mirror case, which is the CoDel sojourn input: true minimum 20, the
    // previous port returned 100.
    #[test]
    fn kernel_port_counterexample_min() {
        let mut wm = WindowedMin::<i64, i128>::new(ns(100)).unwrap();
        for (t, v) in [(0i128, 10i64), (40, 20), (80, 100), (101, 105)] {
            let _ = wm.update(t, v);
        }
        assert_eq!(wm.min(), Some(20));

        let mut wf = WindowedMin::<f64, i128>::new(ns(100)).unwrap();
        for (t, v) in [(0i128, 10.0f64), (40, 20.0), (80, 100.0), (101, 105.0)] {
            let _ = wf.update(t, v).unwrap();
        }
        assert_eq!(wf.min(), Some(20.0));
    }

    /// Exact windowed extremum over all samples with age <= window, inclusive,
    /// matching the kernel's `t - s.t > win` expiry test.
    struct ExactWindow {
        win: u64,
        samples: std::collections::VecDeque<(i128, i64)>,
    }

    impl ExactWindow {
        fn push(&mut self, t: i128, v: i64) {
            self.samples.push_back((t, v));
            while let Some(&(ts, _)) = self.samples.front() {
                if t - ts > i128::from(self.win) {
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
        let mut pmax = WindowedMax::<i64, i128>::new(ns(win)).unwrap();
        let mut pmin = WindowedMin::<i64, i128>::new(ns(win)).unwrap();
        let mut exact = ExactWindow {
            win,
            samples: std::collections::VecDeque::new(),
        };
        let (mut t, mut bad_max, mut bad_min) = (0i128, 0usize, 0usize);
        for _ in 0..n {
            t += i128::from(1 + rng.below(4)); // 1..=4 ticks apart
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
            let mut pmax = WindowedMax::<i64, i128>::new(ns(win)).unwrap();
            let mut pmin = WindowedMin::<i64, i128>::new(ns(win)).unwrap();
            let mut hist: Vec<(i128, i64)> = Vec::new();
            let mut t = 0i128;
            for (gap, v) in steps {
                t += i128::from(gap);
                hist.push((t, v));
                let exact_max = hist.iter().filter(|&&(ts, _)| t - ts <= i128::from(win)).map(|&(_, v)| v).max().unwrap();
                let exact_min = hist.iter().filter(|&&(ts, _)| t - ts <= i128::from(win)).map(|&(_, v)| v).min().unwrap();
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
        let mut wm = WindowedMax::<i64, i128>::new(ns(100)).unwrap();
        let _ = wm.update(1000, 50);
        let _ = wm.update(1030, 40);
        assert_eq!(wm.update(1020, 1), Some(50));
        assert_eq!(wm.max(), Some(50));
        assert_eq!(wm.count(), 2);

        let mut wn = WindowedMin::<i64, i128>::new(ns(100)).unwrap();
        let _ = wn.update(1000, 5);
        let _ = wn.update(1030, 6);
        assert_eq!(wn.update(1020, 99), Some(5));
        assert_eq!(wn.min(), Some(5));
        assert_eq!(wn.count(), 2);
    }

    // The documented cost of ignoring: a late extreme value is dropped.
    #[test]
    fn late_extreme_value_is_dropped() {
        let mut wm = WindowedMax::<f64, i128>::new(ns(100)).unwrap();
        let _ = wm.update(1000, 10.0).unwrap();
        let _ = wm.update(1030, 20.0).unwrap();
        assert_eq!(wm.update(1020, 99.0).unwrap(), 20.0);

        let mut wn = WindowedMin::<f64, i128>::new(ns(100)).unwrap();
        let _ = wn.update(1000, 10.0).unwrap();
        let _ = wn.update(1030, 5.0).unwrap();
        assert_eq!(wn.update(1020, -99.0).unwrap(), 5.0);
        assert_eq!(wn.count(), 2);
    }

    #[test]
    fn equal_timestamp_is_accepted() {
        let mut wm = WindowedMax::<i64, i128>::new(ns(100)).unwrap();
        let _ = wm.update(1000, 10);
        assert_eq!(wm.update(1000, 30), Some(30));
        assert_eq!(wm.count(), 2);
    }

    #[test]
    fn reset_forgets_the_last_timestamp() {
        // 5 is before 1000: late without the reset, taken after it.
        let mut wm = WindowedMax::<i64, i128>::new(ns(100)).unwrap();
        assert_eq!(wm.update(1000, 7), Some(7));
        assert_eq!(wm.update(5, 9), Some(7));
        wm.reset();
        assert_eq!(wm.update(5, 3), Some(3));
        assert_eq!(wm.count(), 1);

        let mut wn = WindowedMin::<i64, i128>::new(ns(100)).unwrap();
        assert_eq!(wn.update(1000, 7), Some(7));
        assert_eq!(wn.update(5, 1), Some(7));
        wn.reset();
        assert_eq!(wn.update(5, 9), Some(9));
        assert_eq!(wn.count(), 1);
    }

    #[test]
    fn the_integer_limits_are_values_like_any_other() {
        let mut wm = WindowedMax::<i64, i128>::new(ns(10)).unwrap();
        assert_eq!(wm.update(0, i64::MIN), Some(i64::MIN));
        assert_eq!(wm.update(1, i64::MAX), Some(i64::MAX));
        assert_eq!(wm.update(12, i64::MIN), Some(i64::MIN));

        let mut wn = WindowedMin::<i64, i128>::new(ns(10)).unwrap();
        assert_eq!(wn.update(0, i64::MAX), Some(i64::MAX));
        assert_eq!(wn.update(1, i64::MIN), Some(i64::MIN));
        assert_eq!(wn.update(12, i64::MAX), Some(i64::MAX));
    }

    #[test]
    fn equal_timestamps_are_taken_by_the_minimum_too() {
        let mut wn = WindowedMin::<i64, i128>::new(ns(100)).unwrap();
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
            let mut pmax = WindowedMax::<i64, i128>::new(ns(win)).unwrap();
            let mut pmin = WindowedMin::<i64, i128>::new(ns(win)).unwrap();
            let mut ref_max = WindowedMax::<i64, i128>::new(ns(win)).unwrap();
            let mut ref_min = WindowedMin::<i64, i128>::new(ns(win)).unwrap();
            let mut kept: Vec<(i128, i64)> = Vec::new();
            let mut t = 1_000_000i128;
            for (step, v) in steps {
                t += i128::from(step);
                let got_max = pmax.update(t, v).unwrap();
                let got_min = pmin.update(t, v).unwrap();
                let last = kept.last().map(|&(ts, _)| ts);
                if last.is_none_or(|l| t >= l) {
                    kept.push((t, v));
                    let _ = ref_max.update(t, v);
                    let _ = ref_min.update(t, v);
                }
                let now = kept.last().unwrap().0;
                let exact_max = kept.iter().filter(|&&(ts, _)| now - ts <= i128::from(win)).map(|&(_, v)| v).max().unwrap();
                let exact_min = kept.iter().filter(|&&(ts, _)| now - ts <= i128::from(win)).map(|&(_, v)| v).min().unwrap();
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
