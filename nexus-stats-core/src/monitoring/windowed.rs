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
// State: 3 × (timestamp, value) + u64 window + u64 count.

/// Internal sample stored per sub-window.
#[derive(Debug, Clone, Copy)]
struct Sample<T: Copy> {
    timestamp: u64,
    value: T,
}

/// `minmax_running_max` / `minmax_running_min` from `lib/win_minmax.c`.
///
/// `better(a, b)` is `a >= b` for a maximum and `a <= b` for a minimum.
/// Returns the current extremum, `s[0].value`. Timestamps are expected to be
/// non-decreasing; subtraction wraps, as in the kernel's `u32` arithmetic.
#[inline]
fn running<T: Copy>(
    s: &mut [Sample<T>; 3],
    win: u64,
    timestamp: u64,
    value: T,
    better: impl Fn(T, T) -> bool,
) -> T {
    let val = Sample { timestamp, value };

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
fn subwin_update<T: Copy>(s: &mut [Sample<T>; 3], win: u64, val: Sample<T>) -> T {
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

/// Streaming windowed maximum over a sliding time window (Nichols' algorithm).
///
/// Tracks the maximum value within a `u64` timestamp window using only
/// 3 stored samples. O(1) amortized per update, `no_std` compatible.
///
/// # Use Cases
/// - Max throughput tracking
/// - BBR-style bandwidth estimation
/// - Peak detection within a time window
#[derive(Debug, Clone)]
pub struct WindowedMaxF64 {
    window: u64,
    samples: [Sample<f64>; 3],
    count: u64,
}

impl WindowedMaxF64 {
    /// Creates a new windowed max tracker.
    ///
    /// `window` is in the same units as the timestamps you will pass
    /// to [`update`](Self::update). Must be positive.
    #[inline]
    pub fn new(window: u64) -> Result<Self, crate::ConfigError> {
        if window == 0 {
            return Err(crate::ConfigError::Invalid("window must be positive"));
        }
        let init = Sample {
            timestamp: 0,
            value: f64::MIN,
        };
        Ok(Self {
            window,
            samples: [init; 3],
            count: 0,
        })
    }

    /// Feeds a sample at the given timestamp. Returns current window max.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the value is NaN, or
    /// `DataError::Infinite` if the value is infinite.
    #[inline]
    pub fn update(&mut self, timestamp: u64, value: f64) -> Result<f64, crate::DataError> {
        check_finite!(value);
        self.count += 1;
        Ok(running(
            &mut self.samples,
            self.window,
            timestamp,
            value,
            |a, b| a >= b,
        ))
    }

    /// Convenience for `i64` timestamps (e.g., wire protocol epoch nanos).
    ///
    /// Timestamps must be non-negative. Negative values wrap to large
    /// `u64` values and will produce incorrect window expiration.
    #[inline]
    pub fn update_i64(&mut self, timestamp: i64, value: f64) -> Result<f64, crate::DataError> {
        debug_assert!(timestamp >= 0, "negative timestamp: {timestamp}");
        self.update(timestamp as u64, value)
    }

    /// Current window maximum, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn max(&self) -> Option<f64> {
        if self.count == 0 {
            None
        } else {
            Some(self.samples[0].value)
        }
    }

    /// Window size in raw units.
    #[inline]
    #[must_use]
    pub fn window(&self) -> u64 {
        self.window
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Resets to empty state. Window size is preserved.
    #[inline]
    pub fn reset(&mut self) {
        let init = Sample {
            timestamp: 0,
            value: f64::MIN,
        };
        self.samples = [init; 3];
        self.count = 0;
    }
}

/// Streaming windowed maximum over a sliding time window (Nichols' algorithm).
///
/// Tracks the maximum value within a `u64` timestamp window using only
/// 3 stored samples. O(1) amortized per update, `no_std` compatible.
///
/// # Use Cases
/// - Max throughput tracking
/// - BBR-style bandwidth estimation
/// - Peak detection within a time window
/// - Deterministic replay with raw tick counters
#[derive(Debug, Clone)]
pub struct WindowedMaxI64 {
    window: u64,
    samples: [Sample<i64>; 3],
    count: u64,
}

impl WindowedMaxI64 {
    /// Creates a new windowed max tracker.
    ///
    /// `window` is in the same units as the timestamps you will pass
    /// to [`update`](Self::update). Must be positive.
    #[inline]
    pub fn new(window: u64) -> Result<Self, crate::ConfigError> {
        if window == 0 {
            return Err(crate::ConfigError::Invalid("window must be positive"));
        }
        let init = Sample {
            timestamp: 0,
            value: i64::MIN,
        };
        Ok(Self {
            window,
            samples: [init; 3],
            count: 0,
        })
    }

    /// Feeds a sample at the given timestamp. Returns current window max.
    #[inline]
    #[must_use]
    pub fn update(&mut self, timestamp: u64, value: i64) -> i64 {
        self.count += 1;
        running(&mut self.samples, self.window, timestamp, value, |a, b| {
            a >= b
        })
    }

    /// Convenience for `i64` timestamps (e.g., wire protocol epoch nanos).
    ///
    /// Timestamps must be non-negative. Negative values wrap to large
    /// `u64` values and will produce incorrect window expiration.
    #[inline]
    #[must_use]
    pub fn update_i64(&mut self, timestamp: i64, value: i64) -> i64 {
        debug_assert!(timestamp >= 0, "negative timestamp: {timestamp}");
        self.update(timestamp as u64, value)
    }

    /// Current window maximum, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn max(&self) -> Option<i64> {
        if self.count == 0 {
            None
        } else {
            Some(self.samples[0].value)
        }
    }

    /// Window size in raw units.
    #[inline]
    #[must_use]
    pub fn window(&self) -> u64 {
        self.window
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Resets to empty state. Window size is preserved.
    #[inline]
    pub fn reset(&mut self) {
        let init = Sample {
            timestamp: 0,
            value: i64::MIN,
        };
        self.samples = [init; 3];
        self.count = 0;
    }
}

/// Streaming windowed minimum over a sliding time window (Nichols' algorithm).
///
/// Tracks the minimum value within a `u64` timestamp window using only
/// 3 stored samples. O(1) amortized per update, `no_std` compatible.
///
/// # Use Cases
/// - Min RTT tracking (BBR)
/// - Minimum price in a window
/// - Best-case latency estimation
/// - Deterministic replay with raw tick counters
#[derive(Debug, Clone)]
pub struct WindowedMinF64 {
    window: u64,
    samples: [Sample<f64>; 3],
    count: u64,
}

impl WindowedMinF64 {
    /// Creates a new windowed min tracker.
    ///
    /// `window` is in the same units as the timestamps you will pass
    /// to [`update`](Self::update). Must be positive.
    #[inline]
    pub fn new(window: u64) -> Result<Self, crate::ConfigError> {
        if window == 0 {
            return Err(crate::ConfigError::Invalid("window must be positive"));
        }
        let init = Sample {
            timestamp: 0,
            value: f64::MAX,
        };
        Ok(Self {
            window,
            samples: [init; 3],
            count: 0,
        })
    }

    /// Feeds a sample at the given timestamp. Returns current window min.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the value is NaN, or
    /// `DataError::Infinite` if the value is infinite.
    #[inline]
    pub fn update(&mut self, timestamp: u64, value: f64) -> Result<f64, crate::DataError> {
        check_finite!(value);
        self.count += 1;
        Ok(running(
            &mut self.samples,
            self.window,
            timestamp,
            value,
            |a, b| a <= b,
        ))
    }

    /// Convenience for `i64` timestamps (e.g., wire protocol epoch nanos).
    ///
    /// Timestamps must be non-negative. Negative values wrap to large
    /// `u64` values and will produce incorrect window expiration.
    #[inline]
    pub fn update_i64(&mut self, timestamp: i64, value: f64) -> Result<f64, crate::DataError> {
        debug_assert!(timestamp >= 0, "negative timestamp: {timestamp}");
        self.update(timestamp as u64, value)
    }

    /// Current window minimum, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn min(&self) -> Option<f64> {
        if self.count == 0 {
            None
        } else {
            Some(self.samples[0].value)
        }
    }

    /// Window size in raw units.
    #[inline]
    #[must_use]
    pub fn window(&self) -> u64 {
        self.window
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Resets to empty state. Window size is preserved.
    #[inline]
    pub fn reset(&mut self) {
        let init = Sample {
            timestamp: 0,
            value: f64::MAX,
        };
        self.samples = [init; 3];
        self.count = 0;
    }
}

/// Streaming windowed minimum over a sliding time window (Nichols' algorithm).
///
/// Tracks the minimum value within a `u64` timestamp window using only
/// 3 stored samples. O(1) amortized per update, `no_std` compatible.
///
/// # Use Cases
/// - Min RTT tracking (BBR)
/// - Minimum price in a window
/// - Best-case latency estimation
/// - Deterministic replay with raw tick counters
#[derive(Debug, Clone)]
pub struct WindowedMinI64 {
    window: u64,
    samples: [Sample<i64>; 3],
    count: u64,
}

impl WindowedMinI64 {
    /// Creates a new windowed min tracker.
    ///
    /// `window` is in the same units as the timestamps you will pass
    /// to [`update`](Self::update). Must be positive.
    #[inline]
    pub fn new(window: u64) -> Result<Self, crate::ConfigError> {
        if window == 0 {
            return Err(crate::ConfigError::Invalid("window must be positive"));
        }
        let init = Sample {
            timestamp: 0,
            value: i64::MAX,
        };
        Ok(Self {
            window,
            samples: [init; 3],
            count: 0,
        })
    }

    /// Feeds a sample at the given timestamp. Returns current window min.
    #[inline]
    #[must_use]
    pub fn update(&mut self, timestamp: u64, value: i64) -> i64 {
        self.count += 1;
        running(&mut self.samples, self.window, timestamp, value, |a, b| {
            a <= b
        })
    }

    /// Convenience for `i64` timestamps (e.g., wire protocol epoch nanos).
    ///
    /// Timestamps must be non-negative. Negative values wrap to large
    /// `u64` values and will produce incorrect window expiration.
    #[inline]
    #[must_use]
    pub fn update_i64(&mut self, timestamp: i64, value: i64) -> i64 {
        debug_assert!(timestamp >= 0, "negative timestamp: {timestamp}");
        self.update(timestamp as u64, value)
    }

    /// Current window minimum, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn min(&self) -> Option<i64> {
        if self.count == 0 {
            None
        } else {
            Some(self.samples[0].value)
        }
    }

    /// Window size in raw units.
    #[inline]
    #[must_use]
    pub fn window(&self) -> u64 {
        self.window
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Resets to empty state. Window size is preserved.
    #[inline]
    pub fn reset(&mut self) {
        let init = Sample {
            timestamp: 0,
            value: i64::MAX,
        };
        self.samples = [init; 3];
        self.count = 0;
    }
}

// --- pub(crate) f32 variants for normalizers ---

#[derive(Debug, Clone)]
pub(crate) struct WindowedMaxF32 {
    window: u64,
    samples: [Sample<f32>; 3],
    count: u64,
}

impl WindowedMaxF32 {
    #[inline]
    pub(crate) fn new(window: u64) -> Result<Self, crate::ConfigError> {
        if window == 0 {
            return Err(crate::ConfigError::Invalid("window must be positive"));
        }
        let init = Sample {
            timestamp: 0,
            value: f32::MIN,
        };
        Ok(Self {
            window,
            samples: [init; 3],
            count: 0,
        })
    }

    #[inline]
    pub(crate) fn update(&mut self, timestamp: u64, value: f32) -> Result<f32, crate::DataError> {
        check_finite!(value);
        self.count += 1;
        Ok(running(
            &mut self.samples,
            self.window,
            timestamp,
            value,
            |a, b| a >= b,
        ))
    }

    #[inline]
    pub(crate) fn max(&self) -> Option<f32> {
        if self.count == 0 {
            None
        } else {
            Some(self.samples[0].value)
        }
    }

    #[inline]
    pub(crate) fn count(&self) -> u64 {
        self.count
    }

    #[inline]
    pub(crate) fn reset(&mut self) {
        let init = Sample {
            timestamp: 0,
            value: f32::MIN,
        };
        self.samples = [init; 3];
        self.count = 0;
    }
}

#[derive(Debug, Clone)]
pub(crate) struct WindowedMinF32 {
    window: u64,
    samples: [Sample<f32>; 3],
    count: u64,
}

impl WindowedMinF32 {
    #[inline]
    pub(crate) fn new(window: u64) -> Result<Self, crate::ConfigError> {
        if window == 0 {
            return Err(crate::ConfigError::Invalid("window must be positive"));
        }
        let init = Sample {
            timestamp: 0,
            value: f32::MAX,
        };
        Ok(Self {
            window,
            samples: [init; 3],
            count: 0,
        })
    }

    #[inline]
    pub(crate) fn update(&mut self, timestamp: u64, value: f32) -> Result<f32, crate::DataError> {
        check_finite!(value);
        self.count += 1;
        Ok(running(
            &mut self.samples,
            self.window,
            timestamp,
            value,
            |a, b| a <= b,
        ))
    }

    #[inline]
    pub(crate) fn min(&self) -> Option<f32> {
        if self.count == 0 {
            None
        } else {
            Some(self.samples[0].value)
        }
    }

    #[inline]
    pub(crate) fn count(&self) -> u64 {
        self.count
    }

    #[inline]
    pub(crate) fn reset(&mut self) {
        let init = Sample {
            timestamp: 0,
            value: f32::MAX,
        };
        self.samples = [init; 3];
        self.count = 0;
    }
}

#[cfg(test)]
mod raw_tests {
    use super::*;

    #[test]
    fn raw_max_basic() {
        let mut wm = WindowedMaxF64::new(100).unwrap();
        assert_eq!(wm.update(0, 10.0).unwrap(), 10.0);
        assert_eq!(wm.update(50, 20.0).unwrap(), 20.0);
    }

    #[test]
    fn raw_max_expires() {
        let mut wm = WindowedMaxF64::new(10).unwrap();
        let _ = wm.update(0, 100.0).unwrap();
        let _ = wm.update(5, 50.0).unwrap();
        let result = wm.update(11, 60.0).unwrap();
        assert!(result <= 60.0);
    }

    #[test]
    fn raw_min_basic() {
        let mut wm = WindowedMinI64::new(100).unwrap();
        assert_eq!(wm.update(0, 100), 100);
        assert_eq!(wm.update(1, 50), 50);
    }

    #[test]
    fn raw_max_i64_convenience() {
        let mut wm = WindowedMaxF64::new(1000).unwrap();
        assert_eq!(wm.update_i64(100i64, 42.0).unwrap(), 42.0);
    }

    #[test]
    fn raw_rejects_zero_window() {
        assert!(WindowedMaxF64::new(0).is_err());
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut wm = WindowedMaxF64::new(100).unwrap();
        assert!(matches!(
            wm.update(0, f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
        assert!(matches!(
            wm.update(0, f64::INFINITY),
            Err(crate::DataError::Infinite)
        ));

        let mut wn = WindowedMinF64::new(100).unwrap();
        assert!(matches!(
            wn.update(0, f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
        assert!(matches!(
            wn.update(0, f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        ));
    }

    // The four-sample counterexample from #758: window 100, samples (t, v).
    // At t = 101 the window covers ages <= 100, so (0, 100) has aged out and the
    // true maximum is 90. The previous port returned 10.
    #[test]
    fn kernel_port_counterexample_max() {
        let mut wm = WindowedMaxI64::new(100).unwrap();
        for (t, v) in [(0u64, 100i64), (40, 90), (80, 10), (101, 5)] {
            let _ = wm.update(t, v);
        }
        assert_eq!(wm.max(), Some(90));

        let mut wf = WindowedMaxF64::new(100).unwrap();
        for (t, v) in [(0u64, 100.0f64), (40, 90.0), (80, 10.0), (101, 5.0)] {
            let _ = wf.update(t, v).unwrap();
        }
        assert_eq!(wf.max(), Some(90.0));
    }

    // The mirror case, which is the CoDel sojourn input: true minimum 20, the
    // previous port returned 100.
    #[test]
    fn kernel_port_counterexample_min() {
        let mut wm = WindowedMinI64::new(100).unwrap();
        for (t, v) in [(0u64, 10i64), (40, 20), (80, 100), (101, 105)] {
            let _ = wm.update(t, v);
        }
        assert_eq!(wm.min(), Some(20));

        let mut wf = WindowedMinF64::new(100).unwrap();
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
        let mut pmax = WindowedMaxI64::new(win).unwrap();
        let mut pmin = WindowedMinI64::new(win).unwrap();
        let mut exact = ExactWindow {
            win,
            samples: std::collections::VecDeque::new(),
        };
        let (mut t, mut bad_max, mut bad_min) = (0u64, 0usize, 0usize);
        for _ in 0..n {
            t += 1 + rng.below(4); // 1..=4 ticks apart
            let v = value(&mut rng);
            exact.push(t, v);
            let got_max = pmax.update(t, v);
            let got_min = pmin.update(t, v);
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
            let mut pmax = WindowedMaxI64::new(win).unwrap();
            let mut pmin = WindowedMinI64::new(win).unwrap();
            let mut hist: Vec<(u64, i64)> = Vec::new();
            let mut t = 0u64;
            for (gap, v) in steps {
                t += gap;
                hist.push((t, v));
                let exact_max = hist.iter().filter(|&&(ts, _)| t - ts <= win).map(|&(_, v)| v).max().unwrap();
                let exact_min = hist.iter().filter(|&&(ts, _)| t - ts <= win).map(|&(_, v)| v).min().unwrap();
                prop_assert!(pmax.update(t, v) <= exact_max);
                prop_assert!(pmin.update(t, v) >= exact_min);
            }
        }
    }
}
