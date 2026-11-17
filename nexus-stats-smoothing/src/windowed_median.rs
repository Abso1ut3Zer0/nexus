use alloc::boxed::Box;

use nexus_stats_core::Sample;
use nexus_stats_core::storage::Ring;

/// Windowed median with runtime-configured window size (requires `alloc` feature).
///
/// Maintains a ring buffer and an insertion-sorted shadow array
/// for O(N) update with O(1) median/quartile queries and an O(N),
/// allocation-free [`mad`](Self::mad).
///
/// # Use Cases
/// - Robust central tendency (median is outlier-resistant)
/// - IQR-based anomaly detection
/// - Modified z-score for non-normal distributions
#[derive(Clone)]
pub struct WindowedMedian<T: Sample> {
    /// Samples in arrival order; `push` hands back the evicted one.
    ring: Ring<T>,
    /// The same samples, sorted. Both buffers have the window's length;
    /// `sorted.len()` is the copy every accessor reads, so `is_primed` and
    /// `current_len` agree and the index checks fold against it.
    sorted: Box<[T]>,
    count: u64,
}

impl<T: Sample> WindowedMedian<T> {
    /// Creates a new windowed median tracker with the given window size.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if the window size is 0.
    #[inline]
    pub fn new(window_size: usize) -> Result<Self, nexus_stats_core::ConfigError> {
        if window_size == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "window size must be > 0",
            ));
        }
        let ring = Ring::new(window_size, T::ZERO)?;
        let sorted = alloc::vec![T::ZERO; window_size].into_boxed_slice();
        Ok(Self {
            ring,
            sorted,
            count: 0,
        })
    }

    /// The insertion/eviction step, shared by every instantiation.
    #[inline]
    fn fold(&mut self, sample: T) {
        let sorted = &mut *self.sorted;
        if let Some(evicted) = self.ring.push(sample) {
            // Full window: `sorted` is exactly the window, no `..len` view
            // needed. Where the evicted value sits in the sorted shadow:
            let remove_pos = rank_lt(sorted, evicted);
            // The sample lands on the side of `remove_pos` it compares to, so
            // rank it within that side as it looks once the evicted value is
            // gone, then close the gap with one memmove.
            if sample <= evicted {
                let insert_pos = rank_le(&sorted[..remove_pos], sample);
                sorted.copy_within(insert_pos..remove_pos, insert_pos + 1);
                sorted[insert_pos] = sample;
            } else {
                let insert_pos = remove_pos + rank_le(&sorted[remove_pos + 1..], sample);
                // Empty when the sample lands in the vacated slot itself.
                sorted.copy_within(remove_pos + 1..=insert_pos, remove_pos);
                sorted[insert_pos] = sample;
            }
        } else {
            // Filling: the shadow holds `len` sorted samples before this one.
            let len = self.ring.len() - 1;
            let insert_pos = rank_le(&sorted[..len], sample);
            sorted.copy_within(insert_pos..len, insert_pos + 1);
            sorted[insert_pos] = sample;
        }
        self.count += 1;
    }

    #[inline]
    fn current_len(&self) -> usize {
        self.count.min(self.sorted.len() as u64) as usize
    }

    /// Median value, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn median(&self) -> Option<T> {
        let len = self.current_len();
        if len == 0 {
            return None;
        }
        // Index through the `..len` view: LLVM folds `len / 2 < len` but not
        // the same index against the full buffer when `len` came from a min.
        let sorted = &self.sorted[..len];
        if len % 2 == 1 {
            Some(sorted[len / 2])
        } else {
            Some(T::midpoint(sorted[len / 2 - 1], sorted[len / 2]))
        }
    }

    /// Returns the q-th quantile of the current window.
    ///
    /// `q = 0.0` returns the minimum, `q = 1.0` returns the maximum,
    /// `q = 0.5` matches [`median()`](Self::median) for odd window sizes.
    ///
    /// Returns `None` if the window is empty.
    ///
    /// # Panics
    ///
    /// Panics if `q` is not in `[0.0, 1.0]`.
    #[inline]
    #[must_use]
    pub fn quantile(&self, q: f64) -> Option<T> {
        assert!(q >= 0.0 && q <= 1.0, "quantile must be in [0.0, 1.0]");
        let len = self.current_len();
        if len == 0 {
            return None;
        }
        let sorted = &self.sorted[..len];
        let idx = ((len - 1) as f64 * q) as usize;
        Some(sorted[idx])
    }

    /// Median Absolute Deviation (MAD), or `None` if empty.
    ///
    /// O(N), allocation-free and branch-free: the deviations are never
    /// materialized or sorted. The `k + 1` points nearest the median are
    /// consecutive in sorted order, so the `k`-th deviation is the tightest
    /// such window, found with one vectorized count.
    #[inline]
    #[must_use]
    pub fn mad(&self) -> Option<T> {
        let median = self.median()?;
        let len = self.current_len();
        let sorted = &self.sorted[..len];
        let mid = len / 2;
        let upper = kth_deviation(sorted, median, mid);
        if len % 2 == 1 {
            Some(upper)
        } else {
            Some(T::midpoint(kth_deviation(sorted, median, mid - 1), upper))
        }
    }

    /// First quartile (Q1), or `None` if < 4 samples.
    #[inline]
    #[must_use]
    pub fn q1(&self) -> Option<T> {
        let len = self.current_len();
        if len < 4 {
            None
        } else {
            Some(self.sorted[..len][len / 4])
        }
    }

    /// Third quartile (Q3), or `None` if < 4 samples.
    #[inline]
    #[must_use]
    pub fn q3(&self) -> Option<T> {
        let len = self.current_len();
        if len < 4 {
            None
        } else {
            Some(self.sorted[..len][3 * len / 4])
        }
    }

    /// Interquartile range (Q3 - Q1), or `None` if < 4 samples.
    #[inline]
    #[must_use]
    pub fn iqr(&self) -> Option<T> {
        match (self.q1(), self.q3()) {
            (Some(q1), Some(q3)) => Some(q3 - q1),
            _ => None,
        }
    }

    /// Modified z-score: `0.6745 * (x - median) / MAD`.
    #[inline]
    #[must_use]
    pub fn modified_z_score(&self, sample: T) -> Option<f64> {
        let median = self.median()?;
        let mad = self.mad()?;
        if mad == T::ZERO {
            return None;
        }
        Some(0.6745 * (sample - median).to_f64() / mad.to_f64())
    }

    /// Window size.
    #[inline]
    #[must_use]
    pub fn window_size(&self) -> usize {
        self.sorted.len()
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the window is full.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.sorted.len() as u64
    }

    /// Resets to empty state.
    #[inline]
    pub fn reset(&mut self) {
        self.ring.clear(T::ZERO);
        self.sorted.fill(T::ZERO);
        self.count = 0;
    }
}

impl<T: Sample> core::fmt::Debug for WindowedMedian<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("WindowedMedian")
            .field("window", &self.sorted.len())
            .field("count", &self.count)
            .finish()
    }
}

impl WindowedMedian<f64> {
    /// Feeds a sample.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(sample);
        self.fold(sample);
        Ok(())
    }
}

impl WindowedMedian<i64> {
    /// Feeds a sample.
    #[inline]
    pub fn update(&mut self, sample: i64) {
        self.fold(sample);
    }
}

/// Up to this many elements a vectorized linear count beats a binary search:
/// the compares are independent, where each search step waits on the load
/// before it. Measured on x86_64 (SSE2 baseline): linear wins at 64 (99 vs
/// 115 ticks per update) and loses at 128 (139 vs 131).
const LINEAR_RANK_MAX: usize = 64;

/// Number of elements `< x` in a sorted slice: the index of the first `>= x`.
#[inline]
fn rank_lt<T: Sample>(sorted: &[T], x: T) -> usize {
    if sorted.len() <= LINEAR_RANK_MAX {
        sorted.iter().filter(|&&v| v < x).count()
    } else {
        sorted.partition_point(|&v| v < x)
    }
}

/// Number of elements `<= x` in a sorted slice: the index of the first `> x`.
#[inline]
fn rank_le<T: Sample>(sorted: &[T], x: T) -> usize {
    if sorted.len() <= LINEAR_RANK_MAX {
        sorted.iter().filter(|&&v| v <= x).count()
    } else {
        sorted.partition_point(|&v| v <= x)
    }
}

/// The `k`-th smallest (0-based) absolute deviation from `median` over a
/// sorted, non-empty slice with `k < sorted.len()`.
///
/// The `k + 1` points nearest the median are `k + 1` consecutive sorted
/// points, so the answer is the tightest such window:
/// `min over a of max(median - s[a], s[a + k] - median)`. The left term falls
/// and the right term rises with `a`, so the minimum sits where they cross.
/// The crossover is a count of the positions where the right term is still
/// below the left one: independent compares, no dependency chain and no
/// data-dependent branch.
#[inline]
fn kth_deviation<T: Sample>(sorted: &[T], median: T, k: usize) -> T {
    let last = sorted.len() - 1 - k;
    let cross = (0..=last)
        .filter(|&a| sorted[a + k] - median < median - sorted[a])
        .count();
    // At `cross` the right term dominates, one before it the left one does;
    // a side that does not exist cannot be the minimum.
    let right = if cross <= last {
        sorted[cross + k] - median
    } else {
        T::MAX
    };
    let left = if cross > 0 {
        median - sorted[cross - 1]
    } else {
        T::MAX
    };
    if right <= left { right } else { left }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[3.0, 1.0, 4.0, 1.0, 5.0] {
            wm.update(v).unwrap();
        }
        assert_eq!(wm.median(), Some(3.0));
    }

    #[test]
    fn reset() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[1.0, 2.0, 3.0] {
            wm.update(v).unwrap();
        }
        wm.reset();
        assert_eq!(wm.count(), 0);
        assert!(wm.median().is_none());
    }

    #[test]
    fn empty() {
        let wm = WindowedMedian::<f64>::new(10).unwrap();
        assert!(wm.median().is_none());
        assert!(wm.mad().is_none());
    }

    #[test]
    fn single_sample() {
        let mut wm = WindowedMedian::<f64>::new(10).unwrap();
        wm.update(42.0).unwrap();
        assert_eq!(wm.median(), Some(42.0));
    }

    #[test]
    fn known_median_odd() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[3.0, 1.0, 4.0, 1.0, 5.0] {
            wm.update(v).unwrap();
        }
        // sorted: [1, 1, 3, 4, 5], median = 3
        assert_eq!(wm.median(), Some(3.0));
    }

    #[test]
    fn known_median_even() {
        let mut wm = WindowedMedian::<f64>::new(4).unwrap();
        for &v in &[1.0, 3.0, 5.0, 7.0] {
            wm.update(v).unwrap();
        }
        // sorted: [1, 3, 5, 7], median = (3+5)/2 = 4
        assert_eq!(wm.median(), Some(4.0));
    }

    #[test]
    fn mad_correctness() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[1.0, 2.0, 3.0, 4.0, 5.0] {
            wm.update(v).unwrap();
        }
        // median = 3, deviations = [2, 1, 0, 1, 2], sorted = [0, 1, 1, 2, 2]
        // MAD = 1.0
        assert_eq!(wm.mad(), Some(1.0));
    }

    #[test]
    fn iqr() {
        let mut wm = WindowedMedian::<f64>::new(8).unwrap();
        for &v in &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0] {
            wm.update(v).unwrap();
        }
        let q1 = wm.q1().unwrap();
        let q3 = wm.q3().unwrap();
        assert!(q3 > q1, "Q3 ({q3}) should be > Q1 ({q1})");
        assert!(wm.iqr().is_some());
    }

    #[test]
    fn modified_z_score() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[1.0, 2.0, 3.0, 4.0, 5.0] {
            wm.update(v).unwrap();
        }
        let z = wm.modified_z_score(10.0);
        assert!(z.is_some());
        assert!(z.unwrap() > 0.0, "outlier should have positive z-score");
    }

    #[test]
    fn window_rolls() {
        let mut wm = WindowedMedian::<f64>::new(3).unwrap();
        wm.update(10.0).unwrap();
        wm.update(20.0).unwrap();
        wm.update(30.0).unwrap();
        assert_eq!(wm.median(), Some(20.0));

        // Roll in new values
        wm.update(100.0).unwrap(); // evicts 10
        // sorted: [20, 30, 100], median = 30
        assert_eq!(wm.median(), Some(30.0));
    }

    #[test]
    fn i64_basic() {
        let mut wm = WindowedMedian::<i64>::new(5).unwrap();
        for v in [3, 1, 4, 1, 5] {
            wm.update(v);
        }
        assert_eq!(wm.median(), Some(3));
    }

    #[test]
    fn priming() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for _ in 0..4 {
            wm.update(1.0).unwrap();
            assert!(!wm.is_primed());
        }
        wm.update(1.0).unwrap();
        assert!(wm.is_primed());
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        assert!(matches!(
            wm.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        assert!(matches!(
            wm.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert!(matches!(
            wm.update(f64::NEG_INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert_eq!(wm.count(), 0);
    }

    #[test]
    fn quantile_matches_median() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[3.0, 1.0, 4.0, 1.0, 5.0] {
            wm.update(v).unwrap();
        }
        // sorted: [1.0, 1.0, 3.0, 4.0, 5.0] — median = 3.0
        assert_eq!(wm.quantile(0.5).unwrap(), wm.median().unwrap());
    }

    #[test]
    fn quantile_extremes() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[10.0, 20.0, 30.0, 40.0, 50.0] {
            wm.update(v).unwrap();
        }
        // sorted: [10, 20, 30, 40, 50]
        assert_eq!(wm.quantile(0.0).unwrap(), 10.0);
        assert_eq!(wm.quantile(1.0).unwrap(), 50.0);
    }

    #[test]
    fn quantile_75th() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[10.0, 20.0, 30.0, 40.0, 50.0] {
            wm.update(v).unwrap();
        }
        // sorted: [10, 20, 30, 40, 50]
        // idx = (4) * 0.75 = 3.0 -> sorted[3] = 40.0
        assert_eq!(wm.quantile(0.75).unwrap(), 40.0);
    }

    #[test]
    fn quantile_empty_returns_none() {
        let wm = WindowedMedian::<f64>::new(5).unwrap();
        assert!(wm.quantile(0.5).is_none());
    }

    #[test]
    #[should_panic(expected = "quantile must be in [0.0, 1.0]")]
    fn quantile_out_of_range() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        wm.update(1.0).unwrap();
        let _ = wm.quantile(1.5);
    }

    /// Median, extremes and `mad()` against a sorted copy of the window (MAD by
    /// the textbook definition: sort the absolute deviations, take their
    /// median) for every window length, odd and even, growing and full, with
    /// plenty of ties.
    #[test]
    fn matches_a_sorted_copy_for_every_window_length() {
        let mut rng = 0x9E37_79B9_7F4A_7C15u64;
        for window in (1..=40).chain([65, 128]) {
            let mut wm = WindowedMedian::<f64>::new(window).unwrap();
            let mut wi = WindowedMedian::<i64>::new(window).unwrap();
            let mut history = Vec::new();
            for _ in 0..window * 3 {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                let x = (rng % 7) as i64;
                wm.update(x as f64).unwrap();
                wi.update(x);
                history.push(x);
                let len = history.len().min(window);
                let mut recent: Vec<i64> = history[history.len() - len..].to_vec();
                recent.sort_unstable();
                let median_i = if len % 2 == 1 {
                    recent[len / 2]
                } else {
                    i64::midpoint(recent[len / 2 - 1], recent[len / 2])
                };
                let median_f = if len % 2 == 1 {
                    recent[len / 2] as f64
                } else {
                    f64::midpoint(recent[len / 2 - 1] as f64, recent[len / 2] as f64)
                };
                let mut dev_i: Vec<i64> = recent.iter().map(|&v| (v - median_i).abs()).collect();
                dev_i.sort_unstable();
                let mut dev_f: Vec<f64> = recent
                    .iter()
                    .map(|&v| (v as f64 - median_f).abs())
                    .collect();
                dev_f.sort_by(f64::total_cmp);
                let mad_i = if len % 2 == 1 {
                    dev_i[len / 2]
                } else {
                    i64::midpoint(dev_i[len / 2 - 1], dev_i[len / 2])
                };
                let mad_f = if len % 2 == 1 {
                    dev_f[len / 2]
                } else {
                    f64::midpoint(dev_f[len / 2 - 1], dev_f[len / 2])
                };
                assert_eq!(wi.median(), Some(median_i), "i64 window {window} len {len}");
                assert_eq!(wm.median(), Some(median_f), "f64 window {window} len {len}");
                assert_eq!(wm.quantile(0.0), Some(recent[0] as f64));
                assert_eq!(wm.quantile(1.0), Some(recent[len - 1] as f64));
                assert_eq!(wi.mad(), Some(mad_i), "i64 window {window} len {len}");
                assert_eq!(wm.mad(), Some(mad_f), "f64 window {window} len {len}");
            }
        }
    }

    /// The new sample lands exactly where the evicted one was, from above
    /// (`evicted < sample <= next`) and from below (`prev <= sample < evicted`):
    /// the shift is empty and the slot is simply overwritten.
    #[test]
    fn sample_landing_in_the_vacated_slot() {
        let mut wm = WindowedMedian::<f64>::new(3).unwrap();
        for x in [1.0, 5.0, 9.0] {
            wm.update(x).unwrap();
        }
        // Evicts 1.0; 3.0 sits before 5.0, i.e. in slot 0 where 1.0 was.
        wm.update(3.0).unwrap();
        assert_eq!(wm.median(), Some(5.0));
        assert_eq!(wm.quantile(0.0), Some(3.0));
        // Evicts 5.0; 4.0 sits after 3.0, i.e. in slot 1 where 5.0 was.
        wm.update(4.0).unwrap();
        assert_eq!(wm.median(), Some(4.0));
        assert_eq!(wm.quantile(0.0), Some(3.0));
        assert_eq!(wm.quantile(1.0), Some(9.0));
    }

    /// `reset` leaves no residue in the ring or the sorted shadow: a replay
    /// reproduces every median and MAD, including across the wrap.
    #[test]
    fn reset_then_replay_matches() {
        let mut w = WindowedMedian::<f64>::new(5).unwrap();
        let stream = [5.0, 1.0, 9.0, 3.0, 7.0, 2.0, 8.0, 4.0, 6.0, 0.0, 10.0, 5.5];
        let run = |w: &mut WindowedMedian<f64>| -> Vec<(Option<u64>, Option<u64>)> {
            stream
                .iter()
                .map(|&x| {
                    w.update(x).unwrap();
                    (w.median().map(f64::to_bits), w.mad().map(f64::to_bits))
                })
                .collect()
        };
        let first = run(&mut w);
        w.reset();
        assert_eq!(w.count(), 0);
        let second = run(&mut w);
        assert_eq!(first, second);
    }
}
