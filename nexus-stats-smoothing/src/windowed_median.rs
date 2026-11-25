use alloc::boxed::Box;

use nexus_stats_core::Sample;
use nexus_stats_core::storage::Ring;

/// Windowed median with runtime-configured window size (requires `alloc` feature).
///
/// Maintains a ring buffer and an insertion-sorted shadow array
/// for O(N) update with O(1) median/quantile queries and an O(N),
/// allocation-free [`mad`](Self::mad).
///
/// Quantiles follow Hyndman and Fan's type 7 (1996), the default in NumPy
/// and R: with `h = (len - 1) * q`, the value at `floor(h)` plus the
/// fraction `h - floor(h)` of the step to the next one. [`median`],
/// [`quantile`] and [`quartiles`] share the rule, so `quantile(0.5)` is
/// `median()` at every length. Interpolation is
/// [`Sample::lerp`](nexus_stats_core::Sample::lerp): NumPy's arithmetic for
/// `f64`, and for `i64` the nearest integer, ties toward zero. Where the
/// interpolation falls exactly halfway, as `quantile(0.5)` does on an even
/// window, the result is the exact midpoint, as `np.median` gives, and
/// `np.quantile` can differ from it in the last bits.
///
/// `update` ignores a NaN: the window and the count stay as they were, and
/// [`checked_update`](Self::checked_update) reports it. An infinity is a
/// value like any other.
///
/// [`median`]: Self::median
/// [`quantile`]: Self::quantile
/// [`quartiles`]: Self::quartiles
///
/// # Use Cases
/// - Robust central tendency (median is outlier-resistant)
/// - IQR-based anomaly detection
/// - Modified z-score for non-normal distributions
///
/// # Example
///
/// ```
/// use nexus_stats_smoothing::WindowedMedian;
///
/// let mut wm = WindowedMedian::<f64>::new(4).unwrap();
/// for x in [0.0, 1.0, 2.0, 3.0] {
///     wm.update(x);
/// }
/// let q = wm.quartiles().unwrap();
/// assert_eq!((q.q1, q.median, q.q3), (0.75, 1.5, 2.25));
/// assert_eq!(q.iqr(), 1.5);
/// ```
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

    /// The `q`-th quantile of the current window (type 7), or `None` if
    /// empty.
    ///
    /// `q = 0.0` is the minimum, `q = 1.0` the maximum, and `q = 0.5` is
    /// [`median()`](Self::median).
    ///
    /// # Panics
    ///
    /// Panics if `q` is NaN or outside `[0.0, 1.0]`. See
    /// [`checked_quantile`](Self::checked_quantile).
    #[inline]
    #[must_use]
    pub fn quantile(&self, q: f64) -> Option<T> {
        assert!(q >= 0.0 && q <= 1.0, "quantile must be in [0.0, 1.0]");
        self.type7(q)
    }

    /// [`quantile`](Self::quantile) without the panic: `Ok(None)` if empty.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `q` is NaN.
    /// - [`DataError::OutOfRange`](nexus_stats_core::DataError::OutOfRange)
    ///   if `q` is outside `[0.0, 1.0]`.
    #[inline]
    pub fn checked_quantile(&self, q: f64) -> Result<Option<T>, nexus_stats_core::DataError> {
        if q.is_nan() {
            return Err(nexus_stats_core::DataError::NotANumber);
        }
        if !(0.0..=1.0).contains(&q) {
            return Err(nexus_stats_core::DataError::OutOfRange);
        }
        Ok(self.type7(q))
    }

    /// The first quartile, the median and the third quartile, read from one
    /// window (type 7), or `None` if empty.
    #[inline]
    #[must_use]
    pub fn quartiles(&self) -> Option<Quartiles<T>> {
        Some(Quartiles {
            q1: self.type7(0.25)?,
            median: self.median()?,
            q3: self.type7(0.75)?,
        })
    }

    /// Hyndman-Fan type 7 for `q` in `[0, 1]`.
    #[inline]
    fn type7(&self, q: f64) -> Option<T> {
        let len = self.current_len();
        if len == 0 {
            return None;
        }
        let sorted = &self.sorted[..len];
        let h = (len - 1) as f64 * q;
        let k = h as usize;
        let t = h - k as f64;
        // `t > 0` only below the last index, since `h <= len - 1`.
        if t == 0.0 {
            Some(sorted[k])
        } else {
            Some(sorted[k].lerp(sorted[k + 1], t))
        }
    }

    /// Median Absolute Deviation (MAD), or `None` if empty.
    ///
    /// NaN when the median is infinite or NaN: the deviations from it are
    /// `inf - inf`, as SciPy's `median_abs_deviation` gives.
    ///
    /// O(N), allocation-free and branch-free: the deviations are never
    /// materialized or sorted. The `k + 1` points nearest the median are
    /// consecutive in sorted order, so the `k`-th deviation is the tightest
    /// such window, found with one vectorized count.
    #[inline]
    #[must_use]
    pub fn mad(&self) -> Option<T> {
        let median = self.median()?;
        if !median.is_finite() {
            // The deviation of the median from itself, `inf - inf`: NaN.
            #[allow(clippy::eq_op)]
            return Some(median - median);
        }
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

    /// Feeds a sample and returns the median, or `None` while the window is
    /// empty. A NaN is ignored: the window and the count stay as they were.
    #[inline]
    pub fn update(&mut self, sample: T) -> Option<T> {
        if !sample.is_nan() {
            self.fold(sample);
        }
        self.median()
    }

    /// [`update`](Self::update), but a NaN is returned as an error instead
    /// of being ignored. The window is unchanged on an error. Infinity is
    /// accepted.
    ///
    /// # Errors
    ///
    /// [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber) if
    /// `sample` is NaN.
    #[inline]
    pub fn checked_update(&mut self, sample: T) -> Result<Option<T>, nexus_stats_core::DataError> {
        if sample.is_nan() {
            return Err(nexus_stats_core::DataError::NotANumber);
        }
        Ok(self.update(sample))
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

/// A [`WindowedMedian`] reading: the three quartiles of one window.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Quartiles<T> {
    /// First quartile, `quantile(0.25)`.
    pub q1: T,
    /// Median, `quantile(0.5)`.
    pub median: T,
    /// Third quartile, `quantile(0.75)`.
    pub q3: T,
}

impl<T: Sample> Quartiles<T> {
    /// Interquartile range, `q3 - q1`.
    #[inline]
    #[must_use]
    pub fn iqr(&self) -> T {
        self.q3 - self.q1
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
            wm.update(v);
        }
        assert_eq!(wm.median(), Some(3.0));
    }

    #[test]
    fn reset() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[1.0, 2.0, 3.0] {
            wm.update(v);
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
        wm.update(42.0);
        assert_eq!(wm.median(), Some(42.0));
    }

    #[test]
    fn known_median_odd() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[3.0, 1.0, 4.0, 1.0, 5.0] {
            wm.update(v);
        }
        // sorted: [1, 1, 3, 4, 5], median = 3
        assert_eq!(wm.median(), Some(3.0));
    }

    #[test]
    fn known_median_even() {
        let mut wm = WindowedMedian::<f64>::new(4).unwrap();
        for &v in &[1.0, 3.0, 5.0, 7.0] {
            wm.update(v);
        }
        // sorted: [1, 3, 5, 7], median = (3+5)/2 = 4
        assert_eq!(wm.median(), Some(4.0));
    }

    #[test]
    fn mad_correctness() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[1.0, 2.0, 3.0, 4.0, 5.0] {
            wm.update(v);
        }
        // median = 3, deviations = [2, 1, 0, 1, 2], sorted = [0, 1, 1, 2, 2]
        // MAD = 1.0
        assert_eq!(wm.mad(), Some(1.0));
    }

    #[test]
    fn iqr_is_symmetric() {
        let mut wm = WindowedMedian::<f64>::new(4).unwrap();
        for v in [0.0, 1.0, 2.0, 3.0] {
            wm.update(v);
        }
        // NumPy: quantile([0, 1, 2, 3], [0.25, 0.75]) = [0.75, 2.25].
        assert_eq!(wm.quartiles().map(|q| q.iqr()), Some(1.5));
    }

    #[test]
    fn modified_z_score() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[1.0, 2.0, 3.0, 4.0, 5.0] {
            wm.update(v);
        }
        let z = wm.modified_z_score(10.0);
        assert!(z.is_some());
        assert!(z.unwrap() > 0.0, "outlier should have positive z-score");
    }

    #[test]
    fn window_rolls() {
        let mut wm = WindowedMedian::<f64>::new(3).unwrap();
        wm.update(10.0);
        wm.update(20.0);
        wm.update(30.0);
        assert_eq!(wm.median(), Some(20.0));

        // Roll in new values
        wm.update(100.0); // evicts 10
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
            wm.update(1.0);
            assert!(!wm.is_primed());
        }
        wm.update(1.0);
        assert!(wm.is_primed());
    }

    #[test]
    fn nan_is_ignored() {
        let mut wm = WindowedMedian::<f64>::new(3).unwrap();
        assert_eq!(wm.update(f64::NAN), None);
        assert_eq!(wm.count(), 0);
        for x in [1.0, 5.0, 9.0] {
            wm.update(x);
        }
        assert_eq!(wm.update(f64::NAN), Some(5.0));
        assert_eq!(wm.count(), 3);
        // Nothing was evicted for the NaN: the next sample evicts 1.0.
        assert_eq!(wm.update(7.0), Some(7.0));
        assert_eq!(wm.quantile(0.0), Some(5.0));
    }

    #[test]
    fn infinity_is_a_value() {
        let mut wm = WindowedMedian::<f64>::new(4).unwrap();
        for x in [f64::NEG_INFINITY, 1.0, 2.0, f64::INFINITY] {
            wm.update(x);
        }
        assert_eq!(wm.median(), Some(1.5));
        assert_eq!(wm.quantile(0.1), Some(f64::NEG_INFINITY));
        assert_eq!(wm.quantile(0.9), Some(f64::INFINITY));
        assert_eq!(wm.quantile(1.0), Some(f64::INFINITY));
    }

    #[test]
    fn quantile_matches_median() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[3.0, 1.0, 4.0, 1.0, 5.0] {
            wm.update(v);
        }
        // sorted: [1.0, 1.0, 3.0, 4.0, 5.0] — median = 3.0
        assert_eq!(wm.quantile(0.5).unwrap(), wm.median().unwrap());
    }

    #[test]
    fn quantile_extremes() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[10.0, 20.0, 30.0, 40.0, 50.0] {
            wm.update(v);
        }
        // sorted: [10, 20, 30, 40, 50]
        assert_eq!(wm.quantile(0.0).unwrap(), 10.0);
        assert_eq!(wm.quantile(1.0).unwrap(), 50.0);
    }

    #[test]
    fn quantile_75th() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        for &v in &[10.0, 20.0, 30.0, 40.0, 50.0] {
            wm.update(v);
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
        wm.update(1.0);
        let _ = wm.quantile(1.5);
    }

    #[test]
    #[should_panic(expected = "quantile must be in [0.0, 1.0]")]
    fn quantile_nan_panics() {
        let mut wm = WindowedMedian::<f64>::new(5).unwrap();
        wm.update(1.0);
        let _ = wm.quantile(f64::NAN);
    }

    #[test]
    fn checked_quantile_refuses_what_quantile_panics_on() {
        use nexus_stats_core::DataError;
        let mut wm = WindowedMedian::<i64>::new(5).unwrap();
        assert_eq!(wm.checked_quantile(0.5), Ok(None));
        wm.update(3);
        assert_eq!(wm.checked_quantile(f64::NAN), Err(DataError::NotANumber));
        for q in [-0.0001, 1.0001, f64::INFINITY, f64::NEG_INFINITY] {
            assert_eq!(wm.checked_quantile(q), Err(DataError::OutOfRange), "q {q}");
        }
        for q in [0.0, -0.0, 0.3, 1.0] {
            assert_eq!(wm.checked_quantile(q), Ok(Some(3)), "q {q}");
        }
    }

    /// `numpy.quantile(numpy.arange(len), q)` (NumPy 2.5.3, the default
    /// `linear` method) for every length from 1 to 12.
    #[test]
    fn matches_numpy_on_0_to_len() {
        const QS: [f64; 7] = [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0];
        #[rustfmt::skip]
        const NUMPY: [[f64; 7]; 12] = [
            [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0],
            [0.0, 0.2, 0.5, 1.0, 1.5, 1.8, 2.0],
            [0.0, 0.300_000_000_000_000_04, 0.75, 1.5, 2.25, 2.7, 3.0],
            [0.0, 0.4, 1.0, 2.0, 3.0, 3.6, 4.0],
            [0.0, 0.5, 1.25, 2.5, 3.75, 4.5, 5.0],
            [0.0, 0.600_000_000_000_000_1, 1.5, 3.0, 4.5, 5.4, 6.0],
            [0.0, 0.700_000_000_000_000_1, 1.75, 3.5, 5.25, 6.3, 7.0],
            [0.0, 0.8, 2.0, 4.0, 6.0, 7.2, 8.0],
            [0.0, 0.9, 2.25, 4.5, 6.75, 8.1, 9.0],
            [0.0, 1.0, 2.5, 5.0, 7.5, 9.0, 10.0],
            [0.0, 1.1, 2.75, 5.5, 8.25, 9.9, 11.0],
        ];
        for (len, expected) in (1..=12).zip(NUMPY) {
            let mut wm = WindowedMedian::<f64>::new(len).unwrap();
            let mut wi = WindowedMedian::<i64>::new(len).unwrap();
            // Fed in reverse, so the sorted shadow does the work.
            for x in (0..len).rev() {
                wm.update(x as f64);
                wi.update(x as i64);
            }
            for (q, want) in QS.into_iter().zip(expected) {
                assert_eq!(wm.quantile(q), Some(want), "len {len} q {q}");
                // Nearest, ties toward zero: these values are all >= 0.
                let rounded = if want.fract() == 0.5 {
                    want.floor()
                } else {
                    want.round()
                };
                assert_eq!(wi.quantile(q), Some(rounded as i64), "i64 len {len} q {q}");
            }
        }
    }

    /// The identities that tie the readings to one rule, for every length,
    /// growing and full, on both types and with ties and negatives.
    #[test]
    fn readings_share_one_rule_at_every_length() {
        let mut rng = 0x2545_F491_4F6C_DD1Du64;
        for window in 1..=24 {
            let mut wm = WindowedMedian::<f64>::new(window).unwrap();
            let mut wi = WindowedMedian::<i64>::new(window).unwrap();
            for _ in 0..window * 3 {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                let x = (rng % 41) as i64 - 20;
                wm.update(x as f64 * 0.37);
                wi.update(x);
                let qf = wm.quartiles().unwrap();
                let qi = wi.quartiles().unwrap();
                assert_eq!(Some(qf.median), wm.median());
                assert_eq!(Some(qf.median), wm.quantile(0.5));
                assert_eq!(Some(qf.q1), wm.quantile(0.25));
                assert_eq!(Some(qf.q3), wm.quantile(0.75));
                assert_eq!(Some(qi.median), wi.median());
                assert_eq!(Some(qi.median), wi.quantile(0.5));
                assert_eq!(Some(qi.q1), wi.quantile(0.25));
                assert_eq!(Some(qi.q3), wi.quantile(0.75));
                let mut last = (f64::NEG_INFINITY, i64::MIN);
                for step in 0..=200 {
                    let q = f64::from(step) / 200.0;
                    let now = (wm.quantile(q).unwrap(), wi.quantile(q).unwrap());
                    assert!(now.0 >= last.0 && now.1 >= last.1, "window {window} q {q}");
                    last = now;
                }
            }
        }
    }

    const RANDOM_QS: [f64; 5] = [0.1, 0.25, 0.33, 0.5, 0.9];

    /// Random windows against `numpy.quantile` (NumPy 2.5.3). Where the
    /// interpolation falls exactly halfway the expected value is the exact
    /// midpoint, by design. Each window is fed three extra samples first,
    /// so eviction is exercised.
    #[test]
    #[allow(clippy::unreadable_literal)]
    fn matches_numpy_on_random_windows() {
        #[rustfmt::skip]
        let cases: [(usize, &[f64], [f64; 5]); 8] = [
            (2, &[0.00817250634952393, 290087.8636295074, 14.72393, 64.4, 2.0], [8.240000000000002, 17.6, 22.592000000000002, 33.2, 58.160000000000004]),
            (10, &[-47.2739, 7.0, 0.0005317085846928424, 82.46308, -495233.70694717905, 6.0, 3.535877428145167e-05, 0.07423638033046545, -2.0, 165.436386, 5.0, -7.599110759721109e-05, 129.0], [-49525.17069471789, -4.8153637127545395e-05, 3.201827782509181e-05, 2.537118190165233, 132.64363859999997]),
            (3, &[-59.33584631618631, 31.09, 9.573474461438093e-05, 18.835971221881522, -140.62, 8.0], [-110.896, -66.31, -42.5308, 8.0, 16.668776977505217]),
            (5, &[-84.495, -153.27187, -125.09, 4.0, -0.006314223985362544, 113.6737, 20.1, -188.68375], [-113.21277568959414, -0.006314223985362544, 1.2757063276899536, 4.0, 76.24422000000001]),
            (11, &[-5.0, -99.305, -4.0, 96.12, 8.281485662827795e-05, -9.0, -843295.1451011808, 179.96268, -36.5, 47.32787, -8.0, 186.23, -105.68242090525226, -26.97352], [-105.68242090525226, -31.73676, -21.581463999999997, -8.0, 179.96268]),
            (6, &[65.0, 1.0, -104.0, -19.8515, -3.1, 91.516, -130.796503, -83.0, -88612.54547269439], [-44371.670987847196, -118.84737725, -99.72877605, -51.42575, 44.208000000000006]),
            (7, &[-14.75, -21.7, 79.19584, -34.328803, -0.00038699756865399307, -6.0, -5.2803, 162.6, -7.76859377159527e-05, 4.0], [-17.331521199999997, -5.64015, -5.294694000000001, -0.00038699756865399307, 67.44000000000005]),
            (6, &[-1.0, 20.4, 68.08404, 51.1812, 146.6565, -6.81359, -72.19, -0.4304121467435924, 6.338514148604047e-06], [-39.501795, -5.217795536685898, -2.664524395383334, -0.2152029041147219, 98.91884999999999]),
        ];
        for (window, samples, expected) in cases {
            let mut wm = WindowedMedian::<f64>::new(window).unwrap();
            for &x in samples {
                wm.update(x);
            }
            for (q, want) in RANDOM_QS.into_iter().zip(expected) {
                assert_eq!(wm.quantile(q), Some(want), "window {window} q {q}");
            }
        }
    }

    /// Random `i64` windows, up to the full range, against exact rational
    /// arithmetic rounded to the nearest value, ties toward zero.
    #[test]
    #[allow(clippy::unreadable_literal)]
    fn matches_exact_arithmetic_on_random_integer_windows() {
        #[rustfmt::skip]
        let cases: [(usize, &[i64], [i64; 5]); 8] = [
            (8, &[-3833152736693627395, -232003497388735066, 4080473775159991937, 28, 4793289647508162802, 9077485341701189391, -18, -7791269336909370249, 45, -19, 662783445940630], [-2337380801072810569, -18, -4, 36, 6078548355766070018]),
            (10, &[-22, 90300607500170, -8821479556438162177, -5, -442018775923861, -195377806676567, 192948502787272709, 48, -22, 1, -8043287699345190330, 6796959819384042033, 7034374045150974867], [-804726586832850329, -146533355007431, -5861334200318, -2, 6820701241960735232]),
            (4, &[722664838361796, -2129905507390868444, 6, -31, 9159346194130709476, 8652877700395296292, 35], [-11, 18, 34, 4326438850197648163, 9007405646010085611]),
            (10, &[45, 46, -144727319440631, -325648531073784, 4788016795744362475, 16, -30, 1622727836846618507, -2577996567643607187, -920788823980826, 769051843397665, -47, 48], [-258628366705943405, -244236398305350, -9769455932259, -7, 1939256732736391779]),
            (5, &[-48, 178074439908772, 376302503001073, 24, -104535388066474, -9178099528283522378, -712915874923620, 33], [-5507144883320082671, -712915874923620, -518234119129333, -104535388066474, 29]),
            (2, &[7668104597061654247, -2657270099507999772, -12, 45, 325883792638411], [32588379263882, 81470948159636, 107541651570706, 162941896319228, 293295413374574]),
            (4, &[-17, 35, -40, -7, -163259434064019, 247326422852466, -3656798902826876433], [-2559808209809032546, -914322170282267122, -36729615867992176, -81629717032013, 173128495996724]),
            (8, &[8538505121527840205, 48, -12378541680415, -5982228131118622579, 648688818511925, 5560143737095218286, -11, 8651881587032278070, 404684872001344, 707502593906327, 450386475412660], [-1794668439335586383, 303513654001005, 418852369058852, 549537646962292, 6487665092076335672]),
        ];
        for (window, samples, expected) in cases {
            let mut wm = WindowedMedian::<i64>::new(window).unwrap();
            for &x in samples {
                wm.update(x);
            }
            for (q, want) in RANDOM_QS.into_iter().zip(expected) {
                assert_eq!(wm.quantile(q), Some(want), "window {window} q {q}");
            }
        }
    }

    /// SciPy's `median_abs_deviation` (1.18.1) on windows with infinities.
    #[test]
    fn mad_is_nan_when_the_median_is_not_finite() {
        let cases: [(&[f64], f64); 6] = [
            (&[1.0, f64::INFINITY, f64::INFINITY], f64::NAN),
            (&[1.0, 2.0, f64::INFINITY, f64::INFINITY], f64::NAN),
            (&[f64::NEG_INFINITY, f64::NEG_INFINITY, 3.0], f64::NAN),
            (&[f64::NEG_INFINITY, f64::INFINITY], f64::NAN),
            (&[f64::NEG_INFINITY, 0.0, f64::INFINITY], f64::INFINITY),
            (&[1.0, 2.0, f64::INFINITY], 1.0),
        ];
        for (window, scipy) in cases {
            let mut wm = WindowedMedian::<f64>::new(window.len()).unwrap();
            for &x in window {
                wm.update(x);
            }
            let mad = wm.mad().unwrap();
            assert!(
                mad == scipy || (mad.is_nan() && scipy.is_nan()),
                "{window:?}: {mad}"
            );
        }
        let mut wm = WindowedMedian::<f64>::new(3).unwrap();
        for x in [1.0, f64::INFINITY, f64::INFINITY] {
            wm.update(x);
        }
        assert!(wm.modified_z_score(1.0).is_some_and(f64::is_nan));
    }

    #[test]
    fn checked_update_reports_nan_and_takes_infinity() {
        use nexus_stats_core::DataError;
        let mut wm = WindowedMedian::<f64>::new(3).unwrap();
        assert_eq!(wm.checked_update(2.0), Ok(Some(2.0)));
        assert_eq!(wm.checked_update(f64::NAN), Err(DataError::NotANumber));
        assert_eq!(wm.count(), 1);
        assert_eq!(wm.checked_update(f64::INFINITY), Ok(Some(f64::INFINITY)));
        assert_eq!(wm.count(), 2);
        let mut wi = WindowedMedian::<i64>::new(3).unwrap();
        assert_eq!(wi.checked_update(-4), Ok(Some(-4)));
    }

    #[test]
    fn one_sample_is_every_quantile() {
        let mut wi = WindowedMedian::<i64>::new(8).unwrap();
        assert!(wi.quartiles().is_none());
        assert_eq!(wi.update(-7), Some(-7));
        let q = wi.quartiles().unwrap();
        assert_eq!((q.q1, q.median, q.q3, q.iqr()), (-7, -7, -7, 0));
    }

    #[test]
    fn integer_median_and_quantile_agree_on_negative_ties() {
        let mut wi = WindowedMedian::<i64>::new(2).unwrap();
        for (a, b) in [(-3, 0), (-2, -1), (1, 2), (i64::MIN, i64::MAX)] {
            wi.update(a);
            wi.update(b);
            assert_eq!(wi.quantile(0.5), wi.median(), "{a} {b}");
            assert_eq!(wi.median(), Some(i64::midpoint(a, b)));
        }
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
                wm.update(x as f64);
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
            wm.update(x);
        }
        // Evicts 1.0; 3.0 sits before 5.0, i.e. in slot 0 where 1.0 was.
        wm.update(3.0);
        assert_eq!(wm.median(), Some(5.0));
        assert_eq!(wm.quantile(0.0), Some(3.0));
        // Evicts 5.0; 4.0 sits after 3.0, i.e. in slot 1 where 5.0 was.
        wm.update(4.0);
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
                    w.update(x);
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
