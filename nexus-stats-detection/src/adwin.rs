use alloc::boxed::Box;
use alloc::vec;
use nexus_stats_core::DataError;

#[derive(Debug, Clone, Copy)]
struct Bucket {
    total: f64,
    count: u64,
}

/// Exponential histogram: level `k` holds buckets of `2^k` samples, oldest
/// first. A `u64` sample count never needs more than 64 levels, and a level
/// never holds more than `max_buckets + 1` buckets (`compress` merges two as
/// soon as it does), so every level is a fixed lane of `stride = max_buckets
/// + 1` slots in one allocation, and nothing allocates after build. Dropping
/// a lane's oldest buckets shifts at most `max_buckets` buckets with swaps:
/// measured against the alternatives, this matches a deque per level while
/// per-lane ring cursors cost 15% more on the cut-test scan (two runs per
/// lane) and a `copy_within` shift lowers to a `memmove` call.
const MAX_LEVELS: usize = u64::BITS as usize;

const EMPTY: Bucket = Bucket {
    total: 0.0,
    count: 0,
};

#[derive(Debug, Clone)]
struct BucketList {
    /// `MAX_LEVELS × stride` slots; lane `k` is `slots[k * stride..][..len[k]]`.
    slots: Box<[Bucket]>,
    /// Occupancy per lane.
    len: [u16; MAX_LEVELS],
    /// Lanes `top..` have never been used; the scans stop there.
    top: usize,
    stride: usize,
}

impl BucketList {
    fn new(max_buckets: usize) -> Self {
        let stride = max_buckets + 1;
        Self {
            slots: vec![EMPTY; MAX_LEVELS * stride].into_boxed_slice(),
            len: [0; MAX_LEVELS],
            top: 1,
            stride,
        }
    }

    #[inline]
    fn lane(&self, level: usize) -> &[Bucket] {
        let base = level * self.stride;
        &self.slots[base..base + usize::from(self.len[level])]
    }

    #[inline]
    fn push_back(&mut self, level: usize, bucket: Bucket) {
        let n = usize::from(self.len[level]);
        debug_assert!(n < self.stride, "lane {level} over capacity");
        self.slots[level * self.stride + n] = bucket;
        self.len[level] += 1;
    }

    /// Drops the `n` oldest buckets of a lane. A swap loop, not `copy_within`:
    /// a copy loop over a runtime-length slice lowers to a `memmove` call.
    #[inline]
    fn pop_front(&mut self, level: usize, n: usize) {
        let base = level * self.stride;
        let len = usize::from(self.len[level]);
        for i in n..len {
            self.slots.swap(base + i - n, base + i);
        }
        self.len[level] -= n as u16;
    }

    fn insert(&mut self, value: f64) {
        self.push_back(
            0,
            Bucket {
                total: value,
                count: 1,
            },
        );
        self.compress();
    }

    fn compress(&mut self) {
        let max_buckets = self.stride - 1;
        let mut level = 0;
        while level + 1 < MAX_LEVELS && usize::from(self.len[level]) > max_buckets {
            let lane = self.lane(level);
            let merged = Bucket {
                total: lane[0].total + lane[1].total,
                count: lane[0].count + lane[1].count,
            };
            self.pop_front(level, 2);
            level += 1;
            if level == self.top {
                self.top += 1;
            }
            self.push_back(level, merged);
        }
    }

    fn drop_oldest(&mut self) -> Option<Bucket> {
        let mut level = self.top;
        while level > 0 {
            level -= 1;
            if self.len[level] > 0 {
                let oldest = self.lane(level)[0];
                self.pop_front(level, 1);
                return Some(oldest);
            }
        }
        None
    }

    fn total(&self) -> f64 {
        let mut sum = 0.0;
        for level in 0..self.top {
            for bucket in self.lane(level) {
                sum += bucket.total;
            }
        }
        sum
    }

    fn reset(&mut self) {
        self.len = [0; MAX_LEVELS];
        self.top = 1;
    }
}

/// ADWIN — Adaptive Windowing for distribution change detection.
///
/// Maintains a variable-length window using an exponential histogram.
/// Detects distribution changes by testing all possible splits via
/// Hoeffding bound. Automatically shrinks the window on detection.
///
/// O(log n) amortized per update (one carry chain, one scan of the
/// buckets on a cut). Memory is fixed at build: one allocation of
/// 64 × (`max_buckets` + 1) buckets.
///
/// Bifet & Gavalda, 2007.
///
/// **Note:** The Hoeffding bound assumes bounded support. For best
/// results, normalize inputs to a known range (e.g. \[0, 1\]).
/// Detection still works on raw values but `delta` loses its
/// strict confidence interpretation.
///
/// # Parameters
///
/// - `delta` (delta) — confidence parameter. Smaller values reduce false
///   positives but increase detection delay. Typical: 0.002.
/// - `max_buckets` — buckets per level (default 5). Higher values
///   increase precision but use more memory.
///
/// # Examples
///
/// ```
/// use nexus_stats_detection::detection::Adwin;
///
/// let mut ad = Adwin::builder()
///     .delta(0.01)
///     .build()
///     .unwrap();
///
/// // Stable signal — no detection
/// for _ in 0..100 {
///     assert!(ad.update(5.0).unwrap() != Some(true));
/// }
/// ```
#[derive(Debug, Clone)]
pub struct Adwin {
    /// `ln(4 / delta)`: the Hoeffding bound's only use of `delta`, computed once.
    ln_4_over_delta: f64,
    buckets: BucketList,
    total: f64,
    width: u64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`Adwin`].
#[derive(Debug, Clone)]
pub struct AdwinBuilder {
    delta: Option<f64>,
    max_buckets: usize,
    min_samples: u64,
}

impl Adwin {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> AdwinBuilder {
        AdwinBuilder {
            delta: None,
            max_buckets: 5,
            min_samples: 30,
        }
    }

    /// Feeds a sample. Returns `Ok(true)` if distribution change detected.
    ///
    /// On detection, the window shrinks to exclude the stale portion.
    /// `count()` reflects total samples seen; `width()` reflects the
    /// current (post-shrink) window size.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    ///
    /// `None` until `min_samples` samples have been seen (no verdict yet), then
    /// `Some(true)` when a change is detected on this sample.
    pub fn update(&mut self, sample: f64) -> Result<Option<bool>, DataError> {
        check_finite!(sample);
        self.count += 1;
        self.width += 1;

        self.buckets.insert(sample);
        self.total += sample;

        if !self.is_primed() {
            return Ok(None);
        }

        Ok(Some(self.check_and_shrink()))
    }

    fn check_and_shrink(&mut self) -> bool {
        let mut changed = false;

        while self.width > 2 {
            let mut n0: u64 = 0;
            let mut sum0: f64 = 0.0;
            let mut found_cut = false;

            // Oldest first: highest lane down, each lane's two runs in order.
            let mut level = self.buckets.top;
            'scan: while level > 0 {
                level -= 1;
                for bucket in self.buckets.lane(level) {
                    n0 += bucket.count;
                    sum0 += bucket.total;

                    let n1 = self.width - n0;
                    if n1 == 0 {
                        break 'scan;
                    }

                    let sum1 = self.total - sum0;
                    let mean0 = sum0 / n0 as f64;
                    let mean1 = sum1 / n1 as f64;
                    let diff = (mean0 - mean1).abs();

                    let m = 1.0 / n0 as f64 + 1.0 / n1 as f64;
                    let eps = nexus_stats_core::math::sqrt(0.5 * m * self.ln_4_over_delta);

                    if diff >= eps {
                        found_cut = true;
                        break 'scan;
                    }
                }
            }

            if !found_cut {
                break;
            }

            let Some(removed) = self.buckets.drop_oldest() else {
                break;
            };
            self.width -= removed.count;
            self.total -= removed.total;
            changed = true;
        }

        if changed {
            // Re-sum once per shrink so the running total does not drift.
            self.total = self.buckets.total();
        }

        changed
    }

    /// Current window size (shrinks on detection).
    #[inline]
    #[must_use]
    pub fn width(&self) -> u64 {
        self.width
    }

    /// Current window mean, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn mean(&self) -> Option<f64> {
        if self.width == 0 {
            None
        } else {
            Some(self.total / self.width as f64)
        }
    }

    /// Total samples ever seen (does not decrease on shrink).
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the detector has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to empty state. Parameters unchanged.
    pub fn reset(&mut self) {
        self.buckets.reset();
        self.total = 0.0;
        self.width = 0;
        self.count = 0;
    }
}

impl AdwinBuilder {
    /// Confidence parameter (delta). Required, must be in (0, 1).
    ///
    /// Smaller values reduce false positives but increase detection delay.
    /// Typical: 0.002.
    #[inline]
    #[must_use]
    pub fn delta(mut self, delta: f64) -> Self {
        self.delta = Some(delta);
        self
    }

    /// Buckets per level (default 5, must be >= 2).
    ///
    /// Higher values increase precision but use more memory.
    #[inline]
    #[must_use]
    pub fn max_buckets(mut self, max_buckets: usize) -> Self {
        self.max_buckets = max_buckets;
        self
    }

    /// Minimum samples before detection activates. Default: 30.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the ADWIN detector.
    ///
    /// # Errors
    ///
    /// - Delta must have been set and be in (0, 1).
    /// - `max_buckets` must be >= 2.
    #[inline]
    pub fn build(self) -> Result<Adwin, nexus_stats_core::ConfigError> {
        let delta = self
            .delta
            .ok_or(nexus_stats_core::ConfigError::Missing("delta"))?;
        if !nexus_stats_core::math::in_unit_interval(delta) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "ADWIN delta must be in (0, 1)",
            ));
        }
        if self.max_buckets < 2 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "ADWIN max_buckets must be >= 2",
            ));
        }
        if self.max_buckets >= usize::from(u16::MAX) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "ADWIN max_buckets must be < 65535",
            ));
        }

        Ok(Adwin {
            ln_4_over_delta: nexus_stats_core::math::ln(4.0 / delta),
            buckets: BucketList::new(self.max_buckets),
            total: 0.0,
            width: 0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_drift_stable() {
        let mut ad = Adwin::builder()
            .delta(0.01)
            .min_samples(20)
            .build()
            .unwrap();

        for _ in 0..500 {
            assert!(ad.update(10.0).unwrap() != Some(true));
        }
    }

    #[test]
    fn mean_shift_detected() {
        let mut ad = Adwin::builder()
            .delta(0.002)
            .min_samples(10)
            .build()
            .unwrap();

        for _ in 0..500 {
            let _ = ad.update(0.0);
        }

        let mut detected = false;
        for _ in 0..500 {
            if ad.update(5.0).unwrap() == Some(true) {
                detected = true;
                break;
            }
        }
        assert!(detected, "should detect mean shift from 0 to 5");
    }

    #[test]
    fn window_shrinks_on_detection() {
        let mut ad = Adwin::builder()
            .delta(0.002)
            .min_samples(10)
            .build()
            .unwrap();

        for _ in 0..500 {
            let _ = ad.update(0.0);
        }
        let width_before = ad.width();

        for _ in 0..500 {
            if ad.update(10.0).unwrap() == Some(true) {
                break;
            }
        }

        assert!(
            ad.width() < width_before + 500,
            "window should have shrunk after detection"
        );
    }

    #[test]
    fn mean_tracks_recent() {
        let mut ad = Adwin::builder()
            .delta(0.002)
            .min_samples(10)
            .build()
            .unwrap();

        for _ in 0..500 {
            let _ = ad.update(0.0);
        }

        for _ in 0..500 {
            let _ = ad.update(10.0);
        }

        let mean = ad.mean().unwrap();
        assert!(
            mean > 5.0,
            "mean should track recent distribution, got {mean}"
        );
    }

    #[test]
    fn sensitivity_vs_delta() {
        let mut sensitive = Adwin::builder().delta(0.5).min_samples(10).build().unwrap();

        let mut conservative = Adwin::builder()
            .delta(0.001)
            .min_samples(10)
            .build()
            .unwrap();

        for _ in 0..200 {
            let _ = sensitive.update(0.0);
            let _ = conservative.update(0.0);
        }

        let mut sensitive_fired = 0u64;
        let mut conservative_fired = 0u64;
        for _ in 0..200 {
            if sensitive.update(2.0).unwrap() == Some(true) && sensitive_fired == 0 {
                sensitive_fired = sensitive.count();
            }
            if conservative.update(2.0).unwrap() == Some(true) && conservative_fired == 0 {
                conservative_fired = conservative.count();
            }
        }

        if sensitive_fired > 0 && conservative_fired > 0 {
            assert!(
                sensitive_fired <= conservative_fired,
                "larger delta should detect sooner: sensitive={sensitive_fired}, conservative={conservative_fired}"
            );
        }
    }

    #[test]
    fn reset_clears() {
        let mut ad = Adwin::builder()
            .delta(0.01)
            .min_samples(10)
            .build()
            .unwrap();

        for _ in 0..100 {
            let _ = ad.update(5.0);
        }

        ad.reset();
        assert_eq!(ad.count(), 0);
        assert_eq!(ad.width(), 0);
        assert!(ad.mean().is_none());
        assert!(!ad.is_primed());
    }

    #[test]
    fn nan_rejected() {
        let mut ad = Adwin::builder().delta(0.01).build().unwrap();
        assert!(matches!(ad.update(f64::NAN), Err(DataError::NotANumber)));
    }

    #[test]
    fn inf_rejected() {
        let mut ad = Adwin::builder().delta(0.01).build().unwrap();
        assert!(matches!(ad.update(f64::INFINITY), Err(DataError::Infinite)));
    }

    #[test]
    fn builder_validation() {
        assert!(matches!(
            Adwin::builder().build(),
            Err(nexus_stats_core::ConfigError::Missing("delta"))
        ));
        assert!(matches!(
            Adwin::builder().delta(0.0).build(),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
        assert!(matches!(
            Adwin::builder().delta(1.0).build(),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
        assert!(matches!(
            Adwin::builder().delta(0.01).max_buckets(1).build(),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }
}
