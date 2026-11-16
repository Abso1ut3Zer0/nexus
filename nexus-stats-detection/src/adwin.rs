extern crate alloc;
use alloc::boxed::Box;
use alloc::collections::VecDeque;
use nexus_stats_core::DataError;

#[derive(Debug, Clone, Copy)]
struct Bucket {
    total: f64,
    count: u64,
}

/// Levels of the exponential histogram: level `k` holds buckets of `2^k`
/// samples. A `u64` sample count never needs more than 64 levels, and a level
/// never holds more than `max_buckets + 1` buckets (`compress` merges two as
/// soon as it does), so the whole structure is allocated once at build and
/// never touches the allocator again.
const MAX_LEVELS: usize = u64::BITS as usize;

#[derive(Debug, Clone)]
struct BucketList {
    /// `levels[k]`, front = oldest. Only `levels[..top]` can be non-empty.
    levels: Box<[VecDeque<Bucket>]>,
    top: usize,
    max_buckets: usize,
}

impl BucketList {
    fn new(max_buckets: usize) -> Self {
        Self {
            levels: (0..MAX_LEVELS)
                .map(|_| VecDeque::with_capacity(max_buckets + 1))
                .collect(),
            top: 1,
            max_buckets,
        }
    }

    fn insert(&mut self, value: f64) {
        self.levels[0].push_back(Bucket {
            total: value,
            count: 1,
        });
        self.compress();
    }

    /// Carry: while a level holds more than `max_buckets`, its two oldest
    /// buckets merge into one bucket of the next level. Each level is visited
    /// at most once per insert.
    fn compress(&mut self) {
        let mut level = 0;
        while level + 1 < MAX_LEVELS && self.levels[level].len() > self.max_buckets {
            // `len > max_buckets >= 2`, so both pops succeed.
            let (Some(b2), Some(b1)) = (
                self.levels[level].pop_front(),
                self.levels[level].pop_front(),
            ) else {
                break;
            };
            let merged = Bucket {
                total: b1.total + b2.total,
                count: b1.count + b2.count,
            };
            level += 1;
            if level == self.top {
                self.top += 1;
            }
            self.levels[level].push_back(merged);
        }
    }

    /// Removes and returns the oldest bucket: the front of the highest
    /// non-empty level.
    fn drop_oldest(&mut self) -> Option<Bucket> {
        self.levels[..self.top]
            .iter_mut()
            .rev()
            .find_map(VecDeque::pop_front)
    }

    /// Buckets from oldest to newest.
    fn iter_oldest_first(&self) -> impl Iterator<Item = &Bucket> {
        self.levels[..self.top]
            .iter()
            .rev()
            .flat_map(VecDeque::iter)
    }

    fn reset(&mut self) {
        for level in &mut self.levels[..self.top] {
            level.clear();
        }
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
/// buckets on a cut). Memory is fixed at build: 64 levels of
/// `max_buckets + 1` buckets.
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
///     assert!(!ad.update(5.0).unwrap());
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
    pub fn update(&mut self, sample: f64) -> Result<bool, DataError> {
        check_finite!(sample);
        self.count += 1;
        self.width += 1;

        self.buckets.insert(sample);
        self.total += sample;

        if !self.is_primed() {
            return Ok(false);
        }

        Ok(self.check_and_shrink())
    }

    fn check_and_shrink(&mut self) -> bool {
        let mut changed = false;

        while self.width > 2 {
            let mut n0: u64 = 0;
            let mut sum0: f64 = 0.0;
            let mut found_cut = false;

            for b in self.buckets.iter_oldest_first() {
                n0 += b.count;
                sum0 += b.total;

                let n1 = self.width - n0;
                if n1 == 0 {
                    break;
                }

                let sum1 = self.total - sum0;
                let mean0 = sum0 / n0 as f64;
                let mean1 = sum1 / n1 as f64;
                let diff = (mean0 - mean1).abs();

                let m = 1.0 / n0 as f64 + 1.0 / n1 as f64;
                let eps = nexus_stats_core::math::sqrt(0.5 * m * self.ln_4_over_delta);

                if diff >= eps {
                    found_cut = true;
                    break;
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
            self.total = self.buckets.iter_oldest_first().map(|b| b.total).sum();
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
            assert!(!ad.update(10.0).unwrap());
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
            if ad.update(5.0).unwrap() {
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
            if ad.update(10.0).unwrap() {
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
            if sensitive.update(2.0).unwrap() && sensitive_fired == 0 {
                sensitive_fired = sensitive.count();
            }
            if conservative.update(2.0).unwrap() && conservative_fired == 0 {
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
