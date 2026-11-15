extern crate alloc;
use alloc::vec;
use alloc::vec::Vec;
use nexus_stats_core::DataError;

#[derive(Debug, Clone, Copy)]
struct Bucket {
    total: f64,
    count: u64,
}

#[derive(Debug, Clone)]
struct BucketList {
    levels: Vec<Vec<Bucket>>,
    max_buckets: usize,
}

impl BucketList {
    fn new(max_buckets: usize) -> Self {
        Self {
            levels: vec![Vec::new()],
            max_buckets,
        }
    }

    fn insert(&mut self, value: f64) {
        self.levels[0].push(Bucket {
            total: value,
            count: 1,
        });
        self.compress();
    }

    fn compress(&mut self) {
        for level in 0.. {
            if level >= self.levels.len() {
                break;
            }
            if self.levels[level].len() <= self.max_buckets {
                break;
            }

            if level + 1 >= self.levels.len() {
                self.levels.push(Vec::new());
            }

            let b2 = self.levels[level].remove(0);
            let b1 = self.levels[level].remove(0);
            let merged = Self::merge_buckets(b1, b2);
            self.levels[level + 1].push(merged);
        }
    }

    fn merge_buckets(a: Bucket, b: Bucket) -> Bucket {
        Bucket {
            total: a.total + b.total,
            count: a.count + b.count,
        }
    }

    fn drop_oldest(&mut self) -> u64 {
        for level in (0..self.levels.len()).rev() {
            if !self.levels[level].is_empty() {
                let removed = self.levels[level].remove(0);
                return removed.count;
            }
        }
        0
    }

    fn reset(&mut self) {
        self.levels.clear();
        self.levels.push(Vec::new());
    }
}

/// ADWIN — Adaptive Windowing for distribution change detection.
///
/// Maintains a variable-length window using an exponential histogram.
/// Detects distribution changes by testing all possible splits via
/// Hoeffding bound. Automatically shrinks the window on detection.
///
/// O(log n) amortized per update, O(log n) memory.
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
    delta: f64,
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

            'outer: for level in (0..self.buckets.levels.len()).rev() {
                for bi in 0..self.buckets.levels[level].len() {
                    let b = &self.buckets.levels[level][bi];
                    n0 += b.count;
                    sum0 += b.total;

                    let n1 = self.width - n0;
                    if n0 == 0 || n1 == 0 {
                        continue;
                    }

                    let sum1 = self.total - sum0;
                    let mean0 = sum0 / n0 as f64;
                    let mean1 = sum1 / n1 as f64;
                    let diff = (mean0 - mean1).abs();

                    let m = 1.0 / n0 as f64 + 1.0 / n1 as f64;
                    let dd = self.delta;
                    let eps = nexus_stats_core::math::sqrt(
                        0.5 * m * nexus_stats_core::math::ln(4.0 / dd),
                    );

                    if diff >= eps {
                        found_cut = true;
                        break 'outer;
                    }
                }
            }

            if !found_cut {
                break;
            }

            let removed = self.buckets.drop_oldest();
            if removed == 0 {
                break;
            }

            self.width -= removed;

            let new_total_f64 = {
                let mut s = 0.0_f64;
                for level in &self.buckets.levels {
                    for b in level {
                        s += b.total;
                    }
                }
                s
            };
            self.total = new_total_f64;

            changed = true;
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
        if delta <= 0.0 || delta >= 1.0 || delta.is_nan() {
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
            delta,
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
