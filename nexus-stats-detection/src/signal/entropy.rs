// Shannon Entropy — Online Categorical Distribution Entropy
//
// H(X) = -Σ p_i * ln(p_i)  where p_i = count_i / total
//
// Maintains frequency counts over `bins` categories, computes entropy on query.
// O(bins) for entropy query, O(1) for update.

extern crate alloc;
use alloc::boxed::Box;
use alloc::vec;

/// Shannon entropy over a categorical distribution.
///
/// Maintains frequency counts and computes entropy on query.
/// Entropy measures how "spread out" or unpredictable a distribution
/// is — higher entropy means more uncertainty.
///
/// # Use Cases
/// - "How predictable is the distribution of order types?"
/// - "Is the venue distribution concentrating or diversifying?"
/// - Monitoring regime change via entropy shifts
///
/// # Complexity
/// - O(1) per observation, O(bins) per entropy query.
/// - Heap-allocated count vector.
///
/// # Examples
///
/// ```
/// use nexus_stats_detection::signal::Entropy;
///
/// // Uniform distribution over 4 categories → maximum entropy
/// let mut e = Entropy::builder().bins(4).build().unwrap();
/// for i in 0..400u32 { e.update(i as usize % 4); }
/// let h = e.entropy().unwrap();
/// // ln(4) ≈ 1.386
/// assert!((h - 1.386).abs() < 0.01);
/// ```
#[derive(Debug, Clone)]
pub struct Entropy {
    counts: Box<[u64]>,
    bins: usize,
    total: u64,
}

/// Builder for [`Entropy`].
#[derive(Debug, Clone)]
pub struct EntropyBuilder {
    bins: Option<usize>,
}

impl Entropy {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> EntropyBuilder {
        EntropyBuilder { bins: None }
    }

    /// Records an observation in the given category.
    ///
    /// # Panics
    ///
    /// Panics if `category >= bins`.
    #[inline]
    pub fn update(&mut self, category: usize) {
        assert!(
            category < self.bins,
            "category {category} out of range (bins={})",
            self.bins,
        );
        self.counts[category] += 1;
        self.total += 1;
    }

    /// Shannon entropy in nats (natural logarithm base), or `None` if empty.
    ///
    /// Maximum entropy for K categories is ln(K) (uniform distribution).
    /// Minimum is 0 (all observations in one category).
    #[inline]
    #[must_use]
    pub fn entropy(&self) -> Option<f64> {
        if self.total == 0 {
            return None;
        }
        let n = self.total as f64;
        let mut h = 0.0;
        for i in 0..self.bins {
            let c = self.counts[i];
            if c > 0 {
                let p = c as f64 / n;
                h -= p * nexus_stats_core::math::ln(p);
            }
        }
        Some(h)
    }

    /// Entropy in bits (log base 2), or `None` if empty.
    ///
    /// `entropy_bits = entropy / ln(2)`.
    #[inline]
    #[must_use]
    pub fn entropy_bits(&self) -> Option<f64> {
        self.entropy().map(|h| h / nexus_stats_core::math::ln(2.0))
    }

    /// Self-information of the given category: `-ln(p_i)`.
    ///
    /// High values indicate rare/surprising events.
    /// Returns `None` if empty or the category has never been observed.
    ///
    /// # Panics
    ///
    /// Panics if `category >= bins`.
    #[inline]
    #[must_use]
    pub fn surprise(&self, category: usize) -> Option<f64> {
        assert!(
            category < self.bins,
            "category {category} out of range (bins={})",
            self.bins,
        );
        if self.total == 0 || self.counts[category] == 0 {
            return None;
        }
        let p = self.counts[category] as f64 / self.total as f64;
        Some(-nexus_stats_core::math::ln(p))
    }

    /// Probability estimate for a category, or `None` if empty.
    ///
    /// # Panics
    ///
    /// Panics if `category >= bins`.
    #[inline]
    #[must_use]
    pub fn probability(&self, category: usize) -> Option<f64> {
        assert!(
            category < self.bins,
            "category {category} out of range (bins={})",
            self.bins,
        );
        if self.total == 0 {
            return None;
        }
        Some(self.counts[category] as f64 / self.total as f64)
    }

    /// Number of configured categories.
    #[inline]
    #[must_use]
    pub fn bins(&self) -> usize {
        self.bins
    }

    /// Total observations across all categories.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total
    }

    /// Whether any observations have been recorded.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.total > 0
    }

    /// Observation count for a specific category.
    ///
    /// # Panics
    ///
    /// Panics if `category >= bins`.
    #[inline]
    #[must_use]
    pub fn category_count(&self, category: usize) -> u64 {
        assert!(
            category < self.bins,
            "category {category} out of range (bins={})",
            self.bins,
        );
        self.counts[category]
    }

    /// Resets to empty state. Configuration and allocation preserved.
    #[inline]
    pub fn reset(&mut self) {
        self.counts.fill(0);
        self.total = 0;
    }
}

impl EntropyBuilder {
    /// Number of categories (required, >= 2).
    #[inline]
    #[must_use]
    pub fn bins(mut self, bins: usize) -> Self {
        self.bins = Some(bins);
        self
    }

    /// Builds the entropy tracker.
    ///
    /// # Errors
    /// Returns `ConfigError` if bins is missing or < 2.
    #[inline]
    pub fn build(self) -> Result<Entropy, nexus_stats_core::ConfigError> {
        let bins = self
            .bins
            .ok_or(nexus_stats_core::ConfigError::Missing("bins"))?;
        if bins < 2 {
            return Err(nexus_stats_core::ConfigError::Invalid("bins must be >= 2"));
        }
        Ok(Entropy {
            counts: vec![0u64; bins].into_boxed_slice(),
            bins,
            total: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uniform_entropy_equals_ln_k() {
        let mut e = Entropy::builder().bins(4).build().unwrap();
        for i in 0..4000u32 {
            e.update(i as usize % 4);
        }
        let h = e.entropy().unwrap();
        let expected = (4.0_f64).ln();
        assert!(
            (h - expected).abs() < 1e-10,
            "uniform entropy should be ln(4)={expected}, got {h}"
        );
    }

    #[test]
    fn concentrated_entropy_zero() {
        let mut e = Entropy::builder().bins(4).build().unwrap();
        for _ in 0..1000 {
            e.update(0);
        }
        let h = e.entropy().unwrap();
        assert!(h.abs() < 1e-10, "concentrated entropy should be 0, got {h}");
    }

    #[test]
    fn binary_50_50() {
        let mut e = Entropy::builder().bins(2).build().unwrap();
        for i in 0..2000u32 {
            e.update(i as usize % 2);
        }
        let h = e.entropy().unwrap();
        let expected = (2.0_f64).ln();
        assert!(
            (h - expected).abs() < 1e-10,
            "50/50 binary entropy should be ln(2)={expected}, got {h}"
        );
    }

    #[test]
    fn entropy_bits_conversion() {
        let mut e = Entropy::builder().bins(2).build().unwrap();
        for i in 0..2000u32 {
            e.update(i as usize % 2);
        }
        let h_bits = e.entropy_bits().unwrap();
        assert!(
            (h_bits - 1.0).abs() < 1e-10,
            "50/50 binary entropy should be 1 bit, got {h_bits}"
        );
    }

    #[test]
    fn surprise_rare_vs_common() {
        let mut e = Entropy::builder().bins(2).build().unwrap();
        for _ in 0..990 {
            e.update(0);
        }
        for _ in 0..10 {
            e.update(1);
        }
        let s_common = e.surprise(0).unwrap();
        let s_rare = e.surprise(1).unwrap();
        assert!(
            s_rare > s_common,
            "rare should be more surprising: common={s_common}, rare={s_rare}"
        );
    }

    #[test]
    fn surprise_unobserved_returns_none() {
        let mut e = Entropy::builder().bins(4).build().unwrap();
        e.update(0);
        assert!(e.surprise(1).is_none());
    }

    #[test]
    fn probability_matches_counts() {
        let mut e = Entropy::builder().bins(3).build().unwrap();
        for _ in 0..30 {
            e.update(0);
        }
        for _ in 0..50 {
            e.update(1);
        }
        for _ in 0..20 {
            e.update(2);
        }
        assert!((e.probability(0).unwrap() - 0.3).abs() < 1e-10);
        assert!((e.probability(1).unwrap() - 0.5).abs() < 1e-10);
        assert!((e.probability(2).unwrap() - 0.2).abs() < 1e-10);
    }

    #[test]
    fn empty_returns_none() {
        let e = Entropy::builder().bins(4).build().unwrap();
        assert!(e.entropy().is_none());
        assert!(e.entropy_bits().is_none());
        assert!(e.probability(0).is_none());
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn observe_out_of_range_panics() {
        let mut e = Entropy::builder().bins(4).build().unwrap();
        e.update(4);
    }

    #[test]
    fn category_count_tracks() {
        let mut e = Entropy::builder().bins(3).build().unwrap();
        e.update(0);
        e.update(0);
        e.update(1);
        assert_eq!(e.category_count(0), 2);
        assert_eq!(e.category_count(1), 1);
        assert_eq!(e.category_count(2), 0);
        assert_eq!(e.count(), 3);
    }

    #[test]
    fn bins_accessor() {
        let e = Entropy::builder().bins(8).build().unwrap();
        assert_eq!(e.bins(), 8);
    }

    #[test]
    fn reset_clears_state() {
        let mut e = Entropy::builder().bins(4).build().unwrap();
        for i in 0..100 {
            e.update(i % 4);
        }
        e.reset();
        assert_eq!(e.count(), 0);
        assert!(e.entropy().is_none());
    }

    #[test]
    fn builder_requires_bins() {
        let result = Entropy::builder().build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("bins"))
        ));
    }

    #[test]
    fn builder_rejects_one_bin() {
        let result = Entropy::builder().bins(1).build();
        assert!(result.is_err());
    }
}
