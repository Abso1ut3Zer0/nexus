// neg_cmp_op_on_partial_ord: !nexus_stats_core::math::positive_finite(x) intentionally rejects NaN.

// Online K-Means Clustering
//
// Mini-batch-free online variant: each observation updates the nearest
// centroid via a fixed learning rate. First k observations seed centroids.
//
// No F32 variant — squared-distance accumulation benefits from f64 precision.
// F32 distances drift noticeably for dims > ~20 or when cluster centroids
// are far apart.

use alloc::boxed::Box;
use alloc::vec;

/// Online k-means clustering with fixed learning rate.
///
/// Maintains `k` centroids in `d`-dimensional space. Each call to
/// [`update`](Self::update) assigns the observation to the nearest
/// centroid and nudges that centroid toward the observation.
///
/// The first `k` observations seed the centroids (one per cluster in
/// order). Normal learning-rate updates begin after seeding completes.
///
/// # Use Cases
/// - Streaming cluster assignment for market regimes
/// - Online segmentation of high-dimensional feature vectors
/// - Lightweight anomaly detection (distance to nearest centroid)
///
/// # Complexity
/// O(k × d) per update.
#[derive(Debug, Clone)]
pub struct OnlineKMeans {
    centroids: Box<[f64]>,
    counts: Box<[u64]>,
    k: usize,
    dims: usize,
    learning_rate: f64,
    seeded: usize,
}

/// Builder for [`OnlineKMeans`].
#[derive(Debug, Clone)]
pub struct OnlineKMeansBuilder {
    clusters: Option<usize>,
    dimensions: Option<usize>,
    learning_rate: Option<f64>,
}

impl OnlineKMeans {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> OnlineKMeansBuilder {
        OnlineKMeansBuilder {
            clusters: Option::None,
            dimensions: Option::None,
            learning_rate: Option::None,
        }
    }

    /// Assigns the observation to the nearest centroid and updates it.
    ///
    /// During the seeding phase (first `k` observations), each point
    /// becomes the initial centroid for the next unseeded cluster.
    /// After seeding, the nearest centroid is nudged toward the
    /// observation by `learning_rate`.
    ///
    /// Returns the assigned cluster index.
    ///
    /// # Panics
    /// Panics if `features.len() != self.dimensions()`.
    #[inline]
    pub fn update(&mut self, features: &[f64]) -> usize {
        debug_assert!(
            features.iter().all(|f| f.is_finite()),
            "features must be finite"
        );
        assert_eq!(
            features.len(),
            self.dims,
            "feature length {} != dimensions {}",
            features.len(),
            self.dims,
        );

        // Seeding phase: assign one point per centroid in order.
        if self.seeded < self.k {
            let cluster = self.seeded;
            let start = cluster * self.dims;
            self.centroids[start..start + self.dims].copy_from_slice(features);
            self.counts[cluster] = 1;
            self.seeded += 1;
            return cluster;
        }

        let cluster = self.nearest(features);
        self.counts[cluster] += 1;

        let start = cluster * self.dims;
        let lr = self.learning_rate;
        for i in 0..self.dims {
            self.centroids[start + i] += lr * (features[i] - self.centroids[start + i]);
        }

        cluster
    }

    /// Returns the nearest centroid index without mutating state.
    ///
    /// # Panics
    /// - Panics if `features.len() != self.dimensions()`.
    /// - Panics if not fully seeded (fewer than `k` observations have
    ///   been provided via [`update`](Self::update)).
    #[inline]
    #[must_use]
    pub fn classify(&self, features: &[f64]) -> usize {
        assert_eq!(
            features.len(),
            self.dims,
            "feature length {} != dimensions {}",
            features.len(),
            self.dims,
        );
        assert!(
            self.seeded >= self.k,
            "cannot classify before seeding is complete ({}/{} seeded)",
            self.seeded,
            self.k,
        );
        self.nearest(features)
    }

    /// Returns all centroids as a flat `k × d` slice (row-major).
    #[inline]
    #[must_use]
    pub fn centroids(&self) -> &[f64] {
        &self.centroids
    }

    /// Returns the centroid for the given cluster.
    ///
    /// # Panics
    /// Panics if `cluster >= self.clusters()`.
    #[inline]
    #[must_use]
    pub fn centroid(&self, cluster: usize) -> &[f64] {
        assert!(
            cluster < self.k,
            "cluster index {cluster} out of range (k={})",
            self.k,
        );
        let start = cluster * self.dims;
        &self.centroids[start..start + self.dims]
    }

    /// Returns the observation count for the given cluster.
    ///
    /// # Panics
    /// Panics if `cluster >= self.clusters()`.
    #[inline]
    #[must_use]
    pub fn cluster_count(&self, cluster: usize) -> u64 {
        assert!(
            cluster < self.k,
            "cluster index {cluster} out of range (k={})",
            self.k,
        );
        self.counts[cluster]
    }

    /// Returns the number of clusters (`k`).
    #[inline]
    #[must_use]
    pub fn clusters(&self) -> usize {
        self.k
    }

    /// Returns the number of dimensions (`d`).
    #[inline]
    #[must_use]
    pub fn dimensions(&self) -> usize {
        self.dims
    }

    /// Returns `true` once all `k` centroids have been seeded.
    #[inline]
    #[must_use]
    pub fn is_seeded(&self) -> bool {
        self.seeded >= self.k
    }

    /// Whether enough data for meaningful queries (all centroids seeded).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.is_seeded()
    }

    /// Returns the total observation count across all clusters.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        let mut total = 0u64;
        for &c in &*self.counts {
            total += c;
        }
        total
    }

    /// Resets all centroids to zero, clears counts, and restarts seeding.
    #[inline]
    pub fn reset(&mut self) {
        self.centroids.fill(0.0);
        self.counts.fill(0);
        self.seeded = 0;
    }

    /// Finds the index of the nearest centroid by squared Euclidean distance.
    #[inline]
    fn nearest(&self, features: &[f64]) -> usize {
        let mut best = 0;
        let mut best_dist = f64::MAX;
        for c in 0..self.k {
            let start = c * self.dims;
            let dist = sq_dist(features, &self.centroids[start..start + self.dims]);
            if dist < best_dist {
                best_dist = dist;
                best = c;
            }
        }
        best
    }
}

/// Squared Euclidean distance between two equal-length slices.
#[inline]
fn sq_dist(a: &[f64], b: &[f64]) -> f64 {
    let mut sum = 0.0;
    for i in 0..a.len() {
        let d = a[i] - b[i];
        sum += d * d;
    }
    sum
}

impl OnlineKMeansBuilder {
    /// Sets the number of clusters (required, >= 2).
    #[inline]
    #[must_use]
    pub fn clusters(mut self, k: usize) -> Self {
        self.clusters = Option::Some(k);
        self
    }

    /// Sets the number of input dimensions (required, >= 1).
    #[inline]
    #[must_use]
    pub fn dimensions(mut self, dims: usize) -> Self {
        self.dimensions = Option::Some(dims);
        self
    }

    /// Sets the learning rate (required, > 0).
    #[inline]
    #[must_use]
    pub fn learning_rate(mut self, lr: f64) -> Self {
        self.learning_rate = Option::Some(lr);
        self
    }

    /// Builds the clusterer. Returns an error if parameters are missing or invalid.
    ///
    /// # Errors
    ///
    /// - All three parameters (`clusters`, `dimensions`, `learning_rate`) are required.
    /// - `clusters` must be >= 2.
    /// - `dimensions` must be >= 1.
    /// - `learning_rate` must be > 0.
    #[inline]
    pub fn build(self) -> Result<OnlineKMeans, nexus_stats_core::ConfigError> {
        let k = self
            .clusters
            .ok_or(nexus_stats_core::ConfigError::Missing("clusters"))?;
        let dims = self
            .dimensions
            .ok_or(nexus_stats_core::ConfigError::Missing("dimensions"))?;
        let lr = self
            .learning_rate
            .ok_or(nexus_stats_core::ConfigError::Missing("learning_rate"))?;

        if k < 2 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "clusters must be >= 2",
            ));
        }
        if dims < 1 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "dimensions must be >= 1",
            ));
        }
        if !nexus_stats_core::math::positive_finite(lr) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "learning_rate must be positive",
            ));
        }

        Ok(OnlineKMeans {
            centroids: vec![0.0; k * dims].into_boxed_slice(),
            counts: vec![0u64; k].into_boxed_slice(),
            k,
            dims,
            learning_rate: lr,
            seeded: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make(k: usize, dims: usize, lr: f64) -> OnlineKMeans {
        OnlineKMeans::builder()
            .clusters(k)
            .dimensions(dims)
            .learning_rate(lr)
            .build()
            .unwrap()
    }

    #[test]
    fn two_well_separated_clusters() {
        let mut km = make(2, 2, 0.05);

        // Feed 100 points near (0, 0) and 100 near (10, 10).
        for i in 0..200 {
            let offset = (i as f64) * 0.001;
            if i % 2 == 0 {
                km.update(&[0.0 + offset, 0.0 + offset]);
            } else {
                km.update(&[10.0 + offset, 10.0 + offset]);
            }
        }

        assert!(km.is_seeded());

        // Each centroid should be near its cluster center.
        let c0 = km.centroid(0);
        let c1 = km.centroid(1);

        // Determine which centroid ended up near which center.
        let (low, high) = if c0[0] < c1[0] { (c0, c1) } else { (c1, c0) };

        assert!(low[0] < 2.0, "low centroid x={}", low[0]);
        assert!(low[1] < 2.0, "low centroid y={}", low[1]);
        assert!(high[0] > 8.0, "high centroid x={}", high[0]);
        assert!(high[1] > 8.0, "high centroid y={}", high[1]);

        // Classify should assign correctly.
        let near_origin = km.classify(&[0.5, 0.5]);
        let near_ten = km.classify(&[9.5, 9.5]);
        assert_ne!(near_origin, near_ten);
    }

    #[test]
    fn classify_does_not_mutate() {
        let mut km = make(2, 2, 0.1);
        km.update(&[0.0, 0.0]);
        km.update(&[10.0, 10.0]);

        let centroids_before = km.centroids().to_vec();
        let count_before = km.count();

        let _ = km.classify(&[5.0, 5.0]);

        assert_eq!(km.centroids(), &centroids_before[..]);
        assert_eq!(km.count(), count_before);
    }

    #[test]
    fn centroid_seeding() {
        let mut km = make(3, 2, 0.01);

        assert!(!km.is_seeded());

        // First 3 observations seed centroids directly.
        assert_eq!(km.update(&[1.0, 2.0]), 0);
        assert_eq!(km.update(&[3.0, 4.0]), 1);
        assert!(!km.is_seeded());
        assert_eq!(km.update(&[5.0, 6.0]), 2);
        assert!(km.is_seeded());

        assert_eq!(km.centroid(0), &[1.0, 2.0]);
        assert_eq!(km.centroid(1), &[3.0, 4.0]);
        assert_eq!(km.centroid(2), &[5.0, 6.0]);
    }

    #[test]
    fn reset_clears_state() {
        let mut km = make(2, 2, 0.1);
        km.update(&[1.0, 2.0]);
        km.update(&[3.0, 4.0]);
        km.update(&[5.0, 6.0]);

        km.reset();

        assert!(!km.is_seeded());
        assert_eq!(km.count(), 0);
        assert_eq!(km.centroids(), &[0.0; 4][..]);
    }

    #[test]
    #[should_panic(expected = "feature length")]
    fn dimension_mismatch_panics() {
        let mut km = make(2, 3, 0.1);
        km.update(&[1.0, 2.0]); // 2 != 3
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn cluster_out_of_range_panics() {
        let km = make(2, 2, 0.1);
        let _ = km.centroid(2); // k=2, valid indices are 0 and 1
    }

    #[test]
    fn builder_validation() {
        // clusters < 2
        let err = OnlineKMeans::builder()
            .clusters(1)
            .dimensions(2)
            .learning_rate(0.1)
            .build();
        assert!(err.is_err());

        // dimensions 0
        let err = OnlineKMeans::builder()
            .clusters(2)
            .dimensions(0)
            .learning_rate(0.1)
            .build();
        assert!(err.is_err());

        // negative learning rate
        let err = OnlineKMeans::builder()
            .clusters(2)
            .dimensions(2)
            .learning_rate(-0.01)
            .build();
        assert!(err.is_err());

        // zero learning rate
        let err = OnlineKMeans::builder()
            .clusters(2)
            .dimensions(2)
            .learning_rate(0.0)
            .build();
        assert!(err.is_err());

        // missing required field
        let err = OnlineKMeans::builder().clusters(2).dimensions(2).build();
        assert!(err.is_err());
    }

    #[test]
    fn count_tracks_total() {
        let mut km = make(2, 2, 0.1);

        assert_eq!(km.count(), 0);

        km.update(&[0.0, 0.0]);
        km.update(&[10.0, 10.0]);
        assert_eq!(km.count(), 2);

        // Further updates increment counts.
        km.update(&[0.1, 0.1]);
        km.update(&[9.9, 9.9]);
        km.update(&[0.2, 0.2]);
        assert_eq!(km.count(), 5);

        // Sum of per-cluster counts matches total.
        let sum: u64 = (0..km.clusters()).map(|c| km.cluster_count(c)).sum();
        assert_eq!(sum, km.count());
    }
}
