use alloc::boxed::Box;
use alloc::vec;
use nexus_stats_core::math::MulAdd;
use nexus_stats_core::math::{axpy, dot};

/// Recursive Least Squares adaptive filter.
///
/// Tracks linear relationships between feature vectors and a scalar
/// target using a recursive update of the covariance matrix. Converges
/// faster than LMS at the cost of O(d²) per update. The forgetting
/// factor controls how quickly old observations are downweighted.
///
/// # Use Cases
/// - Online linear regression with fast convergence
/// - System identification with non-stationary parameters
/// - Adaptive noise cancellation
///
/// # Complexity
/// O(d²) per update, heap-allocated weight vector and covariance matrix.
#[derive(Debug, Clone)]
pub struct RlsFilter {
    weights: Box<[f64]>,
    p_matrix: Box<[f64]>,
    scratch_px: Box<[f64]>,
    scratch_k: Box<[f64]>,
    forgetting_factor: f64,
    initial_covariance: f64,
    max_covariance: Option<f64>,
    dims: usize,
    count: u64,
}

/// Builder for [`RlsFilter`].
#[derive(Debug, Clone)]
pub struct RlsFilterBuilder {
    dimensions: Option<usize>,
    forgetting_factor: f64,
    initial_covariance: f64,
    max_covariance: Option<f64>,
}

impl RlsFilter {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> RlsFilterBuilder {
        RlsFilterBuilder {
            dimensions: None,
            forgetting_factor: 1.0,
            initial_covariance: 1000.0,
            max_covariance: None,
        }
    }

    /// Computes the dot product w·x (predicted output).
    ///
    /// # Panics
    /// Panics if `features.len() != self.dimensions()`.
    #[inline]
    #[must_use]
    pub fn predict(&self, features: &[f64]) -> f64 {
        assert_eq!(
            features.len(),
            self.dims,
            "feature length {} != dimensions {}",
            features.len(),
            self.dims,
        );
        dot(features, &self.weights)
    }

    /// Updates weights using the Sherman-Morrison rank-1 update.
    ///
    /// Computes the Kalman gain, updates weights by the prediction
    /// error, and updates the inverse covariance matrix.
    ///
    /// # Panics
    /// Panics if `features.len() != self.dimensions()`.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the target is NaN, or
    /// `DataError::Infinite` if the target is infinite.
    #[inline]
    pub fn update(
        &mut self,
        features: &[f64],
        target: f64,
    ) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(target);
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
        let d = self.dims;
        let lambda = self.forgetting_factor;

        // px = P·x, one fused dot per row.
        for (px, row) in self
            .scratch_px
            .iter_mut()
            .zip(self.p_matrix.chunks_exact(d))
        {
            *px = dot(features, row);
        }
        let xpx = dot(features, &self.scratch_px);

        // k[i] = px[i] / (lambda + xpx). P is positive-definite, so the
        // denominator is at least lambda; anything else means P has degraded
        // (or a NaN got in): restore P and skip the step rather than apply a
        // fabricated gain.
        let denom = lambda + xpx;
        if !nexus_stats_core::math::positive_finite(denom) {
            self.reset_covariance();
            return Ok(());
        }
        // Reciprocal: one division outside the loop instead of d inside.
        let inv_denom = 1.0 / denom;
        for (k, &px) in self.scratch_k.iter_mut().zip(&self.scratch_px) {
            *k = px * inv_denom;
        }

        // w += k · (target − w·x)
        let error = target - dot(features, &self.weights);
        axpy(error, &self.scratch_k, &mut self.weights);

        // P ← (P − k·pxᵀ) / λ, row by row; one division outside the d² loop.
        let inv_lambda = 1.0 / lambda;
        for (row, &ki) in self.p_matrix.chunks_exact_mut(d).zip(&self.scratch_k) {
            for (p, &pxj) in row.iter_mut().zip(&self.scratch_px) {
                *p = (-ki).fma(pxj, *p) * inv_lambda;
            }
        }

        self.count += 1;

        if let Some(max) = self.max_covariance {
            // The diagonal is every (d + 1)-th element of the row-major matrix.
            let max_diag = self
                .p_matrix
                .iter()
                .step_by(d + 1)
                .fold(0.0, |m, &diag| if diag > m { diag } else { m });
            if max_diag > max {
                self.reset_covariance();
            }
        }

        Ok(())
    }

    #[cold]
    fn reset_covariance(&mut self) {
        let d = self.dims;
        for p in &mut *self.p_matrix {
            *p = 0.0;
        }
        for i in 0..d {
            self.p_matrix[i * d + i] = self.initial_covariance;
        }
    }

    /// Returns the current weight vector.
    #[inline]
    #[must_use]
    pub fn weights(&self) -> &[f64] {
        &self.weights
    }

    /// Returns the number of dimensions.
    #[inline]
    #[must_use]
    pub fn dimensions(&self) -> usize {
        self.dims
    }

    /// Returns the forgetting factor.
    #[inline]
    #[must_use]
    pub fn forgetting_factor(&self) -> f64 {
        self.forgetting_factor
    }

    /// Returns the number of updates performed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Returns the P matrix, d×d row-major: the parameter covariance estimate
    /// (`p[i * d + i]` is the variance of weight `i`).
    #[inline]
    #[must_use]
    pub fn covariance(&self) -> &[f64] {
        &self.p_matrix
    }

    /// Whether any updates have been performed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Zeros weights and resets covariance to initial state.
    #[inline]
    pub fn reset(&mut self) {
        self.weights.fill(0.0);
        self.scratch_px.fill(0.0);
        self.scratch_k.fill(0.0);
        let d = self.dims;
        let delta = self.initial_covariance;
        for i in 0..d {
            for j in 0..d {
                self.p_matrix[i * d + j] = if i == j { delta } else { 0.0 };
            }
        }
        self.count = 0;
    }
}

impl RlsFilterBuilder {
    /// Sets the number of input dimensions (required, >= 1).
    #[inline]
    #[must_use]
    pub fn dimensions(mut self, dims: usize) -> Self {
        self.dimensions = Some(dims);
        self
    }

    /// Sets the forgetting factor (default 1.0, must be in (0, 1]).
    ///
    /// Values less than 1.0 downweight older observations exponentially.
    /// A value of 1.0 gives equal weight to all observations (standard RLS).
    #[inline]
    #[must_use]
    pub fn forgetting_factor(mut self, lambda: f64) -> Self {
        self.forgetting_factor = lambda;
        self
    }

    /// Sets the initial covariance diagonal (default 1000.0, must be > 0).
    ///
    /// The initial covariance matrix P is set to `delta * I`.
    /// Larger values mean less confidence in initial weights.
    #[inline]
    #[must_use]
    pub fn initial_covariance(mut self, delta: f64) -> Self {
        self.initial_covariance = delta;
        self
    }

    /// Maximum allowed diagonal covariance before auto-reset.
    ///
    /// When the largest P diagonal exceeds this threshold, P is reset
    /// to `initial_covariance × I`. Prevents divergence in long-running
    /// filters with forgetting factor < 1.0.
    #[inline]
    #[must_use]
    pub fn max_covariance(mut self, threshold: f64) -> Self {
        self.max_covariance = Some(threshold);
        self
    }

    /// Builds the filter. Returns an error if parameters are missing or invalid.
    #[inline]
    pub fn build(self) -> Result<RlsFilter, nexus_stats_core::ConfigError> {
        let dims = self
            .dimensions
            .ok_or(nexus_stats_core::ConfigError::Missing("dimensions"))?;
        let lambda = self.forgetting_factor;
        let delta = self.initial_covariance;

        if dims < 1 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "dimensions must be >= 1",
            ));
        }
        if !(lambda > 0.0 && lambda <= 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "forgetting_factor must be in (0, 1]",
            ));
        }
        if !nexus_stats_core::math::positive_finite(delta) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "initial_covariance must be positive",
            ));
        }
        if let Some(max) = self.max_covariance
            && (!nexus_stats_core::math::positive_finite(max) || max <= delta)
        {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "max_covariance must be finite and greater than initial_covariance",
            ));
        }

        // Initialize P = delta * I
        let mut p = vec![0.0; dims * dims].into_boxed_slice();
        for i in 0..dims {
            p[i * dims + i] = delta;
        }

        Ok(RlsFilter {
            weights: vec![0.0; dims].into_boxed_slice(),
            p_matrix: p,
            scratch_px: vec![0.0; dims].into_boxed_slice(),
            scratch_k: vec![0.0; dims].into_boxed_slice(),
            forgetting_factor: lambda,
            initial_covariance: delta,
            max_covariance: self.max_covariance,
            dims,
            count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn learns_linear_relationship() {
        // y = 2*x1 + 3*x2
        let mut filter = RlsFilter::builder().dimensions(2).build().unwrap();

        for i in 0..200 {
            let x1 = (i as f64 * 0.7).sin();
            let x2 = (i as f64 * 1.3).cos();
            let target = 2.0f64.mul_add(x1, 3.0 * x2);
            filter.update(&[x1, x2], target).unwrap();
        }

        let w = filter.weights();
        assert!((w[0] - 2.0).abs() < 0.01, "w[0] = {}, expected ~2.0", w[0]);
        assert!((w[1] - 3.0).abs() < 0.01, "w[1] = {}, expected ~3.0", w[1]);
    }

    #[test]
    fn forgetting_adapts_to_change() {
        let mut filter = RlsFilter::builder()
            .dimensions(1)
            .forgetting_factor(0.95)
            .build()
            .unwrap();

        // Learn y = 2*x
        for i in 0..200 {
            let x = (i as f64 * 0.5).sin();
            filter.update(&[x], 2.0 * x).unwrap();
        }

        let w_before = filter.weights()[0];
        assert!(
            (w_before - 2.0).abs() < 0.1,
            "w = {w_before}, expected ~2.0"
        );

        // Switch to y = 5*x
        for i in 0..200 {
            let x = (i as f64 * 0.5).sin();
            filter.update(&[x], 5.0 * x).unwrap();
        }

        let w_after = filter.weights()[0];
        assert!(
            (w_after - 5.0).abs() < 0.5,
            "w = {w_after}, expected ~5.0 after adaptation"
        );
    }

    #[test]
    fn covariance_decreases() {
        let mut filter = RlsFilter::builder()
            .dimensions(1)
            .initial_covariance(1000.0)
            .build()
            .unwrap();

        filter.update(&[1.0], 2.0).unwrap();
        filter.update(&[2.0], 4.0).unwrap();
        filter.update(&[3.0], 6.0).unwrap();

        // The diagonal of P should be much smaller than initial 1000.0
        // We can't access P directly, but we can verify convergence speed
        // is much faster than LMS (RLS converges in ~d samples for noiseless data).
        let w = filter.weights();
        assert!(
            (w[0] - 2.0).abs() < 0.01,
            "RLS should converge quickly, w = {}",
            w[0]
        );
    }

    #[test]
    fn predict_matches_dot_product() {
        let mut filter = RlsFilter::builder().dimensions(3).build().unwrap();

        filter.update(&[1.0, 0.0, 0.0], 5.0).unwrap();
        filter.update(&[0.0, 1.0, 0.0], 3.0).unwrap();
        filter.update(&[0.0, 0.0, 1.0], 7.0).unwrap();

        let features = [2.0, 4.0, 6.0];
        let w = filter.weights();
        let expected = w[2].mul_add(6.0, w[0].mul_add(2.0, w[1] * 4.0));
        let prediction = filter.predict(&features);
        assert!(
            (prediction - expected).abs() < 1e-12,
            "predict={prediction}, expected={expected}"
        );
    }

    #[test]
    fn reset_clears_state() {
        let mut filter = RlsFilter::builder().dimensions(2).build().unwrap();

        filter.update(&[1.0, 2.0], 5.0).unwrap();
        assert!(filter.count() > 0);
        assert!(filter.weights().iter().any(|&w| w != 0.0));

        filter.reset();
        assert_eq!(filter.count(), 0);
        assert!(filter.weights().iter().all(|&w| w == 0.0));
    }

    #[test]
    #[should_panic(expected = "feature length")]
    fn dimension_mismatch_predict() {
        let filter = RlsFilter::builder().dimensions(3).build().unwrap();

        let _ = filter.predict(&[1.0, 2.0]);
    }

    #[test]
    #[should_panic(expected = "feature length")]
    fn dimension_mismatch_update() {
        let mut filter = RlsFilter::builder().dimensions(3).build().unwrap();

        let _ = filter.update(&[1.0], 5.0);
    }

    #[test]
    fn builder_rejects_zero_dimensions() {
        let result = RlsFilter::builder().dimensions(0).build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_rejects_invalid_forgetting_factor() {
        assert!(
            RlsFilter::builder()
                .dimensions(2)
                .forgetting_factor(0.0)
                .build()
                .is_err()
        );

        assert!(
            RlsFilter::builder()
                .dimensions(2)
                .forgetting_factor(1.5)
                .build()
                .is_err()
        );

        assert!(
            RlsFilter::builder()
                .dimensions(2)
                .forgetting_factor(-0.1)
                .build()
                .is_err()
        );
    }

    #[test]
    fn builder_rejects_negative_covariance() {
        let result = RlsFilter::builder()
            .dimensions(2)
            .initial_covariance(-1.0)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn rejects_nan_target() {
        let mut filter = RlsFilter::builder().dimensions(2).build().unwrap();
        assert_eq!(
            filter.update(&[1.0, 2.0], f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(filter.count(), 0);
    }

    #[test]
    fn max_covariance_auto_resets() {
        let mut rls = RlsFilter::builder()
            .dimensions(1)
            .forgetting_factor(0.5)
            .initial_covariance(100.0)
            .max_covariance(1e6)
            .build()
            .unwrap();
        // Zero features carry no information, so each step only divides P by
        // the forgetting factor: P doubles every update and would reach
        // 100 * 2^30 ~ 1e11 without the guard.
        for _ in 0..30 {
            rls.update(&[0.0], 0.0).unwrap();
        }
        let p = rls.covariance()[0];
        assert!(
            p <= 1e6,
            "P must be reset once it passes max_covariance: {p}"
        );
        assert!(
            p >= 100.0,
            "a reset restores the initial covariance, got {p}"
        );
    }
}
