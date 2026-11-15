// LMS and NLMS Adaptive Filters
//
// Least Mean Squares (LMS): w += lr * error * x
// Normalized LMS (NLMS):    w += (lr / (x·x + epsilon)) * error * x
//
// NLMS adapts the step size to the input power, making convergence
// less sensitive to input scaling. Both are O(dims) per update.

extern crate alloc;
use alloc::boxed::Box;
use alloc::vec;
use nexus_stats_core::math::MulAdd;

/// Least Mean Squares adaptive filter.
///
/// Learns linear relationships between feature vectors and a scalar
/// target by gradient descent on the squared error. Convergence rate
/// depends on `learning_rate` and the eigenvalue spread of the input
/// correlation matrix.
///
/// # Use Cases
/// - Online linear regression
/// - Noise cancellation
/// - System identification
///
/// # Complexity
/// O(dims) per update, heap-allocated weight vector.
#[derive(Debug, Clone)]
pub struct LmsFilter {
    weights: Box<[f64]>,
    learning_rate: f64,
    dims: usize,
    count: u64,
}

/// Builder for [`LmsFilter`].
#[derive(Debug, Clone)]
pub struct LmsFilterBuilder {
    dimensions: Option<usize>,
    learning_rate: Option<f64>,
}

impl LmsFilter {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> LmsFilterBuilder {
        LmsFilterBuilder {
            dimensions: None,
            learning_rate: None,
        }
    }

    /// Computes the dot product w·x.
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
        let mut sum = 0.0;
        for i in 0..self.dims {
            sum = self.weights[i].fma(features[i], sum);
        }
        sum
    }

    /// Updates weights: w += lr * (target - predict(features)) * features.
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
        let prediction = self.predict(features);
        let error = target - prediction;
        let step = self.learning_rate * error;
        for i in 0..self.dims {
            self.weights[i] = step.fma(features[i], self.weights[i]);
        }
        self.count += 1;
        Ok(())
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

    /// Returns the learning rate.
    #[inline]
    #[must_use]
    pub fn learning_rate(&self) -> f64 {
        self.learning_rate
    }

    /// Returns the number of updates performed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether any updates have been performed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Zeros all weights, keeping configuration intact.
    #[inline]
    pub fn reset(&mut self) {
        self.weights.fill(0.0);
        self.count = 0;
    }
}

impl LmsFilterBuilder {
    /// Sets the number of input dimensions (required, >= 1).
    #[inline]
    #[must_use]
    pub fn dimensions(mut self, dims: usize) -> Self {
        self.dimensions = Some(dims);
        self
    }

    /// Sets the learning rate (required, > 0).
    #[inline]
    #[must_use]
    pub fn learning_rate(mut self, lr: f64) -> Self {
        self.learning_rate = Some(lr);
        self
    }

    /// Builds the filter. Returns an error if parameters are missing or invalid.
    #[inline]
    pub fn build(self) -> Result<LmsFilter, nexus_stats_core::ConfigError> {
        let dims = self
            .dimensions
            .ok_or(nexus_stats_core::ConfigError::Missing("dimensions"))?;
        let lr = self
            .learning_rate
            .ok_or(nexus_stats_core::ConfigError::Missing("learning_rate"))?;
        if dims < 1 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "dimensions must be >= 1",
            ));
        }
        if lr <= 0.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "learning_rate must be positive",
            ));
        }
        Ok(LmsFilter {
            weights: vec![0.0; dims].into_boxed_slice(),
            learning_rate: lr,
            dims,
            count: 0,
        })
    }
}

/// Normalized Least Mean Squares adaptive filter.
///
/// Like LMS but normalizes the step size by input power (x·x + epsilon),
/// making convergence robust to varying input scales. The epsilon term
/// prevents division by zero when the input is near-silent.
///
/// # Use Cases
/// - Adaptive noise cancellation with varying input power
/// - Echo cancellation
/// - Channel equalization
///
/// # Complexity
/// O(dims) per update, heap-allocated weight vector.
#[derive(Debug, Clone)]
pub struct NlmsFilter {
    weights: Box<[f64]>,
    learning_rate: f64,
    epsilon: f64,
    dims: usize,
    count: u64,
}

/// Builder for [`NlmsFilter`].
#[derive(Debug, Clone)]
pub struct NlmsFilterBuilder {
    dimensions: Option<usize>,
    learning_rate: Option<f64>,
    epsilon: Option<f64>,
}

impl NlmsFilter {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> NlmsFilterBuilder {
        NlmsFilterBuilder {
            dimensions: None,
            learning_rate: None,
            epsilon: None,
        }
    }

    /// Computes the dot product w·x.
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
        let mut sum = 0.0;
        for i in 0..self.dims {
            sum = self.weights[i].fma(features[i], sum);
        }
        sum
    }

    /// Updates weights: w += (lr / (x·x + epsilon)) * (target - predict(features)) * features.
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
        let prediction = self.predict(features);
        let error = target - prediction;
        let mut norm_sq = 0.0;
        for i in 0..self.dims {
            norm_sq = features[i].fma(features[i], norm_sq);
        }
        let step = (self.learning_rate / (norm_sq + self.epsilon)) * error;
        for i in 0..self.dims {
            self.weights[i] = step.fma(features[i], self.weights[i]);
        }
        self.count += 1;
        Ok(())
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

    /// Returns the learning rate.
    #[inline]
    #[must_use]
    pub fn learning_rate(&self) -> f64 {
        self.learning_rate
    }

    /// Returns the epsilon (regularization) parameter.
    #[inline]
    #[must_use]
    pub fn epsilon(&self) -> f64 {
        self.epsilon
    }

    /// Returns the number of updates performed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether any updates have been performed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Zeros all weights, keeping configuration intact.
    #[inline]
    pub fn reset(&mut self) {
        self.weights.fill(0.0);
        self.count = 0;
    }
}

impl NlmsFilterBuilder {
    /// Sets the number of input dimensions (required, >= 1).
    #[inline]
    #[must_use]
    pub fn dimensions(mut self, dims: usize) -> Self {
        self.dimensions = Some(dims);
        self
    }

    /// Sets the learning rate (required, > 0).
    #[inline]
    #[must_use]
    pub fn learning_rate(mut self, lr: f64) -> Self {
        self.learning_rate = Some(lr);
        self
    }

    /// Sets the regularization term (default 1e-8, must be > 0).
    #[inline]
    #[must_use]
    pub fn epsilon(mut self, eps: f64) -> Self {
        self.epsilon = Some(eps);
        self
    }

    /// Builds the filter. Returns an error if parameters are missing or invalid.
    #[inline]
    pub fn build(self) -> Result<NlmsFilter, nexus_stats_core::ConfigError> {
        let dims = self
            .dimensions
            .ok_or(nexus_stats_core::ConfigError::Missing("dimensions"))?;
        let lr = self
            .learning_rate
            .ok_or(nexus_stats_core::ConfigError::Missing("learning_rate"))?;
        let eps = self.epsilon.unwrap_or(1e-8);
        if dims < 1 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "dimensions must be >= 1",
            ));
        }
        if lr <= 0.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "learning_rate must be positive",
            ));
        }
        if eps <= 0.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "epsilon must be positive",
            ));
        }
        Ok(NlmsFilter {
            weights: vec![0.0; dims].into_boxed_slice(),
            learning_rate: lr,
            epsilon: eps,
            dims,
            count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lms_learns_linear_relationship() {
        // y = 2*x1 + 3*x2
        let mut filter = LmsFilter::builder()
            .dimensions(2)
            .learning_rate(0.01)
            .build()
            .unwrap();

        for i in 0..5000 {
            let x1 = (i as f64 * 0.7).sin();
            let x2 = (i as f64 * 1.3).cos();
            let target = 2.0f64.mul_add(x1, 3.0 * x2);
            filter.update(&[x1, x2], target).unwrap();
        }

        let w = filter.weights();
        assert!((w[0] - 2.0).abs() < 0.1, "w[0] = {}, expected ~2.0", w[0]);
        assert!((w[1] - 3.0).abs() < 0.1, "w[1] = {}, expected ~3.0", w[1]);
    }

    #[test]
    fn nlms_learns_with_different_scales() {
        // y = 2*x1 + 3*x2, with x1 scaled 100x larger than x2
        let mut filter = NlmsFilter::builder()
            .dimensions(2)
            .learning_rate(0.5)
            .build()
            .unwrap();

        for i in 0..5000 {
            let x1 = 100.0 * (i as f64 * 0.7).sin();
            let x2 = (i as f64 * 1.3).cos();
            let target = 2.0f64.mul_add(x1, 3.0 * x2);
            filter.update(&[x1, x2], target).unwrap();
        }

        let w = filter.weights();
        assert!((w[0] - 2.0).abs() < 0.1, "w[0] = {}, expected ~2.0", w[0]);
        assert!((w[1] - 3.0).abs() < 0.1, "w[1] = {}, expected ~3.0", w[1]);
    }

    #[test]
    fn predict_matches_manual_dot_product() {
        let mut filter = LmsFilter::builder()
            .dimensions(3)
            .learning_rate(0.1)
            .build()
            .unwrap();

        // Train a bit so weights are non-zero
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
    fn reset_clears_weights() {
        let mut filter = LmsFilter::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        filter.update(&[1.0, 2.0], 5.0).unwrap();
        assert!(filter.count() > 0);
        assert!(filter.weights().iter().any(|&w| w != 0.0));

        filter.reset();
        assert_eq!(filter.count(), 0);
        assert!(filter.weights().iter().all(|&w| w == 0.0));
    }

    #[test]
    #[should_panic(expected = "feature length")]
    fn dimension_mismatch_panics_on_predict() {
        let filter = LmsFilter::builder()
            .dimensions(3)
            .learning_rate(0.1)
            .build()
            .unwrap();

        let _ = filter.predict(&[1.0, 2.0]);
    }

    #[test]
    #[should_panic(expected = "feature length")]
    fn dimension_mismatch_panics_on_update() {
        let mut filter = LmsFilter::builder()
            .dimensions(3)
            .learning_rate(0.1)
            .build()
            .unwrap();

        let _ = filter.update(&[1.0], 5.0);
    }

    #[test]
    fn builder_rejects_zero_dimensions() {
        let result = LmsFilter::builder()
            .dimensions(0)
            .learning_rate(0.1)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_rejects_negative_learning_rate() {
        let result = LmsFilter::builder()
            .dimensions(2)
            .learning_rate(-0.01)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn nlms_builder_rejects_negative_epsilon() {
        let result = NlmsFilter::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .epsilon(-1.0)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn count_tracks_updates() {
        let mut filter = NlmsFilter::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .build()
            .unwrap();

        assert_eq!(filter.count(), 0);
        filter.update(&[1.0], 2.0).unwrap();
        assert_eq!(filter.count(), 1);
        filter.update(&[1.0], 2.0).unwrap();
        assert_eq!(filter.count(), 2);
    }

    #[test]
    fn nlms_epsilon_accessor() {
        let filter = NlmsFilter::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .epsilon(1e-6)
            .build()
            .unwrap();

        assert!((filter.epsilon() - 1e-6).abs() < 1e-15);
    }

    #[test]
    fn nlms_default_epsilon() {
        let filter = NlmsFilter::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .build()
            .unwrap();

        assert!((filter.epsilon() - 1e-8).abs() < 1e-15);
    }

    #[test]
    fn lms_rejects_nan_target() {
        let mut filter = LmsFilter::builder()
            .dimensions(2)
            .learning_rate(0.01)
            .build()
            .unwrap();
        assert_eq!(
            filter.update(&[1.0, 2.0], f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(filter.count(), 0);
    }

    #[test]
    fn nlms_rejects_inf_target() {
        let mut filter = NlmsFilter::builder()
            .dimensions(2)
            .learning_rate(0.5)
            .build()
            .unwrap();
        assert_eq!(
            filter.update(&[1.0, 2.0], f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(filter.count(), 0);
    }
}
