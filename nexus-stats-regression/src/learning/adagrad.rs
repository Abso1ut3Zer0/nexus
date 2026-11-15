#![allow(clippy::suboptimal_flops, clippy::neg_cmp_op_on_partial_ord)]

extern crate alloc;
use alloc::boxed::Box;
use alloc::vec;

/// AdaGrad optimizer — per-coordinate adaptive learning rates.
///
/// Accumulates squared gradients per coordinate, scaling the effective
/// learning rate inversely with past gradient magnitude. Coordinates
/// that receive large gradients get smaller steps; coordinates with
/// small gradients keep larger steps.
///
/// Designed for background threads or reduced-cadence loops, not the
/// hot path. Accumulate gradients from a batch, then step once.
///
/// # Use Cases
/// - Sparse gradient problems (some dimensions update rarely)
/// - Online learning with heterogeneous feature scales
/// - Natural language processing (embedding updates)
///
/// # Complexity
/// O(dims) per step, heap-allocated parameter and accumulator vectors.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::learning::AdaGrad;
///
/// let mut ag = AdaGrad::builder()
///     .dimensions(2)
///     .learning_rate(0.5)
///     .build()
///     .unwrap();
///
/// ag.set_parameters(&[5.0, -3.0]);
/// for _ in 0..200 {
///     let p = ag.parameters();
///     let grad = [2.0 * p[0], 2.0 * p[1]];
///     ag.step(&grad).unwrap();
/// }
/// assert!(ag.parameters()[0].abs() < 0.1);
/// ```
#[derive(Debug, Clone)]
pub struct AdaGrad {
    params: Box<[f64]>,
    sum_sq_grad: Box<[f64]>,
    learning_rate: f64,
    epsilon: f64,
    dims: usize,
    count: u64,
}

/// Builder for [`AdaGrad`].
#[derive(Debug, Clone)]
pub struct AdaGradBuilder {
    dimensions: Option<usize>,
    learning_rate: Option<f64>,
    epsilon: Option<f64>,
}

impl AdaGrad {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> AdaGradBuilder {
        AdaGradBuilder {
            dimensions: Option::None,
            learning_rate: Option::None,
            epsilon: Option::None,
        }
    }

    /// Steps parameters using per-coordinate adaptive rates.
    ///
    /// # Panics
    /// Panics if `gradient.len() != dimensions`.
    ///
    /// # Errors
    /// Returns `DataError` if any gradient element is NaN or infinite.
    #[inline]
    pub fn step(&mut self, gradient: &[f64]) -> Result<(), nexus_stats_core::DataError> {
        assert_eq!(
            gradient.len(),
            self.dims,
            "gradient length {} != dimensions {}",
            gradient.len(),
            self.dims,
        );
        for &g in gradient {
            check_finite!(g);
        }
        for i in 0..self.dims {
            self.sum_sq_grad[i] += gradient[i] * gradient[i];
            self.params[i] -= self.learning_rate * gradient[i]
                / (nexus_stats_core::math::sqrt(self.sum_sq_grad[i]) + self.epsilon);
        }
        self.count += 1;
        Ok(())
    }

    /// Returns the current parameter vector.
    #[inline]
    #[must_use]
    pub fn parameters(&self) -> &[f64] {
        &self.params
    }

    /// Returns a single parameter by index.
    ///
    /// # Panics
    /// Panics if `index >= dimensions`.
    #[inline]
    #[must_use]
    pub fn parameter(&self, index: usize) -> f64 {
        self.params[index]
    }

    /// Overwrites the parameter vector.
    ///
    /// # Panics
    /// Panics if `params.len() != dimensions`.
    #[inline]
    pub fn set_parameters(&mut self, params: &[f64]) {
        assert_eq!(
            params.len(),
            self.dims,
            "params length {} != dimensions {}",
            params.len(),
            self.dims,
        );
        self.params.copy_from_slice(params);
    }

    /// Returns the accumulated squared gradients per coordinate.
    #[inline]
    #[must_use]
    pub fn accumulated_gradients(&self) -> &[f64] {
        &self.sum_sq_grad
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

    /// Returns the epsilon (stability constant).
    #[inline]
    #[must_use]
    pub fn epsilon(&self) -> f64 {
        self.epsilon
    }

    /// Returns the number of steps performed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether any steps have been performed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Zeros all parameters and accumulated gradients, keeping configuration intact.
    #[inline]
    pub fn reset(&mut self) {
        self.params.fill(0.0);
        self.sum_sq_grad.fill(0.0);
        self.count = 0;
    }
}

impl AdaGradBuilder {
    /// Sets the number of parameter dimensions (required, >= 1).
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

    /// Sets the stability constant (default 1e-8, must be > 0).
    #[inline]
    #[must_use]
    pub fn epsilon(mut self, eps: f64) -> Self {
        self.epsilon = Option::Some(eps);
        self
    }

    /// Builds the optimizer.
    ///
    /// # Errors
    /// Returns `ConfigError` if parameters are missing or invalid.
    #[inline]
    pub fn build(self) -> Result<AdaGrad, nexus_stats_core::ConfigError> {
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
        if !(lr > 0.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "learning_rate must be positive",
            ));
        }
        if !(eps > 0.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "epsilon must be positive",
            ));
        }
        Ok(AdaGrad {
            params: vec![0.0; dims].into_boxed_slice(),
            sum_sq_grad: vec![0.0; dims].into_boxed_slice(),
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
    fn minimizes_quadratic() {
        let mut ag = AdaGrad::builder()
            .dimensions(1)
            .learning_rate(1.0)
            .build()
            .unwrap();

        ag.set_parameters(&[5.0]);
        for _ in 0..500 {
            let grad = [2.0 * ag.parameters()[0]];
            ag.step(&grad).unwrap();
        }
        assert!(ag.parameters()[0].abs() < 0.1, "x = {}", ag.parameters()[0]);
    }

    #[test]
    fn adapts_to_different_scales() {
        // Dimension 0 has 100x larger gradients than dimension 1.
        // AdaGrad should adapt per-coordinate.
        let mut ag = AdaGrad::builder()
            .dimensions(2)
            .learning_rate(1.0)
            .build()
            .unwrap();

        ag.set_parameters(&[5.0, 5.0]);
        for _ in 0..500 {
            let p = ag.parameters();
            let grad = [200.0 * p[0], 2.0 * p[1]];
            ag.step(&grad).unwrap();
        }
        assert!(
            ag.parameters()[0].abs() < 0.5,
            "x0 = {}",
            ag.parameters()[0]
        );
        assert!(
            ag.parameters()[1].abs() < 0.5,
            "x1 = {}",
            ag.parameters()[1]
        );
    }

    #[test]
    fn accumulated_gradients_grow() {
        let mut ag = AdaGrad::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        ag.step(&[3.0, 4.0]).unwrap();
        let acc = ag.accumulated_gradients();
        assert!((acc[0] - 9.0).abs() < f64::EPSILON);
        assert!((acc[1] - 16.0).abs() < f64::EPSILON);

        ag.step(&[3.0, 4.0]).unwrap();
        let acc = ag.accumulated_gradients();
        assert!((acc[0] - 18.0).abs() < f64::EPSILON);
        assert!((acc[1] - 32.0).abs() < f64::EPSILON);
    }

    #[test]
    fn rejects_nan_gradient() {
        let mut ag = AdaGrad::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        assert_eq!(
            ag.step(&[1.0, f64::NAN]),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(ag.count(), 0);
    }

    #[test]
    fn rejects_inf_gradient() {
        let mut ag = AdaGrad::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .build()
            .unwrap();

        assert_eq!(
            ag.step(&[f64::INFINITY]),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(ag.count(), 0);
    }

    #[test]
    #[should_panic(expected = "gradient length")]
    fn dimension_mismatch_panics() {
        let mut ag = AdaGrad::builder()
            .dimensions(3)
            .learning_rate(0.1)
            .build()
            .unwrap();

        let _ = ag.step(&[1.0]);
    }

    #[test]
    fn reset_clears_all() {
        let mut ag = AdaGrad::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        ag.set_parameters(&[1.0, 2.0]);
        ag.step(&[1.0, 1.0]).unwrap();

        ag.reset();
        assert_eq!(ag.count(), 0);
        assert!(ag.parameters().iter().all(|&p| p == 0.0));
        assert!(ag.accumulated_gradients().iter().all(|&g| g == 0.0));
    }

    #[test]
    fn builder_rejects_zero_dimensions() {
        let result = AdaGrad::builder().dimensions(0).learning_rate(0.1).build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_rejects_negative_epsilon() {
        let result = AdaGrad::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .epsilon(-1.0)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn default_epsilon() {
        let ag = AdaGrad::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .build()
            .unwrap();

        assert!((ag.epsilon() - 1e-8).abs() < 1e-15);
    }

    #[test]
    fn count_tracks_steps() {
        let mut ag = AdaGrad::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .build()
            .unwrap();

        assert_eq!(ag.count(), 0);
        assert!(!ag.is_primed());
        ag.step(&[1.0]).unwrap();
        assert_eq!(ag.count(), 1);
        assert!(ag.is_primed());
    }

    #[test]
    fn builder_requires_dimensions() {
        let result = AdaGrad::builder().learning_rate(0.1).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("dimensions"))
        ));
    }

    #[test]
    fn builder_requires_learning_rate() {
        let result = AdaGrad::builder().dimensions(2).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("learning_rate"))
        ));
    }
}
