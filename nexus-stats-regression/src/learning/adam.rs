use alloc::boxed::Box;
use alloc::vec;
use nexus_stats_core::math::MulAdd;

/// Adam optimizer — adaptive moment estimation with optional weight decay.
///
/// Tracks first moment (mean) and second moment (uncentered variance) of
/// gradients per coordinate. Bias-corrected estimates produce stable
/// updates even in early steps. With `weight_decay > 0`, applies
/// decoupled weight decay (AdamW) directly to parameters, not through
/// the adaptive learning rate.
///
/// Designed for background threads or reduced-cadence loops, not the
/// hot path. Accumulate gradients from a batch, then step once.
///
/// # Use Cases
/// - Default optimizer for most online learning tasks
/// - Non-convex optimization with noisy gradients
/// - Sparse and dense gradient problems
///
/// # Complexity
/// O(dims) per step, heap-allocated parameter and moment vectors.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::learning::Adam;
///
/// let mut adam = Adam::builder()
///     .dimensions(2)
///     .learning_rate(0.01)
///     .build()
///     .unwrap();
///
/// adam.set_parameters(&[5.0, -3.0]);
/// for _ in 0..3000 {
///     let p = adam.parameters();
///     let grad = [2.0 * p[0], 2.0 * p[1]];
///     adam.step(&grad).unwrap();
/// }
/// assert!(adam.parameters()[0].abs() < 0.1);
/// ```
#[derive(Debug, Clone)]
pub struct Adam {
    params: Box<[f64]>,
    m: Box<[f64]>,
    v: Box<[f64]>,
    learning_rate: f64,
    beta1: f64,
    beta2: f64,
    epsilon: f64,
    weight_decay: f64,
    beta1_t: f64,
    beta2_t: f64,
    dims: usize,
    count: u64,
}

/// Builder for [`Adam`].
#[derive(Debug, Clone)]
pub struct AdamBuilder {
    dimensions: Option<usize>,
    learning_rate: Option<f64>,
    beta1: Option<f64>,
    beta2: Option<f64>,
    epsilon: Option<f64>,
    weight_decay: Option<f64>,
}

impl Adam {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> AdamBuilder {
        AdamBuilder {
            dimensions: Option::None,
            learning_rate: Option::None,
            beta1: Option::None,
            beta2: Option::None,
            epsilon: Option::None,
            weight_decay: Option::None,
        }
    }

    /// Steps parameters using bias-corrected adaptive moments.
    ///
    /// When `weight_decay > 0`, decoupled weight decay is applied
    /// directly to parameters after the Adam update (AdamW).
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

        // Update biased moments
        let one_minus_b1 = 1.0 - self.beta1;
        let one_minus_b2 = 1.0 - self.beta2;
        for i in 0..self.dims {
            self.m[i] = self.beta1.fma(self.m[i], one_minus_b1 * gradient[i]);
            self.v[i] = self
                .beta2
                .fma(self.v[i], one_minus_b2 * gradient[i] * gradient[i]);
        }

        // Update power terms for bias correction
        self.beta1_t *= self.beta1;
        self.beta2_t *= self.beta2;
        let m_correction = 1.0 / (1.0 - self.beta1_t);
        let v_correction = 1.0 / (1.0 - self.beta2_t);

        // Apply Adam update + optional weight decay
        for i in 0..self.dims {
            let m_hat = self.m[i] * m_correction;
            let v_hat = self.v[i] * v_correction;
            self.params[i] -=
                self.learning_rate * m_hat / (nexus_stats_core::math::sqrt(v_hat) + self.epsilon);
            if self.weight_decay > 0.0 {
                self.params[i] -= self.weight_decay * self.params[i];
            }
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

    /// Overwrites the parameter vector. Moment state is preserved.
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

    /// Returns the first moment (gradient mean) vector.
    #[inline]
    #[must_use]
    pub fn first_moment(&self) -> &[f64] {
        &self.m
    }

    /// Returns the second moment (gradient variance) vector.
    #[inline]
    #[must_use]
    pub fn second_moment(&self) -> &[f64] {
        &self.v
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

    /// Returns beta1 (first moment decay rate).
    #[inline]
    #[must_use]
    pub fn beta1(&self) -> f64 {
        self.beta1
    }

    /// Returns beta2 (second moment decay rate).
    #[inline]
    #[must_use]
    pub fn beta2(&self) -> f64 {
        self.beta2
    }

    /// Returns the epsilon (stability constant).
    #[inline]
    #[must_use]
    pub fn epsilon(&self) -> f64 {
        self.epsilon
    }

    /// Returns the weight decay coefficient.
    #[inline]
    #[must_use]
    pub fn weight_decay(&self) -> f64 {
        self.weight_decay
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

    /// Zeros all parameters and moments, keeping configuration intact.
    #[inline]
    pub fn reset(&mut self) {
        self.params.fill(0.0);
        self.m.fill(0.0);
        self.v.fill(0.0);
        self.beta1_t = 1.0;
        self.beta2_t = 1.0;
        self.count = 0;
    }
}

impl AdamBuilder {
    /// Sets the number of parameter dimensions (required, >= 1).
    #[inline]
    #[must_use]
    pub fn dimensions(mut self, dims: usize) -> Self {
        self.dimensions = Option::Some(dims);
        self
    }

    /// Sets the learning rate (required, > 0). Common default: 0.001.
    #[inline]
    #[must_use]
    pub fn learning_rate(mut self, lr: f64) -> Self {
        self.learning_rate = Option::Some(lr);
        self
    }

    /// First moment decay rate (default 0.9, must be in (0, 1)).
    #[inline]
    #[must_use]
    pub fn beta1(mut self, b1: f64) -> Self {
        self.beta1 = Option::Some(b1);
        self
    }

    /// Second moment decay rate (default 0.999, must be in (0, 1)).
    #[inline]
    #[must_use]
    pub fn beta2(mut self, b2: f64) -> Self {
        self.beta2 = Option::Some(b2);
        self
    }

    /// Stability constant (default 1e-8, must be > 0).
    #[inline]
    #[must_use]
    pub fn epsilon(mut self, eps: f64) -> Self {
        self.epsilon = Option::Some(eps);
        self
    }

    /// Decoupled weight decay coefficient (default 0.0 = no decay).
    ///
    /// When > 0, parameters shrink toward zero each step independently
    /// of the adaptive learning rate (AdamW behavior).
    #[inline]
    #[must_use]
    pub fn weight_decay(mut self, wd: f64) -> Self {
        self.weight_decay = Option::Some(wd);
        self
    }

    /// Builds the optimizer.
    ///
    /// # Errors
    /// Returns `ConfigError` if parameters are missing or invalid.
    #[inline]
    pub fn build(self) -> Result<Adam, nexus_stats_core::ConfigError> {
        let dims = self
            .dimensions
            .ok_or(nexus_stats_core::ConfigError::Missing("dimensions"))?;
        let lr = self
            .learning_rate
            .ok_or(nexus_stats_core::ConfigError::Missing("learning_rate"))?;
        let b1 = self.beta1.unwrap_or(0.9);
        let b2 = self.beta2.unwrap_or(0.999);
        let eps = self.epsilon.unwrap_or(1e-8);
        let wd = self.weight_decay.unwrap_or(0.0);
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
        if !nexus_stats_core::math::in_unit_interval(b1) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "beta1 must be in (0, 1)",
            ));
        }
        if !nexus_stats_core::math::in_unit_interval(b2) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "beta2 must be in (0, 1)",
            ));
        }
        if !nexus_stats_core::math::positive_finite(eps) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "epsilon must be positive",
            ));
        }
        if !nexus_stats_core::math::nonnegative_finite(wd) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "weight_decay must be non-negative",
            ));
        }
        Ok(Adam {
            params: vec![0.0; dims].into_boxed_slice(),
            m: vec![0.0; dims].into_boxed_slice(),
            v: vec![0.0; dims].into_boxed_slice(),
            learning_rate: lr,
            beta1: b1,
            beta2: b2,
            epsilon: eps,
            weight_decay: wd,
            beta1_t: 1.0,
            beta2_t: 1.0,
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
        let mut adam = Adam::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        adam.set_parameters(&[5.0, -3.0]);
        for _ in 0..2000 {
            let p = adam.parameters();
            let grad = [2.0 * p[0], 2.0 * p[1]];
            adam.step(&grad).unwrap();
        }
        assert!(
            adam.parameters()[0].abs() < 0.01,
            "x = {}",
            adam.parameters()[0]
        );
        assert!(
            adam.parameters()[1].abs() < 0.01,
            "y = {}",
            adam.parameters()[1]
        );
    }

    #[test]
    fn minimizes_rosenbrock() {
        // f(x,y) = (1-x)² + 100(y-x²)²
        // df/dx = -2(1-x) - 400x(y-x²)
        // df/dy = 200(y-x²)
        let mut adam = Adam::builder()
            .dimensions(2)
            .learning_rate(0.001)
            .build()
            .unwrap();

        adam.set_parameters(&[-1.0, -1.0]);
        for _ in 0..50_000 {
            let p = adam.parameters();
            let x = p[0];
            let y = p[1];
            let dx = (-2.0f64).fma(1.0 - x, -(400.0 * x * (y - x * x)));
            let dy = 200.0 * (y - x * x);
            adam.step(&[dx, dy]).unwrap();
        }
        let p = adam.parameters();
        assert!((p[0] - 1.0).abs() < 0.1, "x = {}, expected ~1.0", p[0]);
        assert!((p[1] - 1.0).abs() < 0.1, "y = {}, expected ~1.0", p[1]);
    }

    #[test]
    fn bias_correction_works() {
        // Without bias correction, early m/v estimates are too small.
        // Verify first step produces a meaningful parameter update.
        let mut adam = Adam::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .build()
            .unwrap();

        adam.set_parameters(&[5.0]);
        adam.step(&[10.0]).unwrap();

        // After one step: m_hat and v_hat should be bias-corrected
        // and produce a step close to learning_rate (since |m_hat/sqrt(v_hat)| ≈ 1)
        let p = adam.parameters()[0];
        assert!(p < 5.0, "parameter should decrease with positive gradient");
        assert!(
            (5.0 - p - 0.1).abs() < 0.01,
            "step should be ~learning_rate, got {}",
            5.0 - p
        );
    }

    #[test]
    fn weight_decay_shrinks_params() {
        let mut adam = Adam::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .weight_decay(0.1)
            .build()
            .unwrap();

        adam.set_parameters(&[10.0]);
        // Step with zero gradient — only weight decay acts
        for _ in 0..100 {
            adam.step(&[0.0]).unwrap();
        }
        assert!(
            adam.parameters()[0].abs() < 10.0,
            "weight decay should shrink parameters, got {}",
            adam.parameters()[0]
        );
    }

    #[test]
    fn zero_weight_decay_is_standard_adam() {
        let mut adam = Adam::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .weight_decay(0.0)
            .build()
            .unwrap();

        assert!((adam.weight_decay() - 0.0).abs() < f64::EPSILON);

        adam.set_parameters(&[5.0]);
        // Zero gradient → no change (no weight decay either)
        adam.step(&[0.0]).unwrap();
        assert!((adam.parameters()[0] - 5.0).abs() < f64::EPSILON);
    }

    #[test]
    fn default_hyperparameters() {
        let adam = Adam::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .build()
            .unwrap();

        assert!((adam.beta1() - 0.9).abs() < f64::EPSILON);
        assert!((adam.beta2() - 0.999).abs() < f64::EPSILON);
        assert!((adam.epsilon() - 1e-8).abs() < 1e-15);
        assert!((adam.weight_decay() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn rejects_nan_gradient() {
        let mut adam = Adam::builder()
            .dimensions(2)
            .learning_rate(0.001)
            .build()
            .unwrap();

        assert_eq!(
            adam.step(&[1.0, f64::NAN]),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(adam.count(), 0);
    }

    #[test]
    fn rejects_inf_gradient() {
        let mut adam = Adam::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .build()
            .unwrap();

        assert_eq!(
            adam.step(&[f64::INFINITY]),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(adam.count(), 0);
    }

    #[test]
    #[should_panic(expected = "gradient length")]
    fn dimension_mismatch_panics() {
        let mut adam = Adam::builder()
            .dimensions(3)
            .learning_rate(0.001)
            .build()
            .unwrap();

        let _ = adam.step(&[1.0]);
    }

    #[test]
    fn reset_clears_all() {
        let mut adam = Adam::builder()
            .dimensions(2)
            .learning_rate(0.001)
            .build()
            .unwrap();

        adam.set_parameters(&[1.0, 2.0]);
        adam.step(&[1.0, 1.0]).unwrap();
        adam.step(&[1.0, 1.0]).unwrap();

        adam.reset();
        assert_eq!(adam.count(), 0);
        assert!(adam.parameters().iter().all(|&p| p == 0.0));
        assert!(adam.first_moment().iter().all(|&m| m == 0.0));
        assert!(adam.second_moment().iter().all(|&v| v == 0.0));
    }

    #[test]
    fn set_parameters_preserves_moments() {
        let mut adam = Adam::builder()
            .dimensions(2)
            .learning_rate(0.001)
            .build()
            .unwrap();

        adam.step(&[1.0, 2.0]).unwrap();
        let m_before: alloc::vec::Vec<f64> = adam.first_moment().to_vec();
        let v_before: alloc::vec::Vec<f64> = adam.second_moment().to_vec();

        adam.set_parameters(&[10.0, 20.0]);

        assert_eq!(adam.first_moment(), m_before.as_slice());
        assert_eq!(adam.second_moment(), v_before.as_slice());
    }

    #[test]
    fn count_tracks_steps() {
        let mut adam = Adam::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .build()
            .unwrap();

        assert_eq!(adam.count(), 0);
        assert!(!adam.is_primed());
        adam.step(&[1.0]).unwrap();
        assert_eq!(adam.count(), 1);
        assert!(adam.is_primed());
    }

    #[test]
    fn builder_validates_beta1() {
        let result = Adam::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .beta1(0.0)
            .build();
        assert!(result.is_err());

        let result = Adam::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .beta1(1.0)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_validates_beta2() {
        let result = Adam::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .beta2(0.0)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_validates_weight_decay() {
        let result = Adam::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .weight_decay(-0.01)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_requires_dimensions() {
        let result = Adam::builder().learning_rate(0.001).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("dimensions"))
        ));
    }

    #[test]
    fn builder_requires_learning_rate() {
        let result = Adam::builder().dimensions(2).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("learning_rate"))
        ));
    }
}
