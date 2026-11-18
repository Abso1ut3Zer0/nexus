use alloc::boxed::Box;
use alloc::vec;
use nexus_stats_core::math::axpy;

/// Online gradient descent optimizer with fixed learning rate.
///
/// Steps parameters in the negative gradient direction. The simplest
/// optimizer — useful as a baseline or when the loss landscape is
/// well-conditioned.
///
/// Designed for background threads or reduced-cadence loops, not the
/// hot path. Accumulate gradients from a batch, then step once.
///
/// # Use Cases
/// - Online parameter tuning
/// - Streaming model updates
/// - Baseline optimizer for comparison
///
/// # Complexity
/// O(dims) per step, heap-allocated parameter vector.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::learning::OnlineGd;
///
/// let mut gd = OnlineGd::builder()
///     .dimensions(2)
///     .learning_rate(0.1)
///     .build()
///     .unwrap();
///
/// // Minimize f(x) = x² → gradient = 2x
/// gd.set_parameters(&[5.0, -3.0]);
/// for _ in 0..100 {
///     let p = gd.parameters();
///     let grad = [2.0 * p[0], 2.0 * p[1]];
///     gd.step(&grad).unwrap();
/// }
/// assert!(gd.parameters()[0].abs() < 0.01);
/// ```
#[derive(Debug, Clone)]
pub struct OnlineGd {
    params: Box<[f64]>,
    learning_rate: f64,
    dims: usize,
    count: u64,
}

/// Builder for [`OnlineGd`].
#[derive(Debug, Clone)]
pub struct OnlineGdBuilder {
    dimensions: Option<usize>,
    learning_rate: Option<f64>,
}

impl OnlineGd {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> OnlineGdBuilder {
        OnlineGdBuilder {
            dimensions: Option::None,
            learning_rate: Option::None,
        }
    }

    /// Steps parameters in the negative gradient direction.
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
        axpy(-self.learning_rate, gradient, &mut self.params);
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

    /// Zeros all parameters, keeping configuration intact.
    #[inline]
    pub fn reset(&mut self) {
        self.params.fill(0.0);
        self.count = 0;
    }
}

impl OnlineGdBuilder {
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

    /// Builds the optimizer.
    ///
    /// # Errors
    /// Returns `ConfigError` if parameters are missing or invalid.
    #[inline]
    pub fn build(self) -> Result<OnlineGd, nexus_stats_core::ConfigError> {
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
        if !nexus_stats_core::math::positive_finite(lr) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "learning_rate must be positive",
            ));
        }
        Ok(OnlineGd {
            params: vec![0.0; dims].into_boxed_slice(),
            learning_rate: lr,
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
        // f(x) = x² → gradient = 2x, minimum at 0
        let mut gd = OnlineGd::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .build()
            .unwrap();

        gd.set_parameters(&[5.0]);
        for _ in 0..100 {
            let grad = [2.0 * gd.parameters()[0]];
            gd.step(&grad).unwrap();
        }
        assert!(
            gd.parameters()[0].abs() < 1e-6,
            "x = {}",
            gd.parameters()[0]
        );
    }

    #[test]
    fn minimizes_2d_quadratic() {
        // f(x,y) = x² + y² → gradient = [2x, 2y]
        let mut gd = OnlineGd::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        gd.set_parameters(&[5.0, -3.0]);
        for _ in 0..100 {
            let p = gd.parameters();
            let grad = [2.0 * p[0], 2.0 * p[1]];
            gd.step(&grad).unwrap();
        }
        assert!(gd.parameters()[0].abs() < 1e-6);
        assert!(gd.parameters()[1].abs() < 1e-6);
    }

    #[test]
    fn high_lr_diverges() {
        // Learning rate too high → parameters grow
        let mut gd = OnlineGd::builder()
            .dimensions(1)
            .learning_rate(1.5) // > 1.0 for quadratic → diverges
            .build()
            .unwrap();

        gd.set_parameters(&[1.0]);
        for _ in 0..20 {
            let grad = [2.0 * gd.parameters()[0]];
            gd.step(&grad).unwrap();
        }
        assert!(gd.parameters()[0].abs() > 1.0);
    }

    #[test]
    fn rejects_nan_gradient() {
        let mut gd = OnlineGd::builder()
            .dimensions(2)
            .learning_rate(0.01)
            .build()
            .unwrap();

        assert_eq!(
            gd.step(&[1.0, f64::NAN]),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(gd.count(), 0);
    }

    #[test]
    fn rejects_inf_gradient() {
        let mut gd = OnlineGd::builder()
            .dimensions(2)
            .learning_rate(0.01)
            .build()
            .unwrap();

        assert_eq!(
            gd.step(&[f64::INFINITY, 0.0]),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(
            gd.step(&[0.0, f64::NEG_INFINITY]),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(gd.count(), 0);
    }

    #[test]
    #[should_panic(expected = "gradient length")]
    fn dimension_mismatch_panics() {
        let mut gd = OnlineGd::builder()
            .dimensions(3)
            .learning_rate(0.01)
            .build()
            .unwrap();

        let _ = gd.step(&[1.0, 2.0]);
    }

    #[test]
    fn reset_zeros_params() {
        let mut gd = OnlineGd::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        gd.set_parameters(&[5.0, -3.0]);
        gd.step(&[1.0, 1.0]).unwrap();
        assert!(gd.count() > 0);

        gd.reset();
        assert_eq!(gd.count(), 0);
        assert!(gd.parameters().iter().all(|&p| p == 0.0));
    }

    #[test]
    fn set_parameters_works() {
        let mut gd = OnlineGd::builder()
            .dimensions(3)
            .learning_rate(0.01)
            .build()
            .unwrap();

        gd.set_parameters(&[1.0, 2.0, 3.0]);
        assert!((gd.parameter(0) - 1.0).abs() < f64::EPSILON);
        assert!((gd.parameter(1) - 2.0).abs() < f64::EPSILON);
        assert!((gd.parameter(2) - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn count_tracks_steps() {
        let mut gd = OnlineGd::builder()
            .dimensions(1)
            .learning_rate(0.01)
            .build()
            .unwrap();

        assert_eq!(gd.count(), 0);
        assert!(!gd.is_primed());
        gd.step(&[1.0]).unwrap();
        assert_eq!(gd.count(), 1);
        assert!(gd.is_primed());
    }

    #[test]
    fn builder_rejects_zero_dimensions() {
        let result = OnlineGd::builder()
            .dimensions(0)
            .learning_rate(0.01)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_rejects_negative_lr() {
        let result = OnlineGd::builder()
            .dimensions(2)
            .learning_rate(-0.01)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_requires_dimensions() {
        let result = OnlineGd::builder().learning_rate(0.01).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("dimensions"))
        ));
    }

    #[test]
    fn builder_requires_learning_rate() {
        let result = OnlineGd::builder().dimensions(2).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("learning_rate"))
        ));
    }
}
