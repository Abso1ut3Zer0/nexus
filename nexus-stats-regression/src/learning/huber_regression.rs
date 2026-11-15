extern crate alloc;
use alloc::boxed::Box;
use alloc::vec;
use nexus_stats_core::math::MulAdd;

/// Streaming linear regression with Huber loss.
///
/// The loss transitions from quadratic to linear at threshold δ,
/// making the regression robust to outliers. Uses SGD with the
/// Huber gradient:
///
/// ```text
/// gradient = residual              if |residual| <= δ
/// gradient = δ * sign(residual)    if |residual| > δ
/// ```
///
/// # Use Cases
///
/// - Spread estimation where occasional large fills shouldn't dominate
/// - Robust parameter estimation for streaming models
/// - Online regression where clean data is mixed with outliers
///
/// # No implicit bias term
///
/// The model is `y = w·x` (no intercept). To fit `y = w·x + b`, include
/// a constant `1.0` as the last feature: `features = &[x1, x2, 1.0]`.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::learning::HuberRegression;
///
/// let mut reg = HuberRegression::builder()
///     .dimensions(2)
///     .learning_rate(0.01)
///     .delta(1.0)
///     .build()
///     .unwrap();
///
/// // y = 2*x1 + 3*x2 with noise
/// for i in 0..1000 {
///     let x1 = (i % 10) as f64;
///     let x2 = (i % 7) as f64;
///     let y = 2.0 * x1 + 3.0 * x2 + 0.1 * (i as f64 % 3.0 - 1.0);
///     reg.update(&[x1, x2], y).unwrap();
/// }
/// let w = reg.weights();
/// assert!((w[0] - 2.0).abs() < 0.5);
/// assert!((w[1] - 3.0).abs() < 0.5);
/// ```
#[derive(Debug, Clone)]
pub struct HuberRegression {
    weights: Box<[f64]>,
    dim: usize,
    lr: f64,
    delta: f64,
    count: u64,
}

/// Builder for [`HuberRegression`].
#[derive(Debug, Clone)]
pub struct HuberRegressionBuilder {
    dimensions: Option<usize>,
    learning_rate: Option<f64>,
    delta: Option<f64>,
}

impl HuberRegression {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> HuberRegressionBuilder {
        HuberRegressionBuilder {
            dimensions: None,
            learning_rate: None,
            delta: None,
        }
    }

    /// Feed one observation: features `x` and target `y`.
    ///
    /// Updates weights via SGD with Huber loss gradient.
    ///
    /// # Panics
    ///
    /// Panics if `features.len() != dimensions`.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if any input is NaN or infinite.
    pub fn update(
        &mut self,
        features: &[f64],
        target: f64,
    ) -> Result<(), nexus_stats_core::DataError> {
        assert_eq!(
            features.len(),
            self.dim,
            "features dimension ({}) != configured dim ({})",
            features.len(),
            self.dim,
        );
        for &v in features {
            check_finite!(v);
        }
        check_finite!(target);

        self.count += 1;

        // Compute prediction: dot(weights, features)
        let mut pred = 0.0f64;
        for i in 0..self.dim {
            pred = self.weights[i].fma(features[i], pred);
        }

        // Residual
        let residual = target - pred;

        // Huber gradient
        let grad_scale = if residual.abs() <= self.delta {
            residual
        } else {
            self.delta * residual.signum()
        };

        // SGD update: w += lr * grad_scale * x
        let step = self.lr * grad_scale;
        for i in 0..self.dim {
            self.weights[i] = step.fma(features[i], self.weights[i]);
        }

        Ok(())
    }

    /// Predict target for given features.
    ///
    /// # Panics
    ///
    /// Panics if `features.len() != dimensions`.
    #[must_use]
    pub fn predict(&self, features: &[f64]) -> f64 {
        assert_eq!(features.len(), self.dim);
        let mut pred = 0.0f64;
        for i in 0..self.dim {
            pred = self.weights[i].fma(features[i], pred);
        }
        pred
    }

    /// Current weight vector.
    #[inline]
    #[must_use]
    pub fn weights(&self) -> &[f64] {
        &self.weights
    }

    /// Whether any updates have been performed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Number of updates.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Reset weights to zero.
    pub fn reset(&mut self) {
        self.weights.iter_mut().for_each(|w| *w = 0.0);
        self.count = 0;
    }
}

impl HuberRegressionBuilder {
    /// Number of features (required).
    #[inline]
    #[must_use]
    pub fn dimensions(mut self, d: usize) -> Self {
        self.dimensions = Some(d);
        self
    }

    /// Learning rate for SGD (required).
    #[inline]
    #[must_use]
    pub fn learning_rate(mut self, lr: f64) -> Self {
        self.learning_rate = Some(lr);
        self
    }

    /// Huber threshold — residuals beyond this are linear (required).
    #[inline]
    #[must_use]
    pub fn delta(mut self, delta: f64) -> Self {
        self.delta = Some(delta);
        self
    }

    /// Build.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if any parameter is missing or invalid.
    pub fn build(self) -> Result<HuberRegression, nexus_stats_core::ConfigError> {
        let dim = self
            .dimensions
            .ok_or(nexus_stats_core::ConfigError::Missing("dimensions"))?;
        if dim == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "dimensions must be > 0",
            ));
        }
        let lr = self
            .learning_rate
            .ok_or(nexus_stats_core::ConfigError::Missing("learning_rate"))?;
        if lr <= 0.0 || !lr.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "learning_rate must be positive",
            ));
        }
        let delta = self
            .delta
            .ok_or(nexus_stats_core::ConfigError::Missing("delta"))?;
        if delta <= 0.0 || !delta.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "delta must be positive",
            ));
        }

        Ok(HuberRegression {
            weights: vec![0.0; dim].into_boxed_slice(),
            dim,
            lr,
            delta,
            count: 0,
        })
    }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    #[test]
    fn clean_linear_data_converges() {
        let mut reg = HuberRegression::builder()
            .dimensions(2)
            .learning_rate(0.001)
            .delta(10.0) // large delta → behaves like least squares
            .build()
            .unwrap();

        // y = 2*x1 + 3*x2
        for i in 0..5000 {
            let x1 = (i % 10) as f64;
            let x2 = (i % 7) as f64;
            let y = 2.0f64.mul_add(x1, 3.0 * x2);
            reg.update(&[x1, x2], y).unwrap();
        }

        let w = reg.weights();
        assert!((w[0] - 2.0).abs() < 0.5, "w[0]={}, expected ~2.0", w[0]);
        assert!((w[1] - 3.0).abs() < 0.5, "w[1]={}, expected ~3.0", w[1]);
    }

    #[test]
    fn outlier_robustness() {
        // Compare: Huber vs infinite-delta (standard regression) with outliers.
        // Use small learning rate relative to feature scale to avoid divergence.
        let mut huber = HuberRegression::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .delta(5.0)
            .build()
            .unwrap();

        let mut standard = HuberRegression::builder()
            .dimensions(1)
            .learning_rate(0.001)
            .delta(f64::MAX)
            .build()
            .unwrap();

        // y = 3*x (x in [0.1, 1.0]), with frequent large outliers
        for i in 0..3000 {
            let x = (i % 10) as f64 / 10.0 + 0.1;
            let y = if i % 10 == 0 {
                500.0 // 10% outlier rate, extreme value
            } else {
                3.0 * x
            };
            huber.update(&[x], y).unwrap();
            standard.update(&[x], y).unwrap();
        }

        let huber_err = (huber.weights()[0] - 3.0).abs();
        let std_err = (standard.weights()[0] - 3.0).abs();
        assert!(
            huber_err < std_err,
            "Huber error ({huber_err}) should be less than standard ({std_err})"
        );
    }

    #[test]
    fn predict_matches_weights() {
        let mut reg = HuberRegression::builder()
            .dimensions(2)
            .learning_rate(0.01)
            .delta(5.0)
            .build()
            .unwrap();

        for i in 0..100 {
            reg.update(&[i as f64, 1.0], (i * 2) as f64).unwrap();
        }

        let w = reg.weights();
        let pred = reg.predict(&[10.0, 1.0]);
        let expected = w[0].mul_add(10.0, w[1] * 1.0);
        assert!((pred - expected).abs() < 1e-10);
    }

    #[test]
    fn reset_clears() {
        let mut reg = HuberRegression::builder()
            .dimensions(2)
            .learning_rate(0.01)
            .delta(5.0)
            .build()
            .unwrap();

        for i in 0..100 {
            reg.update(&[i as f64, 1.0], (i * 2) as f64).unwrap();
        }
        reg.reset();
        assert_eq!(reg.count(), 0);
        assert_eq!(reg.weights(), &[0.0, 0.0]);
    }

    #[test]
    fn invalid_config() {
        assert!(
            HuberRegression::builder()
                .learning_rate(0.01)
                .delta(1.0)
                .build()
                .is_err()
        ); // missing dim
        assert!(
            HuberRegression::builder()
                .dimensions(2)
                .delta(1.0)
                .build()
                .is_err()
        ); // missing lr
        assert!(
            HuberRegression::builder()
                .dimensions(2)
                .learning_rate(0.01)
                .build()
                .is_err()
        ); // missing delta
    }
}
