use alloc::boxed::Box;
use alloc::vec;
use nexus_stats_core::math::MulAdd;

/// Numerically stable sigmoid function.
///
/// Uses the split formulation to avoid overflow:
/// - For z >= 0: 1 / (1 + exp(-z))
/// - For z < 0: exp(z) / (1 + exp(z))
#[inline]
fn sigmoid(z: f64) -> f64 {
    if z >= 0.0 {
        1.0 / (1.0 + nexus_stats_core::math::exp(-z))
    } else {
        let e = nexus_stats_core::math::exp(z);
        e / (1.0 + e)
    }
}

/// Online logistic regression via stochastic gradient descent.
///
/// Learns a binary classifier from streaming feature vectors. Updates
/// weights one sample at a time using the gradient of the cross-entropy
/// loss: `w += lr * (outcome - sigmoid(w·x)) * x`.
///
/// Only f64 is provided — f32 gradient precision is insufficient for
/// reliable convergence in online logistic regression.
///
/// # Use Cases
/// - Online binary classification
/// - Streaming probability estimation
/// - Real-time credit scoring or risk assessment
///
/// # Complexity
/// O(dims) per update, heap-allocated weight vector.
#[derive(Debug, Clone)]
pub struct LogisticRegression {
    weights: Box<[f64]>,
    learning_rate: f64,
    dims: usize,
    count: u64,
}

/// Builder for [`LogisticRegression`].
#[derive(Debug, Clone)]
pub struct LogisticRegressionBuilder {
    dimensions: Option<usize>,
    learning_rate: Option<f64>,
}

impl LogisticRegression {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> LogisticRegressionBuilder {
        LogisticRegressionBuilder {
            dimensions: Option::None,
            learning_rate: Option::None,
        }
    }

    /// Returns the predicted probability P(outcome=true | features).
    ///
    /// Output is in [0, 1].
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
        let mut z = 0.0_f64;
        for i in 0..self.dims {
            z = self.weights[i].fma(features[i], z);
        }
        sigmoid(z)
    }

    /// Updates weights from a single labeled observation.
    ///
    /// Applies stochastic gradient descent on the cross-entropy loss:
    /// `w += lr * (outcome - sigmoid(w·x)) * x`
    ///
    /// # Panics
    /// Panics if `features.len() != self.dimensions()`.
    #[inline]
    pub fn update(&mut self, features: &[f64], outcome: bool) {
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
        let mut z = 0.0_f64;
        for i in 0..self.dims {
            z = self.weights[i].fma(features[i], z);
        }
        let p = sigmoid(z);
        let error = (outcome as u8 as f64) - p;
        let step = self.learning_rate * error;
        for i in 0..self.dims {
            self.weights[i] = step.fma(features[i], self.weights[i]);
        }
        self.count += 1;
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

impl LogisticRegressionBuilder {
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

    /// Builds the classifier. Returns an error if parameters are missing or invalid.
    #[inline]
    pub fn build(self) -> Result<LogisticRegression, nexus_stats_core::ConfigError> {
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
        Ok(LogisticRegression {
            weights: vec![0.0_f64; dims].into_boxed_slice(),
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
    fn linearly_separable_convergence() {
        // Class 0: features around (-1, -1)
        // Class 1: features around (1, 1)
        let mut lr = LogisticRegression::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        for i in 0..2000 {
            let offset = (i as f64 * 0.37).sin() * 0.3;
            if i % 2 == 0 {
                lr.update(&[1.0 + offset, 1.0 + offset], true);
            } else {
                lr.update(&[-1.0 + offset, -1.0 + offset], false);
            }
        }

        // Should correctly classify clear examples
        let p_positive = lr.predict(&[2.0, 2.0]);
        let p_negative = lr.predict(&[-2.0, -2.0]);

        assert!(
            p_positive > 0.9,
            "p(true | [2,2]) = {p_positive}, expected > 0.9"
        );
        assert!(
            p_negative < 0.1,
            "p(true | [-2,-2]) = {p_negative}, expected < 0.1"
        );
    }

    #[test]
    fn predict_in_range() {
        let mut lr = LogisticRegression::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        // Even before training, output should be in [0, 1]
        let p = lr.predict(&[100.0, -100.0]);
        assert!((0.0..=1.0).contains(&p), "p = {p}, expected in [0, 1]");

        lr.update(&[1.0, 0.0], true);
        let p = lr.predict(&[1000.0, 0.0]);
        assert!((0.0..=1.0).contains(&p), "p = {p}, expected in [0, 1]");

        let p = lr.predict(&[-1000.0, 0.0]);
        assert!((0.0..=1.0).contains(&p), "p = {p}, expected in [0, 1]");
    }

    #[test]
    fn reset_clears_weights() {
        let mut lr = LogisticRegression::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();

        lr.update(&[1.0, 2.0], true);
        assert!(lr.count() > 0);
        assert!(lr.weights().iter().any(|&w| w != 0.0));

        lr.reset();
        assert_eq!(lr.count(), 0);
        assert!(lr.weights().iter().all(|&w| w == 0.0));
    }

    #[test]
    #[should_panic(expected = "feature length")]
    fn dimension_mismatch_predict() {
        let lr = LogisticRegression::builder()
            .dimensions(3)
            .learning_rate(0.1)
            .build()
            .unwrap();

        let _ = lr.predict(&[1.0, 2.0]);
    }

    #[test]
    #[should_panic(expected = "feature length")]
    fn dimension_mismatch_update() {
        let mut lr = LogisticRegression::builder()
            .dimensions(3)
            .learning_rate(0.1)
            .build()
            .unwrap();

        lr.update(&[1.0], true);
    }

    #[test]
    fn builder_rejects_zero_dimensions() {
        let result = LogisticRegression::builder()
            .dimensions(0)
            .learning_rate(0.1)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_rejects_negative_learning_rate() {
        let result = LogisticRegression::builder()
            .dimensions(2)
            .learning_rate(-0.01)
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_missing_dimensions() {
        let result = LogisticRegression::builder().learning_rate(0.1).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("dimensions"))
        ));
    }

    #[test]
    fn builder_missing_learning_rate() {
        let result = LogisticRegression::builder().dimensions(2).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("learning_rate"))
        ));
    }

    #[test]
    fn count_tracks_updates() {
        let mut lr = LogisticRegression::builder()
            .dimensions(1)
            .learning_rate(0.1)
            .build()
            .unwrap();

        assert_eq!(lr.count(), 0);
        lr.update(&[1.0], true);
        assert_eq!(lr.count(), 1);
        lr.update(&[1.0], false);
        assert_eq!(lr.count(), 2);
    }

    /// Features are the caller's contract (debug-asserted).
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "features must be finite")]
    fn nan_feature_panics_in_debug() {
        let mut lr = LogisticRegression::builder()
            .dimensions(2)
            .learning_rate(0.1)
            .build()
            .unwrap();
        lr.update(&[f64::NAN, 1.0], true);
    }
}
