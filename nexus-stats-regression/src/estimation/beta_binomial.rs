/// Bayesian success rate estimator using the Beta-Binomial conjugate prior.
///
/// Maintains a Beta(alpha, beta) posterior updated by observing binary
/// outcomes. The posterior mean is a natural shrinkage estimator —
/// with few observations, it stays near the prior; with many, it
/// converges to the observed rate.
///
/// # Use Cases
/// - Fill rate estimation (what fraction of orders fill?)
/// - Exchange reliability scoring
/// - A/B testing with early stopping
/// - Any binary outcome where you want uncertainty quantification
#[derive(Debug, Clone)]
pub struct BetaBinomial {
    alpha: f64,
    beta: f64,
    prior_alpha: f64,
    prior_beta: f64,
}

/// Builder for [`BetaBinomial`].
#[derive(Debug, Clone)]
pub struct BetaBinomialBuilder {
    alpha: f64,
    beta: f64,
}

impl BetaBinomial {
    /// Creates a new estimator with a uniform (uninformative) prior.
    ///
    /// Beta(1, 1) is the uniform distribution on [0, 1].
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            alpha: 1.0,
            beta: 1.0,
            prior_alpha: 1.0,
            prior_beta: 1.0,
        }
    }

    /// Creates an estimator with a specified prior.
    ///
    /// Higher alpha biases toward success, higher beta toward failure.
    /// `Beta(10, 1)` expresses strong prior belief in ~91% success rate.
    ///
    /// # Errors
    ///
    /// Both alpha and beta must be positive.
    #[inline]
    pub fn with_prior(alpha: f64, beta: f64) -> Result<Self, nexus_stats_core::ConfigError> {
        if !nexus_stats_core::math::positive_finite(alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be positive",
            ));
        }
        if !nexus_stats_core::math::positive_finite(beta) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "beta must be positive",
            ));
        }
        Ok(Self {
            alpha,
            beta,
            prior_alpha: alpha,
            prior_beta: beta,
        })
    }

    /// Creates a builder with defaults of alpha=1.0, beta=1.0.
    #[inline]
    #[must_use]
    pub fn builder() -> BetaBinomialBuilder {
        BetaBinomialBuilder {
            alpha: 1.0,
            beta: 1.0,
        }
    }

    /// Updates with a single binary outcome.
    #[inline]
    pub fn update(&mut self, success: bool) {
        if success {
            self.alpha += 1.0;
        } else {
            self.beta += 1.0;
        }
    }

    /// Updates with a batch of outcomes.
    #[inline]
    pub fn update_batch(&mut self, successes: u64, failures: u64) {
        self.alpha += successes as f64;
        self.beta += failures as f64;
    }

    /// Posterior mean: the expected success rate.
    ///
    /// This is the Bayes estimator under squared error loss.
    #[inline]
    #[must_use]
    pub fn mean(&self) -> f64 {
        self.alpha / (self.alpha + self.beta)
    }

    /// Posterior variance.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> f64 {
        let sum = self.alpha + self.beta;
        (self.alpha * self.beta) / (sum * sum * (sum + 1.0))
    }

    /// Posterior mode, or `None` if alpha <= 1 or beta <= 1.
    ///
    /// The mode is undefined for the uniform prior (1, 1) and
    /// degenerate when either parameter is at or below 1.
    #[inline]
    #[must_use]
    pub fn mode(&self) -> Option<f64> {
        if self.alpha <= 1.0 || self.beta <= 1.0 {
            None
        } else {
            Some((self.alpha - 1.0) / (self.alpha + self.beta - 2.0))
        }
    }

    /// Approximate credible interval using normal approximation.
    ///
    /// Returns `(lower, upper)` bounds for the given confidence level
    /// (e.g., 0.95 for a 95% interval). Uses the Abramowitz & Stegun
    /// rational approximation (26.2.23) for the inverse normal CDF.
    ///
    /// Returns `None` if no observations have been made, or if `confidence`
    /// is not in (0, 1) (NaN included).
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn credible_interval(&self, confidence: f64) -> Option<(f64, f64)> {
        if self.total() == 0.0 {
            return None;
        }
        if !(confidence > 0.0 && confidence < 1.0) {
            return None;
        }

        let tail = (1.0 - confidence) / 2.0;

        let z = nexus_stats_core::math::upper_tail_z(tail);

        let mean = self.mean();
        let std_dev = nexus_stats_core::math::sqrt(self.variance());
        let half_width = z * std_dev;

        // Clamp to [0, 1] since we're estimating a probability.
        let lower = if mean - half_width < 0.0 {
            0.0
        } else {
            mean - half_width
        };
        let upper = if mean + half_width > 1.0 {
            1.0
        } else {
            mean + half_width
        };

        Some((lower, upper))
    }

    /// Number of observed successes (excluding prior).
    #[inline]
    #[must_use]
    pub fn successes(&self) -> f64 {
        self.alpha - self.prior_alpha
    }

    /// Number of observed failures (excluding prior).
    #[inline]
    #[must_use]
    pub fn failures(&self) -> f64 {
        self.beta - self.prior_beta
    }

    /// Total number of observations (excluding prior).
    #[inline]
    #[must_use]
    pub fn total(&self) -> f64 {
        self.successes() + self.failures()
    }

    /// Total observations as an integer.
    #[inline]
    #[must_use]
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    pub fn count(&self) -> u64 {
        self.total() as u64
    }

    /// Whether any observations have been made.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.total() > 0.0
    }

    /// Resets to the original prior, discarding all observations.
    #[inline]
    pub fn reset(&mut self) {
        self.alpha = self.prior_alpha;
        self.beta = self.prior_beta;
    }
}

impl Default for BetaBinomial {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl BetaBinomialBuilder {
    /// Sets the alpha (success) prior parameter.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = alpha;
        self
    }

    /// Sets the beta (failure) prior parameter.
    #[inline]
    #[must_use]
    pub fn beta(mut self, beta: f64) -> Self {
        self.beta = beta;
        self
    }

    /// Builds the estimator.
    ///
    /// # Errors
    ///
    /// Both alpha and beta must be positive.
    #[inline]
    pub fn build(self) -> Result<BetaBinomial, nexus_stats_core::ConfigError> {
        if !nexus_stats_core::math::positive_finite(self.alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be positive",
            ));
        }
        if !nexus_stats_core::math::positive_finite(self.beta) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "beta must be positive",
            ));
        }
        Ok(BetaBinomial {
            alpha: self.alpha,
            beta: self.beta,
            prior_alpha: self.alpha,
            prior_beta: self.beta,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uniform_prior_balanced_observations() {
        let mut bb = BetaBinomial::new();
        for _ in 0..50 {
            bb.update(true);
            bb.update(false);
        }
        // Beta(51, 51) → mean = 0.5
        let mean = bb.mean();
        assert!((mean - 0.5).abs() < 0.01, "expected ~0.5, got {mean}");
    }

    #[test]
    fn informative_prior() {
        let bb = BetaBinomial::with_prior(10.0, 1.0).unwrap();
        // Beta(10, 1) → mean = 10/11 ≈ 0.909
        let mean = bb.mean();
        assert!(
            (mean - 10.0 / 11.0).abs() < 1e-10,
            "expected ~0.909, got {mean}"
        );
    }

    #[test]
    fn variance_decreases_with_observations() {
        let mut bb = BetaBinomial::new();
        let initial_var = bb.variance();

        for _ in 0..100 {
            bb.update(true);
        }
        let final_var = bb.variance();
        assert!(
            final_var < initial_var,
            "variance should decrease: {initial_var} → {final_var}"
        );
    }

    #[test]
    fn mode_none_for_uniform_prior() {
        let bb = BetaBinomial::new();
        assert!(bb.mode().is_none(), "mode undefined for Beta(1, 1)");
    }

    #[test]
    fn mode_some_for_informative_prior() {
        let bb = BetaBinomial::with_prior(10.0, 10.0).unwrap();
        // Beta(10, 10) → mode = 9/18 = 0.5
        let mode = bb.mode().unwrap();
        assert!((mode - 0.5).abs() < 1e-10, "expected 0.5, got {mode}");
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn credible_interval_narrows() {
        let mut bb = BetaBinomial::with_prior(2.0, 2.0).unwrap();
        for _ in 0..10 {
            bb.update(true);
            bb.update(false);
        }
        let (lo1, hi1) = bb.credible_interval(0.95).unwrap();
        let width1 = hi1 - lo1;

        for _ in 0..200 {
            bb.update(true);
            bb.update(false);
        }
        let (lo2, hi2) = bb.credible_interval(0.95).unwrap();
        let width2 = hi2 - lo2;

        assert!(
            width2 < width1,
            "interval should narrow: {width1:.4} → {width2:.4}"
        );
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn credible_interval_none_without_observations() {
        let bb = BetaBinomial::with_prior(2.0, 2.0).unwrap();
        assert!(bb.credible_interval(0.95).is_none());
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn credible_interval_none_for_invalid_confidence() {
        let mut bb = BetaBinomial::with_prior(2.0, 2.0).unwrap();
        bb.update(true);
        bb.update(false);
        for c in [
            0.0,
            1.0,
            -0.5,
            1.5,
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
        ] {
            assert!(bb.credible_interval(c).is_none(), "confidence {c}");
        }
        for c in [1e-9, 0.95, 1.0 - 1e-9] {
            assert!(bb.credible_interval(c).is_some(), "confidence {c}");
        }
    }

    #[test]
    fn observe_batch_equivalence() {
        let mut single = BetaBinomial::new();
        for _ in 0..30 {
            single.update(true);
        }
        for _ in 0..20 {
            single.update(false);
        }

        let mut batch = BetaBinomial::new();
        batch.update_batch(30, 20);

        assert!(
            (single.mean() - batch.mean()).abs() < 1e-10,
            "single={} batch={}",
            single.mean(),
            batch.mean()
        );
        assert_eq!(single.count(), batch.count());
    }

    #[test]
    fn reset_restores_prior() {
        let mut bb = BetaBinomial::with_prior(5.0, 3.0).unwrap();
        let mean_before = bb.mean();

        for _ in 0..100 {
            bb.update(true);
        }
        bb.reset();

        assert!(
            (bb.mean() - mean_before).abs() < 1e-10,
            "reset should restore prior mean"
        );
        assert_eq!(bb.count(), 0);
        assert!(!bb.is_primed());
    }

    #[test]
    fn default_is_new() {
        let a = BetaBinomial::new();
        let b = BetaBinomial::default();
        assert!(
            (a.mean() - b.mean()).abs() < 1e-10,
            "default and new should be identical"
        );
    }

    #[test]
    fn with_prior_validation() {
        assert!(BetaBinomial::with_prior(0.0, 1.0).is_err());
        assert!(BetaBinomial::with_prior(1.0, 0.0).is_err());
        assert!(BetaBinomial::with_prior(-1.0, 1.0).is_err());
        assert!(BetaBinomial::with_prior(1.0, -1.0).is_err());
        assert!(BetaBinomial::with_prior(0.5, 0.5).is_ok());
    }
}
