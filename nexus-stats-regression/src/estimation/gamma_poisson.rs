// Gamma-Poisson — Bayesian Event Rate Estimation
//
// Conjugate prior: Gamma(alpha, beta) with Poisson likelihood.
// Posterior after observing k events in t exposure: Gamma(alpha + k, beta + t).
// Posterior mean rate = alpha / beta.
//
// 32 bytes per instance. Zero allocation.

#![allow(
    clippy::suboptimal_flops,
    clippy::float_cmp,
    clippy::neg_cmp_op_on_partial_ord
)]

/// Bayesian event rate estimator using the Gamma-Poisson conjugate prior.
///
/// Maintains a Gamma posterior over the Poisson rate parameter.
/// Each observation adds event counts and exposure time, updating the
/// posterior analytically — no sampling, no iteration.
///
/// # Use Cases
/// - "What's the expected message arrival rate given what we've seen?"
/// - Estimating fill rates, error rates, or tick rates with uncertainty
/// - Credible intervals on event rates from limited data
///
/// # Complexity
/// - O(1) per observation, O(1) per query.
/// - 32 bytes state. Zero allocation.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::estimation::GammaPoisson;
///
/// let mut gp = GammaPoisson::new();
/// gp.update(100, 10.0);  // 100 events in 10 seconds
/// let rate = gp.rate();
/// // With weak prior (1,1), rate ≈ 101/11 ≈ 9.18
/// assert!((rate - 9.18).abs() < 0.01);
/// ```
#[derive(Debug, Clone)]
pub struct GammaPoisson {
    alpha: f64,
    beta: f64,
    prior_alpha: f64,
    prior_beta: f64,
}

/// Builder for [`GammaPoisson`].
#[derive(Debug, Clone)]
pub struct GammaPoissonBuilder {
    alpha: f64,
    beta: f64,
}

impl GammaPoisson {
    /// Creates a builder with default prior (alpha=1, beta=1).
    #[inline]
    #[must_use]
    pub fn builder() -> GammaPoissonBuilder {
        GammaPoissonBuilder {
            alpha: 1.0,
            beta: 1.0,
        }
    }

    /// Creates an estimator with a weakly informative prior (alpha=1, beta=1).
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self {
            alpha: 1.0,
            beta: 1.0,
            prior_alpha: 1.0,
            prior_beta: 1.0,
        }
    }

    /// Creates an estimator with a specific Gamma prior.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `alpha <= 0` or `beta <= 0`.
    #[inline]
    pub fn with_prior(alpha: f64, beta: f64) -> Result<Self, nexus_stats_core::ConfigError> {
        if !(alpha > 0.0) {
            return Err(nexus_stats_core::ConfigError::Invalid("alpha must be > 0"));
        }
        if !(beta > 0.0) {
            return Err(nexus_stats_core::ConfigError::Invalid("beta must be > 0"));
        }
        Ok(Self {
            alpha,
            beta,
            prior_alpha: alpha,
            prior_beta: beta,
        })
    }

    /// Updates with an observation: `count` events observed over `exposure` time.
    ///
    /// Updates the posterior: alpha += count, beta += exposure.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the exposure is NaN,
    /// `DataError::Infinite` if it is infinite, and `DataError::Negative` if
    /// it is negative (the posterior rate would go negative).
    #[inline]
    pub fn update(&mut self, count: u64, exposure: f64) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(exposure);
        if exposure < 0.0 {
            return Err(nexus_stats_core::DataError::Negative);
        }
        self.alpha += count as f64;
        self.beta += exposure;
        Ok(())
    }

    /// Posterior mean rate (alpha / beta).
    #[inline]
    #[must_use]
    pub fn rate(&self) -> f64 {
        self.alpha / self.beta
    }

    /// Posterior variance (alpha / beta²).
    #[inline]
    #[must_use]
    pub fn variance(&self) -> f64 {
        self.alpha / (self.beta * self.beta)
    }

    /// Approximate credible interval using normal approximation.
    ///
    /// Returns `(lower, upper)` bounds for the given confidence level,
    /// or `None` if no exposure has been observed or confidence is not in (0, 1).
    ///
    /// Uses the Abramowitz & Stegun rational approximation for the
    /// inverse normal CDF.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn credible_interval(&self, confidence: f64) -> Option<(f64, f64)> {
        if self.total_exposure() <= 0.0 {
            return None;
        }
        if !(confidence > 0.0 && confidence < 1.0) {
            return None;
        }

        let tail = (1.0 - confidence) / 2.0;

        // Abramowitz & Stegun rational approximation for inverse normal
        let t = nexus_stats_core::math::sqrt(-2.0 * nexus_stats_core::math::ln(tail));
        let z = t
            - (2.515_517 + 0.802_853 * t + 0.010_328 * t * t)
                / (1.0 + 1.432_788 * t + 0.189_269 * t * t + 0.001_308 * t * t * t);

        let std_dev = nexus_stats_core::math::sqrt(self.variance());
        let mean = self.rate();

        let lower = (mean - z * std_dev).max(0.0);
        Some((lower, mean + z * std_dev))
    }

    /// Total event count observed (excluding prior).
    #[inline]
    #[must_use]
    pub fn total_count(&self) -> f64 {
        self.alpha - self.prior_alpha
    }

    /// Total exposure time observed (excluding prior).
    #[inline]
    #[must_use]
    pub fn total_exposure(&self) -> f64 {
        self.beta - self.prior_beta
    }

    /// Total event count as integer.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total_count() as u64
    }

    /// Whether any exposure has been observed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.total_exposure() > 0.0
    }

    /// Resets to the original prior, discarding all observations.
    #[inline]
    pub fn reset(&mut self) {
        self.alpha = self.prior_alpha;
        self.beta = self.prior_beta;
    }
}

impl Default for GammaPoisson {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl GammaPoissonBuilder {
    /// Sets the shape parameter (prior alpha). Must be > 0.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = alpha;
        self
    }

    /// Sets the rate parameter (prior beta). Must be > 0.
    #[inline]
    #[must_use]
    pub fn beta(mut self, beta: f64) -> Self {
        self.beta = beta;
        self
    }

    /// Builds the estimator, validating parameters.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if alpha or beta are not positive.
    #[inline]
    pub fn build(self) -> Result<GammaPoisson, nexus_stats_core::ConfigError> {
        if !(self.alpha > 0.0) {
            return Err(nexus_stats_core::ConfigError::Invalid("alpha must be > 0"));
        }
        if !(self.beta > 0.0) {
            return Err(nexus_stats_core::ConfigError::Invalid("beta must be > 0"));
        }
        Ok(GammaPoisson {
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
    fn rate_after_observation() {
        let mut gp = GammaPoisson::new();
        gp.update(100, 10.0).unwrap();
        // Posterior: Gamma(1+100, 1+10) = Gamma(101, 11)
        // Mean = 101/11 ≈ 9.1818...
        let rate = gp.rate();
        assert!((rate - 101.0 / 11.0).abs() < 1e-10);
    }

    #[test]
    fn variance_decreases_with_exposure() {
        let mut gp = GammaPoisson::new();
        gp.update(10, 1.0).unwrap();
        let v1 = gp.variance();
        gp.update(100, 10.0).unwrap();
        let v2 = gp.variance();
        assert!(v2 < v1, "variance should decrease with more exposure");
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn credible_interval_narrows_with_data() {
        let mut gp = GammaPoisson::new();
        gp.update(10, 1.0).unwrap();
        let (lo1, hi1) = gp.credible_interval(0.95).unwrap();
        let width1 = hi1 - lo1;

        gp.update(1000, 100.0).unwrap();
        let (lo2, hi2) = gp.credible_interval(0.95).unwrap();
        let width2 = hi2 - lo2;

        assert!(width2 < width1, "interval should narrow with more data");
        // Rate should be within the interval
        let rate = gp.rate();
        assert!(rate >= lo2 && rate <= hi2);
    }

    #[test]
    fn reset_restores_prior() {
        let mut gp = GammaPoisson::with_prior(2.0, 3.0).unwrap();
        gp.update(50, 5.0).unwrap();
        assert!(gp.count() > 0);
        gp.reset();
        assert_eq!(gp.count(), 0);
        assert_eq!(gp.total_exposure(), 0.0);
        assert_eq!(gp.rate(), 2.0 / 3.0);
    }

    #[test]
    fn with_prior_validation() {
        assert!(GammaPoisson::with_prior(0.0, 1.0).is_err());
        assert!(GammaPoisson::with_prior(-1.0, 1.0).is_err());
        assert!(GammaPoisson::with_prior(1.0, 0.0).is_err());
        assert!(GammaPoisson::with_prior(1.0, -1.0).is_err());
        assert!(GammaPoisson::with_prior(f64::NAN, 1.0).is_err());
        assert!(GammaPoisson::with_prior(1.0, f64::NAN).is_err());
        assert!(GammaPoisson::with_prior(1.0, 1.0).is_ok());
    }

    #[test]
    fn default_is_new() {
        let a = GammaPoisson::new();
        let b = GammaPoisson::default();
        assert_eq!(a.rate(), b.rate());
        assert_eq!(a.variance(), b.variance());
    }

    #[test]
    fn batch_observation_accumulates() {
        let mut gp = GammaPoisson::new();
        gp.update(10, 1.0).unwrap();
        gp.update(20, 2.0).unwrap();
        gp.update(30, 3.0).unwrap();
        // Total: 60 events, 6.0 exposure
        assert_eq!(gp.count(), 60);
        assert!((gp.total_exposure() - 6.0).abs() < 1e-10);
        // Posterior: Gamma(61, 7) → 61/7
        assert!((gp.rate() - 61.0 / 7.0).abs() < 1e-10);
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn credible_interval_none_without_exposure() {
        let gp = GammaPoisson::new();
        assert!(gp.credible_interval(0.95).is_none());
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn credible_interval_none_for_invalid_confidence() {
        let mut gp = GammaPoisson::new();
        gp.update(10, 1.0).unwrap();
        assert!(gp.credible_interval(0.0).is_none());
        assert!(gp.credible_interval(1.0).is_none());
        assert!(gp.credible_interval(-0.5).is_none());
        assert!(gp.credible_interval(1.5).is_none());
    }

    #[test]
    fn builder_defaults() {
        let gp = GammaPoisson::builder().build().unwrap();
        assert_eq!(gp.rate(), 1.0); // Gamma(1,1) → mean = 1
    }

    #[test]
    fn builder_custom_prior() {
        let gp = GammaPoisson::builder()
            .alpha(5.0)
            .beta(2.0)
            .build()
            .unwrap();
        assert_eq!(gp.rate(), 2.5); // 5/2
    }

    #[test]
    fn builder_validation() {
        assert!(GammaPoisson::builder().alpha(0.0).build().is_err());
        assert!(GammaPoisson::builder().beta(-1.0).build().is_err());
    }

    #[test]
    fn rejects_nan_and_inf_exposure() {
        let mut gp = GammaPoisson::new();
        assert_eq!(
            gp.update(10, f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            gp.update(10, f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(gp.count(), 0);
    }
}
