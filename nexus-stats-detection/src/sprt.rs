use nexus_stats_core::math::MulAdd;

// neg_cmp_op_on_partial_ord: !(x > 0.0) intentionally rejects NaN,
// unlike x <= 0.0 which passes NaN silently.

/// Result of a sequential test.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decision {
    /// Not enough evidence — keep sampling.
    Continue,
    /// Accept the null hypothesis (H0).
    AcceptNull,
    /// Accept the alternative hypothesis (H1).
    AcceptAlternative,
}

// ---------------------------------------------------------------------------
// SprtBernoulli
// ---------------------------------------------------------------------------

/// Wald's Sequential Probability Ratio Test for Bernoulli observations.
///
/// Tests H0: success rate = `p0` vs H1: success rate = `p1` by
/// accumulating log-likelihood ratios after each binary observation.
/// Terminates as soon as the cumulative ratio crosses one of two
/// pre-computed boundaries derived from the desired error rates.
///
/// F64 only — log-likelihood accumulation requires high precision.
/// f32 accumulation errors would cause premature or missed decisions.
///
/// # Use Cases
/// - A/B testing with early stopping
/// - Monitoring success rates against a baseline
/// - Detecting degraded rates in streaming processes
#[derive(Debug, Clone)]
pub struct SprtBernoulli {
    log_likelihood: f64,
    upper_bound: f64,
    lower_bound: f64,
    log_odds_success: f64,
    log_odds_failure: f64,
    count: u64,
    decided: bool,
    last_decision: Decision,
}

/// Builder for [`SprtBernoulli`].
#[derive(Debug, Clone)]
pub struct SprtBernoulliBuilder {
    null_rate: Option<f64>,
    alt_rate: Option<f64>,
    alpha: Option<f64>,
    beta: Option<f64>,
}

impl SprtBernoulli {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> SprtBernoulliBuilder {
        SprtBernoulliBuilder {
            null_rate: Option::None,
            alt_rate: Option::None,
            alpha: Option::None,
            beta: Option::None,
        }
    }

    /// Updates with a binary observation. Returns the current decision.
    ///
    /// Once a boundary is crossed the decision is sticky — further
    /// updates return the same result without changing state.
    #[inline]
    #[must_use]
    pub fn update(&mut self, success: bool) -> Decision {
        if self.decided {
            return self.last_decision;
        }

        if success {
            self.log_likelihood += self.log_odds_success;
        } else {
            self.log_likelihood += self.log_odds_failure;
        }
        self.count += 1;

        let decision = if self.log_likelihood >= self.upper_bound {
            Decision::AcceptAlternative
        } else if self.log_likelihood <= self.lower_bound {
            Decision::AcceptNull
        } else {
            Decision::Continue
        };

        if decision != Decision::Continue {
            self.decided = true;
            self.last_decision = decision;
        }

        decision
    }

    /// Current cumulative log-likelihood ratio.
    #[inline]
    #[must_use]
    pub fn log_likelihood_ratio(&self) -> f64 {
        self.log_likelihood
    }

    /// Number of observations processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether a terminal decision has been reached.
    #[inline]
    #[must_use]
    pub fn is_decided(&self) -> bool {
        self.decided
    }

    /// The current decision state.
    #[inline]
    #[must_use]
    pub fn decision(&self) -> Decision {
        self.last_decision
    }

    /// Whether at least one observation has been weighed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets log-likelihood and count. Configuration unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.log_likelihood = 0.0;
        self.count = 0;
        self.decided = false;
        self.last_decision = Decision::Continue;
    }
}

impl SprtBernoulliBuilder {
    /// Null hypothesis success rate (p0).
    #[inline]
    #[must_use]
    pub fn null_rate(mut self, rate: f64) -> Self {
        self.null_rate = Option::Some(rate);
        self
    }

    /// Alternative hypothesis success rate (p1).
    #[inline]
    #[must_use]
    pub fn alt_rate(mut self, rate: f64) -> Self {
        self.alt_rate = Option::Some(rate);
        self
    }

    /// Type I error rate (probability of rejecting H0 when true).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Option::Some(alpha);
        self
    }

    /// Type II error rate (probability of accepting H0 when H1 is true).
    #[inline]
    #[must_use]
    pub fn beta(mut self, beta: f64) -> Self {
        self.beta = Option::Some(beta);
        self
    }

    /// Builds the test.
    ///
    /// # Errors
    ///
    /// - All parameters must be set.
    /// - `null_rate` and `alt_rate` must be in (0, 1) and must differ.
    /// - `alpha` and `beta` must be in (0, 1).
    #[inline]
    pub fn build(self) -> Result<SprtBernoulli, nexus_stats_core::ConfigError> {
        let p0 = self
            .null_rate
            .ok_or(nexus_stats_core::ConfigError::Missing("null_rate"))?;
        let p1 = self
            .alt_rate
            .ok_or(nexus_stats_core::ConfigError::Missing("alt_rate"))?;
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        let beta = self
            .beta
            .ok_or(nexus_stats_core::ConfigError::Missing("beta"))?;

        if !(p0 > 0.0 && p0 < 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "null_rate must be in (0, 1)",
            ));
        }
        if !(p1 > 0.0 && p1 < 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alt_rate must be in (0, 1)",
            ));
        }
        if (p1 - p0).abs() <= f64::EPSILON {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "null_rate and alt_rate must differ",
            ));
        }
        if !nexus_stats_core::math::in_unit_interval(alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1)",
            ));
        }
        if !(beta > 0.0 && beta < 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "beta must be in (0, 1)",
            ));
        }

        let ln = nexus_stats_core::math::ln;

        let upper_bound = ln((1.0 - beta) / alpha);
        let lower_bound = ln(beta / (1.0 - alpha));
        let log_odds_success = ln(p1 / p0);
        let log_odds_failure = ln((1.0 - p1) / (1.0 - p0));

        Ok(SprtBernoulli {
            log_likelihood: 0.0,
            upper_bound,
            lower_bound,
            log_odds_success,
            log_odds_failure,
            count: 0,
            decided: false,
            last_decision: Decision::Continue,
        })
    }
}

// ---------------------------------------------------------------------------
// SprtGaussian
// ---------------------------------------------------------------------------

/// Wald's Sequential Probability Ratio Test for Gaussian observations
/// with known variance.
///
/// Tests H0: mean = `μ0` vs H1: mean = `μ1` by accumulating
/// log-likelihood ratios from each observation. Terminates when the
/// cumulative ratio crosses a pre-computed boundary.
///
/// # Use Cases
/// - Detecting mean shifts in latency distributions
/// - Quality control for continuous measurements
/// - Sequential clinical trials with continuous endpoints
#[derive(Debug, Clone)]
pub struct SprtGaussian {
    log_likelihood: f64,
    upper_bound: f64,
    lower_bound: f64,
    null_mean: f64,
    alt_mean: f64,
    variance: f64,
    half_inv_var: f64,
    mean_diff: f64,
    count: u64,
    decided: bool,
    last_decision: Decision,
}

/// Builder for [`SprtGaussian`].
#[derive(Debug, Clone)]
pub struct SprtGaussianBuilder {
    null_mean: Option<f64>,
    alt_mean: Option<f64>,
    variance: Option<f64>,
    alpha: Option<f64>,
    beta: Option<f64>,
}

impl SprtGaussian {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> SprtGaussianBuilder {
        SprtGaussianBuilder {
            null_mean: Option::None,
            alt_mean: Option::None,
            variance: Option::None,
            alpha: Option::None,
            beta: Option::None,
        }
    }

    /// Updates with an observation. Returns the current decision.
    ///
    /// Once a boundary is crossed the decision is sticky — further
    /// updates return the same result without changing state.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the value is NaN, or
    /// `DataError::Infinite` if the value is infinite.
    #[inline]
    pub fn update(&mut self, value: f64) -> Result<Decision, nexus_stats_core::DataError> {
        check_finite!(value);
        if self.decided {
            return Ok(self.last_decision);
        }

        self.log_likelihood += self.half_inv_var
            * self.mean_diff
            * (2.0f64.fma(value, -self.null_mean) - self.alt_mean);
        self.count += 1;

        let decision = if self.log_likelihood >= self.upper_bound {
            Decision::AcceptAlternative
        } else if self.log_likelihood <= self.lower_bound {
            Decision::AcceptNull
        } else {
            Decision::Continue
        };

        if decision != Decision::Continue {
            self.decided = true;
            self.last_decision = decision;
        }

        Ok(decision)
    }

    /// Current cumulative log-likelihood ratio.
    #[inline]
    #[must_use]
    pub fn log_likelihood_ratio(&self) -> f64 {
        self.log_likelihood
    }

    /// The assumed known variance.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> f64 {
        self.variance
    }

    /// Number of observations processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether a terminal decision has been reached.
    #[inline]
    #[must_use]
    pub fn is_decided(&self) -> bool {
        self.decided
    }

    /// The current decision state.
    #[inline]
    #[must_use]
    pub fn decision(&self) -> Decision {
        self.last_decision
    }

    /// Whether at least one observation has been weighed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets log-likelihood and count. Configuration unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.log_likelihood = 0.0;
        self.count = 0;
        self.decided = false;
        self.last_decision = Decision::Continue;
    }
}

impl SprtGaussianBuilder {
    /// Null hypothesis mean (μ0).
    #[inline]
    #[must_use]
    pub fn null_mean(mut self, mean: f64) -> Self {
        self.null_mean = Option::Some(mean);
        self
    }

    /// Alternative hypothesis mean (μ1).
    #[inline]
    #[must_use]
    pub fn alt_mean(mut self, mean: f64) -> Self {
        self.alt_mean = Option::Some(mean);
        self
    }

    /// Known variance of the process (σ²).
    #[inline]
    #[must_use]
    pub fn variance(mut self, variance: f64) -> Self {
        self.variance = Option::Some(variance);
        self
    }

    /// Type I error rate (probability of rejecting H0 when true).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Option::Some(alpha);
        self
    }

    /// Type II error rate (probability of accepting H0 when H1 is true).
    #[inline]
    #[must_use]
    pub fn beta(mut self, beta: f64) -> Self {
        self.beta = Option::Some(beta);
        self
    }

    /// Builds the test.
    ///
    /// # Errors
    ///
    /// - All parameters must be set.
    /// - `variance` must be positive.
    /// - `null_mean` and `alt_mean` must differ.
    /// - `alpha` and `beta` must be in (0, 1).
    #[inline]
    pub fn build(self) -> Result<SprtGaussian, nexus_stats_core::ConfigError> {
        let null_mean = self
            .null_mean
            .ok_or(nexus_stats_core::ConfigError::Missing("null_mean"))?;
        let alt_mean = self
            .alt_mean
            .ok_or(nexus_stats_core::ConfigError::Missing("alt_mean"))?;
        let variance = self
            .variance
            .ok_or(nexus_stats_core::ConfigError::Missing("variance"))?;
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        let beta = self
            .beta
            .ok_or(nexus_stats_core::ConfigError::Missing("beta"))?;

        if !nexus_stats_core::math::positive_finite(variance) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "variance must be positive",
            ));
        }
        if (alt_mean - null_mean).abs() <= f64::EPSILON {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "null_mean and alt_mean must differ",
            ));
        }
        if !nexus_stats_core::math::in_unit_interval(alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1)",
            ));
        }
        if !(beta > 0.0 && beta < 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "beta must be in (0, 1)",
            ));
        }

        let ln = nexus_stats_core::math::ln;

        let upper_bound = ln((1.0 - beta) / alpha);
        let lower_bound = ln(beta / (1.0 - alpha));
        let half_inv_var = 0.5 / variance;
        let mean_diff = alt_mean - null_mean;

        Ok(SprtGaussian {
            log_likelihood: 0.0,
            upper_bound,
            lower_bound,
            null_mean,
            alt_mean,
            variance,
            half_inv_var,
            mean_diff,
            count: 0,
            decided: false,
            last_decision: Decision::Continue,
        })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- SprtBernoulli -------------------------------------------------------

    #[test]
    fn bernoulli_accepts_alternative_on_high_rate() {
        let mut sprt = SprtBernoulli::builder()
            .null_rate(0.50)
            .alt_rate(0.55)
            .alpha(0.05)
            .beta(0.05)
            .build()
            .unwrap();

        // Feed 80% successes — clearly above both hypotheses, should
        // accumulate evidence toward H1.
        let mut decision = Decision::Continue;
        for i in 0..10_000 {
            let success = i % 5 != 0; // 80% success rate
            decision = sprt.update(success);
            if decision != Decision::Continue {
                break;
            }
        }
        assert_eq!(decision, Decision::AcceptAlternative);
    }

    #[test]
    fn bernoulli_accepts_null_on_low_rate() {
        let mut sprt = SprtBernoulli::builder()
            .null_rate(0.50)
            .alt_rate(0.55)
            .alpha(0.05)
            .beta(0.05)
            .build()
            .unwrap();

        // Feed exactly 50% — should accumulate evidence for H0.
        let mut decision = Decision::Continue;
        for i in 0..10_000 {
            let success = i % 2 == 0;
            decision = sprt.update(success);
            if decision != Decision::Continue {
                break;
            }
        }
        assert_eq!(decision, Decision::AcceptNull);
    }

    #[test]
    fn bernoulli_decision_is_sticky() {
        let mut sprt = SprtBernoulli::builder()
            .null_rate(0.50)
            .alt_rate(0.55)
            .alpha(0.05)
            .beta(0.05)
            .build()
            .unwrap();

        // Drive to a decision.
        for i in 0..10_000 {
            let success = i % 5 != 0;
            if sprt.update(success) != Decision::Continue {
                break;
            }
        }

        assert!(sprt.is_decided());
        let locked = sprt.decision();

        // Further observations don't change the outcome.
        for _ in 0..100 {
            assert_eq!(sprt.update(false), locked);
        }
    }

    #[test]
    fn bernoulli_reset() {
        let mut sprt = SprtBernoulli::builder()
            .null_rate(0.50)
            .alt_rate(0.55)
            .alpha(0.05)
            .beta(0.05)
            .build()
            .unwrap();

        // Accumulate some evidence.
        for _ in 0..50 {
            let _ = sprt.update(true);
        }
        assert!(sprt.count() > 0);

        sprt.reset();
        assert_eq!(sprt.count(), 0);
        assert_eq!(sprt.log_likelihood_ratio(), 0.0);
        assert!(!sprt.is_decided());
        assert_eq!(sprt.decision(), Decision::Continue);
    }

    #[test]
    fn bernoulli_count_tracks_observations() {
        let mut sprt = SprtBernoulli::builder()
            .null_rate(0.50)
            .alt_rate(0.55)
            .alpha(0.05)
            .beta(0.05)
            .build()
            .unwrap();

        for _ in 0..7 {
            let _ = sprt.update(true);
        }
        assert_eq!(sprt.count(), 7);
    }

    // -- SprtGaussian --------------------------------------------------------

    #[test]
    fn gaussian_accepts_alternative_above_alt_mean() {
        let mut sprt = SprtGaussian::builder()
            .null_mean(100.0)
            .alt_mean(105.0)
            .variance(25.0)
            .alpha(0.05)
            .beta(0.05)
            .build()
            .unwrap();

        let mut decision = Decision::Continue;
        for _ in 0..10_000 {
            decision = sprt.update(108.0).unwrap();
            if decision != Decision::Continue {
                break;
            }
        }
        assert_eq!(decision, Decision::AcceptAlternative);
    }

    #[test]
    fn gaussian_accepts_null_at_null_mean() {
        let mut sprt = SprtGaussian::builder()
            .null_mean(100.0)
            .alt_mean(105.0)
            .variance(25.0)
            .alpha(0.05)
            .beta(0.05)
            .build()
            .unwrap();

        let mut decision = Decision::Continue;
        for _ in 0..10_000 {
            decision = sprt.update(100.0).unwrap();
            if decision != Decision::Continue {
                break;
            }
        }
        assert_eq!(decision, Decision::AcceptNull);
    }

    #[test]
    fn gaussian_decision_is_sticky() {
        let mut sprt = SprtGaussian::builder()
            .null_mean(100.0)
            .alt_mean(105.0)
            .variance(25.0)
            .alpha(0.05)
            .beta(0.05)
            .build()
            .unwrap();

        for _ in 0..10_000 {
            if sprt.update(108.0).unwrap() != Decision::Continue {
                break;
            }
        }

        assert!(sprt.is_decided());
        let locked = sprt.decision();

        for _ in 0..100 {
            assert_eq!(sprt.update(90.0).unwrap(), locked);
        }
    }

    // -- Builder validation --------------------------------------------------

    #[test]
    fn bernoulli_missing_params() {
        assert!(matches!(
            SprtBernoulli::builder()
                .alt_rate(0.55)
                .alpha(0.05)
                .beta(0.05)
                .build(),
            Err(nexus_stats_core::ConfigError::Missing("null_rate"))
        ));
    }

    #[test]
    fn bernoulli_invalid_rates() {
        assert!(matches!(
            SprtBernoulli::builder()
                .null_rate(0.0)
                .alt_rate(0.55)
                .alpha(0.05)
                .beta(0.05)
                .build(),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));

        assert!(matches!(
            SprtBernoulli::builder()
                .null_rate(0.50)
                .alt_rate(0.50)
                .alpha(0.05)
                .beta(0.05)
                .build(),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn gaussian_missing_params() {
        assert!(matches!(
            SprtGaussian::builder()
                .alt_mean(105.0)
                .variance(25.0)
                .alpha(0.05)
                .beta(0.05)
                .build(),
            Err(nexus_stats_core::ConfigError::Missing("null_mean"))
        ));
    }

    #[test]
    fn gaussian_invalid_variance() {
        assert!(matches!(
            SprtGaussian::builder()
                .null_mean(100.0)
                .alt_mean(105.0)
                .variance(0.0)
                .alpha(0.05)
                .beta(0.05)
                .build(),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }

    // -- Boundary correctness ------------------------------------------------

    #[test]
    fn bounds_are_correct() {
        let alpha = 0.05_f64;
        let beta = 0.10_f64;

        let sprt = SprtBernoulli::builder()
            .null_rate(0.40)
            .alt_rate(0.60)
            .alpha(alpha)
            .beta(beta)
            .build()
            .unwrap();

        let expected_upper = ((1.0 - beta) / alpha).ln();
        let expected_lower = (beta / (1.0 - alpha)).ln();

        assert!(
            (sprt.log_likelihood_ratio() - 0.0).abs() < f64::EPSILON,
            "initial log-likelihood should be zero"
        );

        // Drive to upper bound and verify it matches expected.
        // We can't read bounds directly, but we can verify the math
        // by checking the Gaussian variant which has the same formula.
        let sprt_g = SprtGaussian::builder()
            .null_mean(0.0)
            .alt_mean(1.0)
            .variance(1.0)
            .alpha(alpha)
            .beta(beta)
            .build()
            .unwrap();

        // Both should have identical bounds — verify via deterministic
        // observations that trigger at the expected sample count.
        // For now, just verify the formulas are consistent by checking
        // that the same alpha/beta produce the same sign structure.
        assert!(expected_upper > 0.0);
        assert!(expected_lower < 0.0);

        // Bernoulli: one observation of success with p1 > p0 should
        // move log-likelihood positive.
        let mut b = SprtBernoulli::builder()
            .null_rate(0.40)
            .alt_rate(0.60)
            .alpha(alpha)
            .beta(beta)
            .build()
            .unwrap();
        let _ = b.update(true);
        assert!(b.log_likelihood_ratio() > 0.0);

        // Gaussian: one observation above midpoint should move positive.
        let mut g = SprtGaussian::builder()
            .null_mean(0.0)
            .alt_mean(1.0)
            .variance(1.0)
            .alpha(alpha)
            .beta(beta)
            .build()
            .unwrap();
        g.update(2.0).unwrap();
        assert!(g.log_likelihood_ratio() > 0.0);

        // Verify numeric bound values match Wald's formulas directly.
        // Test module is a child of the defining module — can access private fields.
        assert!(
            (sprt.upper_bound - expected_upper).abs() < 1e-10,
            "Bernoulli upper bound: got {}, expected {expected_upper}",
            sprt.upper_bound
        );
        assert!(
            (sprt.lower_bound - expected_lower).abs() < 1e-10,
            "Bernoulli lower bound: got {}, expected {expected_lower}",
            sprt.lower_bound
        );
        assert!(
            (sprt_g.upper_bound - expected_upper).abs() < 1e-10,
            "Gaussian upper bound: got {}, expected {expected_upper}",
            sprt_g.upper_bound
        );
        assert!(
            (sprt_g.lower_bound - expected_lower).abs() < 1e-10,
            "Gaussian lower bound: got {}, expected {expected_lower}",
            sprt_g.lower_bound
        );
    }

    #[test]
    fn gaussian_rejects_nan_and_inf() {
        let mut sprt = SprtGaussian::builder()
            .null_mean(100.0)
            .alt_mean(105.0)
            .variance(25.0)
            .alpha(0.05)
            .beta(0.05)
            .build()
            .unwrap();
        assert_eq!(
            sprt.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            sprt.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(sprt.count(), 0);
    }
}
