use super::arm_bank::{ArmBank, checked_decay};
use super::sampling::f64_impl;

/// Thompson Sampling with Beta prior.
///
/// Each arm maintains Beta(alpha, beta) parameters. Selection samples
/// from each arm's Beta posterior and picks the highest sample.
/// Arms with wider posteriors (more uncertain) are explored naturally.
///
/// For binary rewards: alpha counts successes, beta counts failures.
/// For continuous [0, 1] rewards: alpha += reward, beta += (1 - reward).
///
/// Thompson (1933), Agrawal & Goyal (2012).
///
/// # Parameters
///
/// - `arms` — number of arms (>= 2)
/// - `initial_alpha` — prior alpha for all arms (default: 1.0, uniform)
/// - `initial_beta` — prior beta for all arms (default: 1.0, uniform)
/// - `decay` — multiplicative discount on alpha, beta per update (default: 1.0)
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::learning::ThompsonBeta;
///
/// let mut bandit = ThompsonBeta::builder()
///     .arms(3)
///     .build()
///     .unwrap();
///
/// let mut s: u64 = 42;
/// let mut rng = || -> f64 {
///     s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
///     (s >> 33) as f64 / (1u64 << 31) as f64
/// };
/// let arm = bandit.select(&mut rng);
/// bandit.update(arm, 1.0).unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct ThompsonBeta {
    /// Posterior parameters per arm (`a` = alphas, `b` = betas), plus the pull counter.
    bank: ArmBank,
    initial_alpha: f64,
    initial_beta: f64,
    decay: f64,
}

/// Builder for [`ThompsonBeta`].
#[derive(Debug, Clone)]
pub struct ThompsonBetaBuilder {
    arms: Option<usize>,
    initial_alpha: f64,
    initial_beta: f64,
    decay: f64,
    min_samples: Option<u64>,
}

impl ThompsonBeta {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> ThompsonBetaBuilder {
        ThompsonBetaBuilder {
            arms: None,
            initial_alpha: 1.0,
            initial_beta: 1.0,
            decay: 1.0,
            min_samples: None,
        }
    }

    /// Samples from each arm's Beta posterior, returns the arm
    /// with the highest sample.
    ///
    /// `rng` must return independent uniform samples in [0, 1).
    #[must_use]
    pub fn select(&self, rng: &mut impl FnMut() -> f64) -> usize {
        let mut best_arm = 0;
        let mut best_sample = f64::NEG_INFINITY;
        for (i, (&a, &b)) in self.bank.a.iter().zip(self.bank.b.iter()).enumerate() {
            let sample = f64_impl::beta_sample(a, b, rng);
            if sample > best_sample {
                best_sample = sample;
                best_arm = i;
            }
        }
        best_arm
    }

    /// Records a reward in [0, 1] for an arm.
    ///
    /// Updates: alpha += reward, beta += (1 - reward).
    /// If `decay < 1.0`, all alpha/beta are discounted first.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if reward is NaN, infinite, or outside [0, 1].
    ///
    /// # Panics
    ///
    /// Panics if `arm >= num_arms`.
    #[inline]
    pub fn update(&mut self, arm: usize, reward: f64) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(reward);
        if !(0.0..=1.0).contains(&reward) {
            return Err(nexus_stats_core::DataError::OutOfRange);
        }
        self.bank.check_arm(arm);
        if self.decay < 1.0 {
            // Decay toward the prior, not toward zero: an arm that is never
            // pulled forgets its evidence but keeps its prior, so its posterior
            // never collapses to a point mass (or a 0/0 draw).
            self.bank
                .decay_toward(self.decay, self.initial_alpha, self.initial_beta);
        }
        self.bank.record(arm, reward, 1.0 - reward);
        Ok(())
    }

    /// Posterior mean for an arm: alpha / (alpha + beta).
    #[inline]
    #[must_use]
    pub fn mean_reward(&self, arm: usize) -> f64 {
        self.bank.check_arm(arm);
        self.bank.a[arm] / (self.bank.a[arm] + self.bank.b[arm])
    }

    /// Number of arms.
    #[inline]
    #[must_use]
    pub fn num_arms(&self) -> usize {
        self.bank.arms()
    }

    /// Whether total pulls >= min_samples.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.bank.is_primed()
    }

    /// Returns the number of updates performed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.bank.total_pulls
    }

    /// Resets alpha/beta to initial priors.
    #[inline]
    pub fn reset(&mut self) {
        self.bank.reset(self.initial_alpha, self.initial_beta);
    }
}

impl ThompsonBetaBuilder {
    /// Sets the number of arms (required, >= 2).
    #[inline]
    #[must_use]
    pub fn arms(mut self, n: usize) -> Self {
        self.arms = Some(n);
        self
    }

    /// Sets the initial alpha prior (default: 1.0, must be > 0).
    #[inline]
    #[must_use]
    pub fn initial_alpha(mut self, a: f64) -> Self {
        self.initial_alpha = a;
        self
    }

    /// Sets the initial beta prior (default: 1.0, must be > 0).
    #[inline]
    #[must_use]
    pub fn initial_beta(mut self, b: f64) -> Self {
        self.initial_beta = b;
        self
    }

    /// Sets the decay factor (default: 1.0, in (0, 1]).
    #[inline]
    #[must_use]
    pub fn decay(mut self, d: f64) -> Self {
        self.decay = d;
        self
    }

    /// Sets the minimum samples before `is_primed()` returns true.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, n: u64) -> Self {
        self.min_samples = Some(n);
        self
    }

    /// Builds the bandit.
    #[inline]
    pub fn build(self) -> Result<ThompsonBeta, nexus_stats_core::ConfigError> {
        let arms = self
            .arms
            .ok_or(nexus_stats_core::ConfigError::Missing("arms"))?;
        if self.initial_alpha <= 0.0 || !self.initial_alpha.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "initial_alpha must be positive and finite",
            ));
        }
        if self.initial_beta <= 0.0 || !self.initial_beta.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "initial_beta must be positive and finite",
            ));
        }
        let decay = checked_decay(self.decay)?;
        let min_samples = self.min_samples.unwrap_or(arms as u64);
        Ok(ThompsonBeta {
            bank: ArmBank::new(arms, self.initial_alpha, self.initial_beta, min_samples)?,
            initial_alpha: self.initial_alpha,
            initial_beta: self.initial_beta,
            decay,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::learning::sampling::test_rng as make_rng;

    #[test]
    fn uniform_prior_explores() {
        let bandit = ThompsonBeta::builder().arms(3).build().unwrap();
        let mut rng = make_rng(42);
        let mut counts = [0u32; 3];
        for _ in 0..300 {
            counts[bandit.select(&mut rng)] += 1;
        }
        // With uniform prior, all arms should get some selections
        for (i, &c) in counts.iter().enumerate() {
            assert!(c > 10, "arm {i} only selected {c} times with uniform prior");
        }
    }

    #[test]
    fn converges_to_best() {
        let mut bandit = ThompsonBeta::builder().arms(3).build().unwrap();
        let mut rng = make_rng(42);

        for _ in 0..500 {
            let arm = bandit.select(&mut rng);
            let reward = if arm == 1 { 0.9 } else { 0.1 };
            bandit.update(arm, reward).unwrap();
        }

        assert!(
            bandit.mean_reward(1) > bandit.mean_reward(0),
            "arm 1 mean {} should exceed arm 0 mean {}",
            bandit.mean_reward(1),
            bandit.mean_reward(0),
        );
    }

    #[test]
    fn binary_rewards() {
        let mut bandit = ThompsonBeta::builder().arms(2).build().unwrap();
        for _ in 0..100 {
            bandit.update(0, 1.0).unwrap(); // always success
            bandit.update(1, 0.0).unwrap(); // always failure
        }
        // alpha[0] >> beta[0], alpha[1] << beta[1]
        assert!(bandit.mean_reward(0) > 0.9);
        assert!(bandit.mean_reward(1) < 0.1);
    }

    #[test]
    fn continuous_rewards() {
        let mut bandit = ThompsonBeta::builder().arms(2).build().unwrap();
        for _ in 0..200 {
            bandit.update(0, 0.7).unwrap();
            bandit.update(1, 0.3).unwrap();
        }
        assert!(
            (bandit.mean_reward(0) - 0.7).abs() < 0.1,
            "mean_reward(0) = {}",
            bandit.mean_reward(0)
        );
    }

    #[test]
    fn decay_adapts() {
        let mut bandit = ThompsonBeta::builder().arms(2).decay(0.95).build().unwrap();
        // Phase 1: arm 0 is best (50 pairs).
        for _ in 0..50 {
            bandit.update(0, 1.0).unwrap();
            bandit.update(1, 0.0).unwrap();
        }
        // Phase 2: arm 1 is best, but for only 30 pairs. Without decay arm 0
        // still leads (50/80 vs 30/80); with decay the old evidence is gone.
        for _ in 0..30 {
            bandit.update(0, 0.0).unwrap();
            bandit.update(1, 1.0).unwrap();
        }
        assert!(
            bandit.mean_reward(1) > bandit.mean_reward(0),
            "should adapt: arm0={}, arm1={}",
            bandit.mean_reward(0),
            bandit.mean_reward(1),
        );
    }

    #[test]
    fn reset_restores_prior() {
        let mut bandit = ThompsonBeta::builder()
            .arms(2)
            .initial_alpha(2.0)
            .initial_beta(3.0)
            .build()
            .unwrap();

        bandit.update(0, 1.0).unwrap();
        bandit.update(1, 0.0).unwrap();
        bandit.reset();

        assert_eq!(bandit.count(), 0);
        let expected_mean = 2.0 / (2.0 + 3.0);
        assert!(
            (bandit.mean_reward(0) - expected_mean).abs() < 1e-12,
            "mean after reset: {}",
            bandit.mean_reward(0)
        );
    }

    #[test]
    fn reward_out_of_range() {
        let mut bandit = ThompsonBeta::builder().arms(2).build().unwrap();
        assert!(bandit.update(0, -0.1).is_err());
        assert!(bandit.update(0, 1.1).is_err());
        assert!(bandit.update(0, f64::NAN).is_err());
        assert!(bandit.update(0, f64::INFINITY).is_err());
        assert_eq!(bandit.count(), 0);
    }

    #[test]
    fn builder_validation() {
        assert!(ThompsonBeta::builder().arms(1).build().is_err());
        assert!(
            ThompsonBeta::builder()
                .arms(2)
                .initial_alpha(0.0)
                .build()
                .is_err()
        );
        assert!(
            ThompsonBeta::builder()
                .arms(2)
                .initial_beta(-1.0)
                .build()
                .is_err()
        );
        assert!(ThompsonBeta::builder().arms(2).decay(0.0).build().is_err());
        assert!(ThompsonBeta::builder().arms(2).decay(1.5).build().is_err());
    }
}
