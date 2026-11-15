extern crate alloc;
use alloc::boxed::Box;
use alloc::vec;

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
    alphas: Box<[f64]>,
    betas: Box<[f64]>,
    initial_alpha: f64,
    initial_beta: f64,
    decay: f64,
    total_pulls: u64,
    num_arms: usize,
    min_samples: u64,
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
        for (i, (&a, &b)) in self.alphas.iter().zip(self.betas.iter()).enumerate() {
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
        if reward < 0.0 || reward > 1.0 {
            return Err(nexus_stats_core::DataError::Negative);
        }
        assert!(
            arm < self.num_arms,
            "arm {arm} >= num_arms {}",
            self.num_arms
        );

        if self.decay < 1.0 {
            let decay = self.decay;
            for (a, b) in self.alphas.iter_mut().zip(self.betas.iter_mut()) {
                *a *= decay;
                *b *= decay;
            }
        }

        self.alphas[arm] += reward;
        self.betas[arm] += 1.0 - reward;
        self.total_pulls += 1;
        Ok(())
    }

    /// Posterior mean for an arm: alpha / (alpha + beta).
    #[inline]
    #[must_use]
    pub fn mean_reward(&self, arm: usize) -> f64 {
        assert!(
            arm < self.num_arms,
            "arm {arm} >= num_arms {}",
            self.num_arms
        );
        self.alphas[arm] / (self.alphas[arm] + self.betas[arm])
    }

    /// Total pulls across all arms.
    #[inline]
    #[must_use]
    pub fn total_pulls(&self) -> u64 {
        self.total_pulls
    }

    /// Number of arms.
    #[inline]
    #[must_use]
    pub fn num_arms(&self) -> usize {
        self.num_arms
    }

    /// Whether total pulls >= min_samples.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.total_pulls >= self.min_samples
    }

    /// Returns the number of updates performed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total_pulls
    }

    /// Resets alpha/beta to initial priors.
    #[inline]
    pub fn reset(&mut self) {
        self.alphas.fill(self.initial_alpha);
        self.betas.fill(self.initial_beta);
        self.total_pulls = 0;
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
        if arms < 2 {
            return Err(nexus_stats_core::ConfigError::Invalid("arms must be >= 2"));
        }
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
        if self.decay <= 0.0 || self.decay > 1.0 || !self.decay.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "decay must be in (0, 1]",
            ));
        }
        let min_samples = self.min_samples.unwrap_or(arms as u64);
        Ok(ThompsonBeta {
            alphas: vec![self.initial_alpha; arms].into_boxed_slice(),
            betas: vec![self.initial_beta; arms].into_boxed_slice(),
            initial_alpha: self.initial_alpha,
            initial_beta: self.initial_beta,
            decay: self.decay,
            total_pulls: 0,
            num_arms: arms,
            min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_rng(seed: u64) -> impl FnMut() -> f64 {
        let mut state = seed;
        move || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) as f64 / (1u64 << 31) as f64
        }
    }

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

        // Phase 1: arm 0 is best
        for _ in 0..50 {
            bandit.update(0, 1.0).unwrap();
            bandit.update(1, 0.0).unwrap();
        }
        assert!(bandit.mean_reward(0) > bandit.mean_reward(1));

        // Phase 2: arm 1 is best
        for _ in 0..100 {
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

        assert_eq!(bandit.total_pulls(), 0);
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
        assert_eq!(bandit.total_pulls(), 0);
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
