use super::arm_bank::{ArmBank, checked_decay};
use super::sampling::f64_impl;

/// Thompson Sampling with Gamma prior.
///
/// Each arm maintains Gamma(shape, rate) parameters. Selection
/// samples from each arm's Gamma posterior and picks the highest
/// sample. For positive continuous rewards where Beta (bounded
/// [0, 1]) is too restrictive.
///
/// Conjugate update: shape += reward, rate += 1.
/// Posterior mean: shape / rate (approximates sample mean).
///
/// # Parameters
///
/// - `arms` — number of arms (>= 2)
/// - `initial_shape` — prior shape for all arms (default: 1.0)
/// - `initial_rate` — prior rate for all arms (default: 1.0)
/// - `decay` — multiplicative discount on shape, rate per update (default: 1.0)
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::learning::ThompsonGamma;
///
/// let mut bandit = ThompsonGamma::builder()
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
/// bandit.update(arm, 2.5).unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct ThompsonGamma {
    /// Posterior parameters per arm (`a` = shapes, `b` = rates), plus the pull counter.
    bank: ArmBank,
    initial_shape: f64,
    initial_rate: f64,
    decay: f64,
}

/// Builder for [`ThompsonGamma`].
#[derive(Debug, Clone)]
pub struct ThompsonGammaBuilder {
    arms: Option<usize>,
    initial_shape: f64,
    initial_rate: f64,
    decay: f64,
    min_samples: Option<u64>,
}

impl ThompsonGamma {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> ThompsonGammaBuilder {
        ThompsonGammaBuilder {
            arms: None,
            initial_shape: 1.0,
            initial_rate: 1.0,
            decay: 1.0,
            min_samples: None,
        }
    }

    /// Samples from each arm's Gamma posterior, returns the arm
    /// with the highest sample.
    ///
    /// `rng` must return independent uniform samples in [0, 1).
    #[must_use]
    pub fn select(&self, rng: &mut impl FnMut() -> f64) -> usize {
        let mut best_arm = 0;
        let mut best_sample = f64::NEG_INFINITY;
        for (i, (&shape, &rate)) in self.bank.a.iter().zip(self.bank.b.iter()).enumerate() {
            let g = f64_impl::gamma_sample(shape, rng);
            let sample = g / rate;
            if sample > best_sample {
                best_sample = sample;
                best_arm = i;
            }
        }
        best_arm
    }

    /// Records a positive reward for an arm.
    ///
    /// Updates: shape += reward, rate += 1.
    /// If `decay < 1.0`, all shape/rate are discounted first.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if reward is NaN, infinite, or <= 0.
    ///
    /// # Panics
    ///
    /// Panics if `arm >= num_arms`.
    #[inline]
    pub fn update(&mut self, arm: usize, reward: f64) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(reward);
        if reward <= 0.0 {
            return Err(nexus_stats_core::DataError::OutOfRange);
        }
        self.bank.check_arm(arm);
        if self.decay < 1.0 {
            // Decay toward the prior, not toward zero: an arm that is never
            // pulled forgets its evidence but keeps its prior, so its posterior
            // never collapses to a point mass (or a 0/0 draw).
            self.bank
                .decay_toward(self.decay, self.initial_shape, self.initial_rate);
        }
        self.bank.record(arm, reward, 1.0);
        Ok(())
    }

    /// Posterior mean for an arm: shape / rate.
    #[inline]
    #[must_use]
    pub fn mean_reward(&self, arm: usize) -> f64 {
        self.bank.check_arm(arm);
        self.bank.a[arm] / self.bank.b[arm]
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

    /// Resets shape/rate to initial priors.
    #[inline]
    pub fn reset(&mut self) {
        self.bank.reset(self.initial_shape, self.initial_rate);
    }
}

impl ThompsonGammaBuilder {
    /// Sets the number of arms (required, >= 2).
    #[inline]
    #[must_use]
    pub fn arms(mut self, n: usize) -> Self {
        self.arms = Some(n);
        self
    }

    /// Sets the initial shape prior (default: 1.0, must be > 0).
    #[inline]
    #[must_use]
    pub fn initial_shape(mut self, s: f64) -> Self {
        self.initial_shape = s;
        self
    }

    /// Sets the initial rate prior (default: 1.0, must be > 0).
    #[inline]
    #[must_use]
    pub fn initial_rate(mut self, r: f64) -> Self {
        self.initial_rate = r;
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
    pub fn build(self) -> Result<ThompsonGamma, nexus_stats_core::ConfigError> {
        let arms = self
            .arms
            .ok_or(nexus_stats_core::ConfigError::Missing("arms"))?;
        if self.initial_shape <= 0.0 || !self.initial_shape.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "initial_shape must be positive and finite",
            ));
        }
        if self.initial_rate <= 0.0 || !self.initial_rate.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "initial_rate must be positive and finite",
            ));
        }
        let decay = checked_decay(self.decay)?;
        let min_samples = self.min_samples.unwrap_or(arms as u64);
        Ok(ThompsonGamma {
            bank: ArmBank::new(arms, self.initial_shape, self.initial_rate, min_samples)?,
            initial_shape: self.initial_shape,
            initial_rate: self.initial_rate,
            decay,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::learning::sampling::test_rng as make_rng;

    #[test]
    fn explores_with_weak_prior() {
        let bandit = ThompsonGamma::builder().arms(3).build().unwrap();
        let mut rng = make_rng(42);
        let mut counts = [0u32; 3];
        for _ in 0..300 {
            counts[bandit.select(&mut rng)] += 1;
        }
        for (i, &c) in counts.iter().enumerate() {
            assert!(c > 10, "arm {i} only selected {c} times");
        }
    }

    #[test]
    fn converges_to_best() {
        let mut bandit = ThompsonGamma::builder().arms(3).build().unwrap();
        let mut rng = make_rng(42);

        for _ in 0..500 {
            let arm = bandit.select(&mut rng);
            let reward = if arm == 1 { 5.0 } else { 1.0 };
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
    fn mean_reward_tracks() {
        let mut bandit = ThompsonGamma::builder().arms(2).build().unwrap();
        for _ in 0..200 {
            bandit.update(0, 3.0).unwrap();
            bandit.update(1, 7.0).unwrap();
        }
        // Posterior mean = (initial_shape + sum_rewards) / (initial_rate + n)
        // Arm 0: (1 + 600) / (1 + 200) = 601/201 ≈ 2.99
        // Arm 1: (1 + 1400) / (1 + 200) = 1401/201 ≈ 6.97
        let m0 = bandit.mean_reward(0);
        let m1 = bandit.mean_reward(1);
        assert!((m0 - 3.0).abs() < 0.1, "m0={m0}, expected ~3.0");
        assert!((m1 - 7.0).abs() < 0.1, "m1={m1}, expected ~7.0");
    }

    #[test]
    fn decay_adapts() {
        let mut bandit = ThompsonGamma::builder()
            .arms(2)
            .decay(0.95)
            .build()
            .unwrap();
        // Phase 1: arm 0 is best (50 pairs).
        for _ in 0..50 {
            bandit.update(0, 1.0).unwrap();
            bandit.update(1, 0.1).unwrap();
        }
        // Phase 2: arm 1 is best, for only 30 pairs. Without decay arm 0
        // still leads on total reward; with decay the old evidence is gone.
        for _ in 0..30 {
            bandit.update(0, 0.1).unwrap();
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
    fn negative_reward_rejected() {
        let mut bandit = ThompsonGamma::builder().arms(2).build().unwrap();
        assert!(bandit.update(0, -1.0).is_err());
        assert!(bandit.update(0, 0.0).is_err());
        assert_eq!(bandit.count(), 0);
    }

    #[test]
    fn reset_restores_prior() {
        let mut bandit = ThompsonGamma::builder()
            .arms(2)
            .initial_shape(2.0)
            .initial_rate(3.0)
            .build()
            .unwrap();

        bandit.update(0, 5.0).unwrap();
        bandit.reset();

        assert_eq!(bandit.count(), 0);
        let expected = 2.0 / 3.0;
        assert!(
            (bandit.mean_reward(0) - expected).abs() < 1e-12,
            "mean after reset: {}",
            bandit.mean_reward(0),
        );
    }

    #[test]
    fn nan_inf_rejected() {
        let mut bandit = ThompsonGamma::builder().arms(2).build().unwrap();
        assert_eq!(
            bandit.update(0, f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            bandit.update(0, f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
    }

    #[test]
    fn builder_validation() {
        assert!(ThompsonGamma::builder().arms(1).build().is_err());
        assert!(
            ThompsonGamma::builder()
                .arms(2)
                .initial_shape(0.0)
                .build()
                .is_err()
        );
        assert!(
            ThompsonGamma::builder()
                .arms(2)
                .initial_rate(-1.0)
                .build()
                .is_err()
        );
        assert!(ThompsonGamma::builder().arms(2).decay(0.0).build().is_err());
    }
}
