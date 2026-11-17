use super::arm_bank::{ArmBank, checked_decay};

/// Epsilon-greedy multi-armed bandit.
///
/// With probability `epsilon`, selects a uniformly random arm
/// (explore). Otherwise selects the arm with the highest mean
/// reward (exploit). Ties broken by lowest index.
///
/// Arms with zero pulls are selected first (round-robin, lowest
/// index priority) before the epsilon-greedy rule applies.
///
/// The simplest bandit algorithm. Useful as a baseline and when
/// operational simplicity matters more than convergence speed.
///
/// # Parameters
///
/// - `arms` — number of arms (>= 2)
/// - `epsilon` — exploration probability, in (0, 1)
/// - `decay` — exponential discount on counts/rewards (default: 1.0)
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::learning::EpsilonGreedy;
///
/// let mut bandit = EpsilonGreedy::builder()
///     .arms(3)
///     .epsilon(0.1)
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
pub struct EpsilonGreedy {
    /// Pull counts (`a`) and reward sums (`b`) per arm, plus the pull counter.
    bank: ArmBank,
    epsilon: f64,
    decay: f64,
}

/// Builder for [`EpsilonGreedy`].
#[derive(Debug, Clone)]
pub struct EpsilonGreedyBuilder {
    arms: Option<usize>,
    epsilon: Option<f64>,
    decay: f64,
    min_samples: Option<u64>,
}

impl EpsilonGreedy {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> EpsilonGreedyBuilder {
        EpsilonGreedyBuilder {
            arms: None,
            epsilon: None,
            decay: 1.0,
            min_samples: None,
        }
    }

    /// Selects an arm: random with probability epsilon, best mean otherwise.
    ///
    /// Unpulled arms are selected first (lowest index priority).
    /// `rng` must return a uniform sample in [0, 1).
    #[must_use]
    #[allow(clippy::float_cmp)]
    pub fn select(&self, rng: &mut impl FnMut() -> f64) -> usize {
        // Round-robin unpulled arms first
        for (i, &c) in self.bank.a.iter().enumerate() {
            if c == 0.0 {
                return i;
            }
        }

        let coin = rng();
        if coin < self.epsilon {
            // Explore: uniform random arm
            let r = rng();
            let idx = (r * self.bank.arms() as f64) as usize;
            // Clamp to valid range (r could be very close to 1.0)
            if idx >= self.bank.arms() {
                self.bank.arms() - 1
            } else {
                idx
            }
        } else {
            // Exploit: best mean reward
            let mut best_arm = 0;
            let mut best_mean = f64::NEG_INFINITY;
            for (i, (&r, &c)) in self.bank.b.iter().zip(self.bank.a.iter()).enumerate() {
                let mean = r / c;
                if mean > best_mean {
                    best_mean = mean;
                    best_arm = i;
                }
            }
            best_arm
        }
    }

    /// Records a reward for an arm.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if reward is NaN or infinite.
    ///
    /// # Panics
    ///
    /// Panics if `arm >= num_arms`.
    #[inline]
    pub fn update(&mut self, arm: usize, reward: f64) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(reward);
        self.bank.check_arm(arm);
        if self.decay < 1.0 {
            self.bank.decay(self.decay);
        }
        self.bank.record(arm, 1.0, reward);
        Ok(())
    }

    /// Mean reward for an arm, or `None` if never pulled.
    #[inline]
    #[must_use]
    #[allow(clippy::float_cmp)]
    pub fn mean_reward(&self, arm: usize) -> Option<f64> {
        self.bank.check_arm(arm);
        if self.bank.a[arm] == 0.0 {
            return None;
        }
        Some(self.bank.b[arm] / self.bank.a[arm])
    }

    /// Effective pull count for an arm (decayed).
    #[inline]
    #[must_use]
    pub fn pulls(&self, arm: usize) -> f64 {
        self.bank.check_arm(arm);
        self.bank.a[arm]
    }

    /// Number of arms.
    #[inline]
    #[must_use]
    pub fn num_arms(&self) -> usize {
        self.bank.arms()
    }

    /// Whether all arms have been pulled at least once
    /// and `count() >= min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.bank.is_primed() && self.bank.a.iter().all(|&c| c > 0.0)
    }

    /// Returns the number of updates performed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.bank.total_pulls
    }

    /// Resets all state, keeping configuration.
    #[inline]
    pub fn reset(&mut self) {
        self.bank.reset(0.0, 0.0);
    }
}

impl EpsilonGreedyBuilder {
    /// Sets the number of arms (required, >= 2).
    #[inline]
    #[must_use]
    pub fn arms(mut self, n: usize) -> Self {
        self.arms = Some(n);
        self
    }

    /// Sets the exploration probability (required, in (0, 1)).
    #[inline]
    #[must_use]
    pub fn epsilon(mut self, e: f64) -> Self {
        self.epsilon = Some(e);
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
    pub fn build(self) -> Result<EpsilonGreedy, nexus_stats_core::ConfigError> {
        let arms = self
            .arms
            .ok_or(nexus_stats_core::ConfigError::Missing("arms"))?;
        let epsilon = self
            .epsilon
            .ok_or(nexus_stats_core::ConfigError::Missing("epsilon"))?;
        if epsilon <= 0.0 || epsilon >= 1.0 || !epsilon.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "epsilon must be in (0, 1)",
            ));
        }
        let decay = checked_decay(self.decay)?;
        let min_samples = self.min_samples.unwrap_or(arms as u64);
        Ok(EpsilonGreedy {
            bank: ArmBank::new(arms, 0.0, 0.0, min_samples)?,
            epsilon,
            decay,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::learning::sampling::test_rng as make_rng;

    #[test]
    fn explore_all_first() {
        let mut bandit = EpsilonGreedy::builder()
            .arms(3)
            .epsilon(0.1)
            .build()
            .unwrap();
        let mut rng = make_rng(42);

        let a0 = bandit.select(&mut rng);
        bandit.update(a0, 0.5).unwrap();
        let a1 = bandit.select(&mut rng);
        assert_ne!(a1, a0);
        bandit.update(a1, 0.5).unwrap();
        let a2 = bandit.select(&mut rng);
        assert_ne!(a2, a0);
        assert_ne!(a2, a1);
    }

    #[test]
    fn pure_exploit() {
        let mut bandit = EpsilonGreedy::builder()
            .arms(3)
            .epsilon(0.01) // very low exploration
            .build()
            .unwrap();

        // Seed all arms
        bandit.update(0, 0.0).unwrap();
        bandit.update(1, 1.0).unwrap();
        bandit.update(2, 0.0).unwrap();

        let mut rng = make_rng(42);
        let mut best_count = 0u32;
        let trials = 500;
        for _ in 0..trials {
            let arm = bandit.select(&mut rng);
            if arm == 1 {
                best_count += 1;
            }
            bandit
                .update(arm, if arm == 1 { 1.0 } else { 0.0 })
                .unwrap();
        }

        assert!(
            best_count as f64 / trials as f64 > 0.9,
            "best arm fraction = {}",
            best_count as f64 / trials as f64
        );
    }

    #[test]
    fn explores_at_rate() {
        let epsilon = 0.3;
        let mut bandit = EpsilonGreedy::builder()
            .arms(2)
            .epsilon(epsilon)
            .build()
            .unwrap();

        // Seed both arms — arm 0 is clearly better
        bandit.update(0, 1.0).unwrap();
        bandit.update(1, 0.0).unwrap();

        let mut rng = make_rng(42);
        let mut explore_count = 0u32;
        let trials = 2000;
        for _ in 0..trials {
            let arm = bandit.select(&mut rng);
            if arm == 1 {
                explore_count += 1;
            }
            bandit
                .update(arm, if arm == 0 { 1.0 } else { 0.0 })
                .unwrap();
        }

        // Should explore ~epsilon/2 of the time (half of explores go to arm 1)
        let explore_rate = explore_count as f64 / trials as f64;
        assert!(
            explore_rate > 0.05 && explore_rate < 0.4,
            "explore_rate={explore_rate}, expected ~{}",
            epsilon / 2.0
        );
    }

    #[test]
    fn decay_adapts() {
        let mut bandit = EpsilonGreedy::builder()
            .arms(2)
            .epsilon(0.1)
            .decay(0.9)
            .build()
            .unwrap();
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
            bandit.mean_reward(1).unwrap() > bandit.mean_reward(0).unwrap(),
            "should adapt: arm0={:?}, arm1={:?}",
            bandit.mean_reward(0),
            bandit.mean_reward(1),
        );
    }

    #[test]
    fn reset_clears() {
        let mut bandit = EpsilonGreedy::builder()
            .arms(2)
            .epsilon(0.1)
            .build()
            .unwrap();
        bandit.update(0, 1.0).unwrap();
        bandit.reset();
        assert_eq!(bandit.count(), 0);
        assert_eq!(bandit.mean_reward(0), None);
    }

    #[test]
    fn nan_rejected() {
        let mut bandit = EpsilonGreedy::builder()
            .arms(2)
            .epsilon(0.1)
            .build()
            .unwrap();
        assert_eq!(
            bandit.update(0, f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
    }

    #[test]
    fn inf_rejected() {
        let mut bandit = EpsilonGreedy::builder()
            .arms(2)
            .epsilon(0.1)
            .build()
            .unwrap();
        assert_eq!(
            bandit.update(0, f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
    }

    #[test]
    fn builder_validation() {
        assert!(
            EpsilonGreedy::builder()
                .arms(1)
                .epsilon(0.1)
                .build()
                .is_err()
        );
        assert!(
            EpsilonGreedy::builder()
                .arms(2)
                .epsilon(0.0)
                .build()
                .is_err()
        );
        assert!(
            EpsilonGreedy::builder()
                .arms(2)
                .epsilon(1.0)
                .build()
                .is_err()
        );
        assert!(
            EpsilonGreedy::builder()
                .arms(2)
                .epsilon(-0.1)
                .build()
                .is_err()
        );
        assert!(
            EpsilonGreedy::builder()
                .arms(2)
                .epsilon(0.1)
                .decay(0.0)
                .build()
                .is_err()
        );
    }

    #[test]
    fn mean_reward_tracks() {
        let mut bandit = EpsilonGreedy::builder()
            .arms(2)
            .epsilon(0.1)
            .build()
            .unwrap();

        for _ in 0..100 {
            bandit.update(0, 0.8).unwrap();
            bandit.update(1, 0.2).unwrap();
        }

        let m0 = bandit.mean_reward(0).unwrap();
        let m1 = bandit.mean_reward(1).unwrap();
        assert!(
            (m0 - 0.8).abs() < 0.01,
            "mean_reward(0)={m0}, expected ~0.8"
        );
        assert!(
            (m1 - 0.2).abs() < 0.01,
            "mean_reward(1)={m1}, expected ~0.2"
        );
    }
}
