extern crate alloc;
use alloc::boxed::Box;
use alloc::vec;

/// UCB1 multi-armed bandit.
///
/// Selects the arm maximizing `mean + c * sqrt(ln(N) / n_i)` where
/// `c` is the exploration constant, `N` is total effective pulls,
/// and `n_i` is the effective pull count for arm `i`. Arms with
/// zero pulls are selected first (lowest index priority).
///
/// Deterministic — no RNG needed for selection.
///
/// Auer, Cesa-Bianchi, Fischer (2002).
///
/// # Parameters
///
/// - `arms` — number of arms (>= 2)
/// - `exploration` — confidence scale `c` (default: sqrt(2) ≈ 1.414)
/// - `decay` — exponential discount on counts/rewards per update
///   (default: 1.0 = stationary). Set < 1.0 for non-stationary rewards.
///
/// # Reward scaling
///
/// UCB1's regret bound assumes rewards in [0, 1]. The exploration
/// constant `c` should be scaled for other ranges.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::learning::Ucb1;
///
/// let mut bandit = Ucb1::builder()
///     .arms(3)
///     .build()
///     .unwrap();
///
/// let arm = bandit.select();
/// bandit.update(arm, 1.0).unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct Ucb1 {
    counts: Box<[f64]>,
    rewards: Box<[f64]>,
    exploration: f64,
    decay: f64,
    total_pulls: u64,
    num_arms: usize,
    min_samples: u64,
}

/// Builder for [`Ucb1`].
#[derive(Debug, Clone)]
pub struct Ucb1Builder {
    arms: Option<usize>,
    exploration: f64,
    decay: f64,
    min_samples: Option<u64>,
}

impl Ucb1 {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> Ucb1Builder {
        let sqrt2 = nexus_stats_core::math::sqrt(2.0);
        Ucb1Builder {
            arms: None,
            exploration: sqrt2,
            decay: 1.0,
            min_samples: None,
        }
    }

    /// Selects the arm with the highest UCB score.
    ///
    /// Arms with zero pulls are returned first (lowest index).
    /// Ties among pulled arms are broken by lowest index.
    #[must_use]
    #[allow(clippy::float_cmp)]
    pub fn select(&self) -> usize {
        for (i, &c) in self.counts.iter().enumerate() {
            if c == 0.0 {
                return i;
            }
        }

        let total_eff: f64 = self.counts.iter().copied().sum();
        let ln_total = nexus_stats_core::math::ln(total_eff);
        let scaled_exp = self.exploration * nexus_stats_core::math::sqrt(ln_total);

        let mut best_arm = 0;
        let mut best_score = f64::NEG_INFINITY;
        for (i, (&r, &c)) in self.rewards.iter().zip(self.counts.iter()).enumerate() {
            let inv_c = 1.0 / c;
            let mean = r * inv_c;
            let bonus = scaled_exp * nexus_stats_core::math::sqrt(inv_c);
            let score = mean + bonus;
            if score > best_score {
                best_score = score;
                best_arm = i;
            }
        }
        best_arm
    }

    /// Records a reward for an arm.
    ///
    /// If `decay < 1.0`, all arm counts and rewards are multiplied
    /// by `decay` before incorporating the new observation.
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
        assert!(
            arm < self.num_arms,
            "arm {arm} >= num_arms {}",
            self.num_arms
        );

        if self.decay < 1.0 {
            let decay = self.decay;
            for (c, r) in self.counts.iter_mut().zip(self.rewards.iter_mut()) {
                *c *= decay;
                *r *= decay;
            }
        }

        self.counts[arm] += 1.0;
        self.rewards[arm] += reward;
        self.total_pulls += 1;
        Ok(())
    }

    /// Mean reward for an arm, or `None` if never pulled.
    #[inline]
    #[must_use]
    #[allow(clippy::float_cmp)]
    pub fn mean_reward(&self, arm: usize) -> Option<f64> {
        assert!(
            arm < self.num_arms,
            "arm {arm} >= num_arms {}",
            self.num_arms
        );
        if self.counts[arm] == 0.0 {
            return None;
        }
        Some(self.rewards[arm] / self.counts[arm])
    }

    /// Effective pull count for an arm (decayed).
    #[inline]
    #[must_use]
    pub fn pulls(&self, arm: usize) -> f64 {
        assert!(
            arm < self.num_arms,
            "arm {arm} >= num_arms {}",
            self.num_arms
        );
        self.counts[arm]
    }

    /// Total pulls across all arms (un-decayed counter).
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

    /// Whether all arms have been pulled at least once
    /// and `total_pulls >= min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.total_pulls >= self.min_samples && self.counts.iter().all(|&c| c > 0.0)
    }

    /// Returns the number of updates performed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total_pulls
    }

    /// Resets all state, keeping configuration.
    #[inline]
    pub fn reset(&mut self) {
        self.counts.fill(0.0);
        self.rewards.fill(0.0);
        self.total_pulls = 0;
    }
}

impl Ucb1Builder {
    /// Sets the number of arms (required, >= 2).
    #[inline]
    #[must_use]
    pub fn arms(mut self, n: usize) -> Self {
        self.arms = Some(n);
        self
    }

    /// Sets the exploration constant `c` (default: sqrt(2)).
    #[inline]
    #[must_use]
    pub fn exploration(mut self, c: f64) -> Self {
        self.exploration = c;
        self
    }

    /// Sets the decay factor for non-stationary rewards (default: 1.0).
    #[inline]
    #[must_use]
    pub fn decay(mut self, d: f64) -> Self {
        self.decay = d;
        self
    }

    /// Sets the minimum samples before `is_primed()` returns true (default: arms).
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, n: u64) -> Self {
        self.min_samples = Some(n);
        self
    }

    /// Builds the bandit.
    #[inline]
    pub fn build(self) -> Result<Ucb1, nexus_stats_core::ConfigError> {
        let arms = self
            .arms
            .ok_or(nexus_stats_core::ConfigError::Missing("arms"))?;
        if arms < 2 {
            return Err(nexus_stats_core::ConfigError::Invalid("arms must be >= 2"));
        }
        if self.exploration <= 0.0 || !self.exploration.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "exploration must be positive and finite",
            ));
        }
        if self.decay <= 0.0 || self.decay > 1.0 || !self.decay.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "decay must be in (0, 1]",
            ));
        }
        let min_samples = self.min_samples.unwrap_or(arms as u64);
        Ok(Ucb1 {
            counts: vec![0.0; arms].into_boxed_slice(),
            rewards: vec![0.0; arms].into_boxed_slice(),
            exploration: self.exploration,
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

    #[test]
    fn explore_all_first() {
        let mut bandit = Ucb1::builder().arms(3).build().unwrap();
        let a0 = bandit.select();
        bandit.update(a0, 0.5).unwrap();
        let a1 = bandit.select();
        assert_ne!(a1, a0);
        bandit.update(a1, 0.5).unwrap();
        let a2 = bandit.select();
        assert_ne!(a2, a0);
        assert_ne!(a2, a1);
    }

    #[test]
    fn exploits_best_arm() {
        let mut bandit = Ucb1::builder().arms(3).build().unwrap();
        // Seed all arms
        for i in 0..3 {
            bandit.update(i, if i == 1 { 1.0 } else { 0.0 }).unwrap();
        }
        // Arm 1 consistently best
        let mut counts = [0u64; 3];
        for _ in 0..200 {
            let arm = bandit.select();
            let reward = if arm == 1 { 1.0 } else { 0.0 };
            bandit.update(arm, reward).unwrap();
            counts[arm] += 1;
        }
        assert!(
            counts[1] > counts[0] && counts[1] > counts[2],
            "arm 1 should dominate: {counts:?}"
        );
    }

    #[test]
    fn exploration_decreases() {
        let mut bandit = Ucb1::builder().arms(2).build().unwrap();
        bandit.update(0, 0.8).unwrap();
        bandit.update(1, 0.2).unwrap();

        // UCB bonus for arm 1 after few pulls
        let early_bonus = {
            let total: f64 = bandit.counts.iter().sum();
            let ln_t = total.ln();
            bandit.exploration * (ln_t / bandit.counts[1]).sqrt()
        };

        for _ in 0..100 {
            let arm = bandit.select();
            bandit
                .update(arm, if arm == 0 { 0.8 } else { 0.2 })
                .unwrap();
        }

        let late_bonus = {
            let total: f64 = bandit.counts.iter().sum();
            let ln_t = total.ln();
            bandit.exploration * (ln_t / bandit.counts[1]).sqrt()
        };

        assert!(
            late_bonus < early_bonus,
            "bonus should decrease: early={early_bonus}, late={late_bonus}"
        );
    }

    #[test]
    fn decay_forgets() {
        let mut bandit = Ucb1::builder().arms(2).decay(0.95).build().unwrap();

        bandit.update(0, 1.0).unwrap();
        bandit.update(1, 0.0).unwrap();
        let initial_count = bandit.pulls(0);

        for _ in 0..20 {
            bandit.update(1, 0.0).unwrap();
        }

        assert!(
            bandit.pulls(0) < initial_count,
            "decayed count {} should be less than initial {}",
            bandit.pulls(0),
            initial_count
        );
    }

    #[test]
    fn decay_regime_shift() {
        let mut bandit = Ucb1::builder().arms(2).decay(0.9).build().unwrap();

        // Phase 1: arm 0 is best
        for _ in 0..50 {
            bandit.update(0, 1.0).unwrap();
            bandit.update(1, 0.0).unwrap();
        }
        assert!(
            bandit.mean_reward(0).unwrap() > bandit.mean_reward(1).unwrap(),
            "arm 0 should lead after phase 1"
        );

        // Phase 2: arm 1 is best
        for _ in 0..100 {
            bandit.update(0, 0.0).unwrap();
            bandit.update(1, 1.0).unwrap();
        }
        assert!(
            bandit.mean_reward(1).unwrap() > bandit.mean_reward(0).unwrap(),
            "arm 1 should lead after phase 2"
        );
    }

    #[test]
    fn reset_clears() {
        let mut bandit = Ucb1::builder().arms(3).build().unwrap();
        bandit.update(0, 1.0).unwrap();
        bandit.update(1, 0.5).unwrap();
        assert_eq!(bandit.total_pulls(), 2);

        bandit.reset();
        assert_eq!(bandit.total_pulls(), 0);
        assert_eq!(bandit.mean_reward(0), None);
        assert_eq!(bandit.mean_reward(1), None);
    }

    #[test]
    fn nan_rejected() {
        let mut bandit = Ucb1::builder().arms(2).build().unwrap();
        assert_eq!(
            bandit.update(0, f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(bandit.total_pulls(), 0);
    }

    #[test]
    fn inf_rejected() {
        let mut bandit = Ucb1::builder().arms(2).build().unwrap();
        assert_eq!(
            bandit.update(0, f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
    }

    #[test]
    fn builder_validation() {
        assert!(Ucb1::builder().arms(1).build().is_err());
        assert!(Ucb1::builder().arms(2).exploration(0.0).build().is_err());
        assert!(Ucb1::builder().arms(2).exploration(-1.0).build().is_err());
        assert!(Ucb1::builder().arms(2).decay(0.0).build().is_err());
        assert!(Ucb1::builder().arms(2).decay(1.1).build().is_err());
        assert!(Ucb1::builder().build().is_err()); // missing arms
    }
}
