extern crate alloc;
use alloc::boxed::Box;
use alloc::vec;

/// EXP3 adversarial bandit.
///
/// Exponential-weight algorithm for Exploration and Exploitation.
/// Unlike UCB1/Thompson which assume stochastic rewards, EXP3
/// makes no assumptions about how rewards are generated — they
/// can be adversarial.
///
/// Selection probability: `p_i = (1 - gamma) * w_i / sum(w) + gamma / K`
///
/// Weight update (log-space): `ln(w_i) += eta * reward / (K * p_i)`
///
/// Internally stores log-weights for numerical stability. No
/// overflow possible regardless of learning rate or horizon.
///
/// Auer, Cesa-Bianchi, Freund, Schapire (2002).
///
/// # Parameters
///
/// - `arms` — number of arms K (>= 2)
/// - `gamma` — exploration mixing rate, in (0, 1]. Higher = more uniform.
/// - `eta` — learning rate (default: gamma)
///
/// # Reward range
///
/// Rewards must be in [0, 1]. Normalize before feeding.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::learning::Exp3;
///
/// let mut bandit = Exp3::builder()
///     .arms(3)
///     .gamma(0.1)
///     .build()
///     .unwrap();
///
/// let mut s: u64 = 42;
/// let mut rng = || -> f64 {
///     s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
///     (s >> 33) as f64 / (1u64 << 31) as f64
/// };
/// let (arm, prob) = bandit.select(&mut rng);
/// bandit.update(arm, 0.8, prob).unwrap();
/// ```
///
/// `Exp3` is `!Sync`: `select` takes `&self` but writes an internal scratch
/// buffer, so share it across threads through `&mut` (or one per thread).
#[derive(Debug)]
pub struct Exp3 {
    log_weights: Box<[f64]>,
    scratch: core::cell::UnsafeCell<Box<[f64]>>,
    gamma: f64,
    eta: f64,
    total_pulls: u64,
    num_arms: usize,
    min_samples: u64,
}

impl Clone for Exp3 {
    fn clone(&self) -> Self {
        Self {
            log_weights: self.log_weights.clone(),
            scratch: core::cell::UnsafeCell::new(vec![0.0; self.num_arms].into_boxed_slice()),
            gamma: self.gamma,
            eta: self.eta,
            total_pulls: self.total_pulls,
            num_arms: self.num_arms,
            min_samples: self.min_samples,
        }
    }
}

/// Builder for [`Exp3`].
#[derive(Debug, Clone)]
pub struct Exp3Builder {
    arms: Option<usize>,
    gamma: Option<f64>,
    eta: Option<f64>,
    min_samples: Option<u64>,
}

impl Exp3 {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> Exp3Builder {
        Exp3Builder {
            arms: None,
            gamma: None,
            eta: None,
            min_samples: None,
        }
    }

    /// Samples an arm proportional to mixed weights.
    ///
    /// Returns `(arm_index, selection_probability)`. The caller
    /// must pass the probability back to `update()`.
    ///
    /// Uses log-sum-exp with a cached scratch buffer to avoid
    /// recomputing exp() values during CDF sampling.
    #[must_use]
    #[allow(clippy::suboptimal_flops)]
    pub fn select(&self, rng: &mut impl FnMut() -> f64) -> (usize, f64) {
        let k = self.num_arms as f64;
        let gamma = self.gamma;
        // Drawn before the scratch borrow below: `rng` is caller code, and
        // nothing of the caller's may run while that borrow is live.
        let u = rng();

        // SAFETY: `scratch` is touched only inside this method, the borrow
        // never escapes it, and no caller code runs while it is live (the
        // only callback, `rng`, was already drawn), so no second borrow of
        // the cell can be created. The `UnsafeCell` is why `Exp3` is `!Sync`.
        let scratch = unsafe { &mut *self.scratch.get() };

        let max_lw = self
            .log_weights
            .iter()
            .copied()
            .fold(f64::NEG_INFINITY, |a, b| if a > b { a } else { b });

        // Compute exp values into scratch, accumulate sum (K exp calls)
        let mut sum_exp = 0.0;
        for (s, &lw) in scratch.iter_mut().zip(self.log_weights.iter()) {
            *s = nexus_stats_core::math::exp(lw - max_lw);
            sum_exp += *s;
        }

        let scale = (1.0 - gamma) / sum_exp;
        let gamma_over_k = gamma / k;
        let mut cumulative = 0.0;

        // CDF sampling from cached exp values — no exp() calls
        for (i, &exp_w) in scratch.iter().enumerate() {
            let p_i = exp_w * scale + gamma_over_k;
            cumulative += p_i;
            if u < cumulative {
                return (i, p_i);
            }
        }

        let last = self.num_arms - 1;
        let p_last = scratch[last] * scale + gamma_over_k;
        (last, p_last)
    }

    /// Records a reward for the selected arm.
    ///
    /// `prob` is the selection probability returned by `select()`.
    /// Log-weight update: `ln(w_arm) += eta * reward / (K * prob)`.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if reward is NaN, infinite, or outside [0, 1],
    /// or if prob is NaN, infinite, or <= 0.
    ///
    /// # Panics
    ///
    /// Panics if `arm >= num_arms`.
    #[inline]
    pub fn update(
        &mut self,
        arm: usize,
        reward: f64,
        prob: f64,
    ) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(reward);
        if reward < 0.0 || reward > 1.0 {
            return Err(nexus_stats_core::DataError::Negative);
        }
        check_finite!(prob);
        if prob <= 0.0 {
            return Err(nexus_stats_core::DataError::Negative);
        }
        assert!(
            arm < self.num_arms,
            "arm {arm} >= num_arms {}",
            self.num_arms
        );

        let k = self.num_arms as f64;
        self.log_weights[arm] += self.eta * reward / (k * prob);
        self.total_pulls += 1;
        Ok(())
    }

    /// Writes the current probability distribution into `out`.
    ///
    /// # Panics
    ///
    /// Panics if `out.len() != num_arms`.
    #[allow(clippy::suboptimal_flops)]
    pub fn probabilities(&self, out: &mut [f64]) {
        assert_eq!(
            out.len(),
            self.num_arms,
            "output length {} != num_arms {}",
            out.len(),
            self.num_arms,
        );
        let k = self.num_arms as f64;
        let gamma = self.gamma;

        // Log-sum-exp: use output buffer as scratch for exp values
        let max_lw = self
            .log_weights
            .iter()
            .copied()
            .fold(f64::NEG_INFINITY, |a, b| if a > b { a } else { b });
        let mut sum_exp = 0.0;
        for (o, &lw) in out.iter_mut().zip(self.log_weights.iter()) {
            *o = nexus_stats_core::math::exp(lw - max_lw);
            sum_exp += *o;
        }
        let scale = (1.0 - gamma) / sum_exp;
        let gamma_over_k = gamma / k;
        for o in out.iter_mut() {
            *o = *o * scale + gamma_over_k;
        }
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

    /// Resets log-weights to uniform (all zero = equal weight).
    #[inline]
    pub fn reset(&mut self) {
        self.log_weights.fill(0.0);
        self.total_pulls = 0;
    }
}

impl Exp3Builder {
    /// Sets the number of arms (required, >= 2).
    #[inline]
    #[must_use]
    pub fn arms(mut self, n: usize) -> Self {
        self.arms = Some(n);
        self
    }

    /// Sets the exploration mixing rate (required, in (0, 1]).
    #[inline]
    #[must_use]
    pub fn gamma(mut self, g: f64) -> Self {
        self.gamma = Some(g);
        self
    }

    /// Sets the learning rate (default: gamma, must be > 0).
    #[inline]
    #[must_use]
    pub fn eta(mut self, e: f64) -> Self {
        self.eta = Some(e);
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
    pub fn build(self) -> Result<Exp3, nexus_stats_core::ConfigError> {
        let arms = self
            .arms
            .ok_or(nexus_stats_core::ConfigError::Missing("arms"))?;
        let gamma = self
            .gamma
            .ok_or(nexus_stats_core::ConfigError::Missing("gamma"))?;
        if arms < 2 {
            return Err(nexus_stats_core::ConfigError::Invalid("arms must be >= 2"));
        }
        if gamma <= 0.0 || gamma > 1.0 || !gamma.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "gamma must be in (0, 1]",
            ));
        }
        let eta = self.eta.unwrap_or(gamma);
        if eta <= 0.0 || !eta.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "eta must be positive and finite",
            ));
        }
        let min_samples = self.min_samples.unwrap_or(arms as u64);
        Ok(Exp3 {
            log_weights: vec![0.0; arms].into_boxed_slice(),
            scratch: core::cell::UnsafeCell::new(vec![0.0; arms].into_boxed_slice()),
            gamma,
            eta,
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
    fn uniform_start() {
        let bandit = Exp3::builder().arms(3).gamma(0.1).build().unwrap();

        let mut probs = vec![0.0; 3];
        bandit.probabilities(&mut probs);
        let expected = 1.0 / 3.0;
        for (i, &p) in probs.iter().enumerate() {
            assert!(
                (p - expected).abs() < 1e-10,
                "prob[{i}]={p}, expected {expected}"
            );
        }
    }

    #[test]
    fn adapts_to_best() {
        let mut bandit = Exp3::builder().arms(3).gamma(0.1).build().unwrap();
        let mut rng = make_rng(42);

        for _ in 0..500 {
            let (arm, prob) = bandit.select(&mut rng);
            let reward = if arm == 1 { 0.9 } else { 0.1 };
            bandit.update(arm, reward, prob).unwrap();
        }

        let mut probs = vec![0.0; 3];
        bandit.probabilities(&mut probs);
        assert!(
            probs[1] > probs[0] && probs[1] > probs[2],
            "arm 1 should have highest prob: {probs:?}"
        );
    }

    #[test]
    fn adversarial_robustness() {
        let mut bandit = Exp3::builder().arms(2).gamma(0.2).build().unwrap();
        let mut rng = make_rng(42);

        // Alternating which arm pays
        for round in 0..200 {
            let (arm, prob) = bandit.select(&mut rng);
            let best_arm = round % 2;
            let reward = if arm == best_arm { 1.0 } else { 0.0 };
            bandit.update(arm, reward, prob).unwrap();
        }

        // Both arms should maintain reasonable probability
        let mut probs = vec![0.0; 2];
        bandit.probabilities(&mut probs);
        assert!(probs[0] > 0.1, "arm 0 prob={}", probs[0]);
        assert!(probs[1] > 0.1, "arm 1 prob={}", probs[1]);
    }

    #[test]
    fn prob_sums_to_one() {
        let mut bandit = Exp3::builder().arms(4).gamma(0.15).build().unwrap();
        let mut rng = make_rng(42);

        for _ in 0..50 {
            let (arm, prob) = bandit.select(&mut rng);
            bandit.update(arm, 0.5, prob).unwrap();
        }

        let mut probs = vec![0.0; 4];
        bandit.probabilities(&mut probs);
        let sum: f64 = probs.iter().sum();
        assert!((sum - 1.0).abs() < 1e-10, "prob sum={sum}, expected 1.0");
    }

    #[test]
    fn log_weights_no_overflow() {
        let mut bandit = Exp3::builder()
            .arms(2)
            .gamma(0.1)
            .eta(10.0) // aggressive learning rate
            .build()
            .unwrap();

        // Many updates that would overflow raw weights
        for _ in 0..10_000 {
            bandit.update(0, 1.0, 0.05).unwrap();
        }

        // Log-weights stay finite, probabilities still valid
        assert!(
            bandit.log_weights.iter().all(|w| w.is_finite()),
            "log_weights should be finite: {:?}",
            &*bandit.log_weights,
        );
        let mut probs = vec![0.0; 2];
        bandit.probabilities(&mut probs);
        let sum: f64 = probs.iter().sum();
        assert!((sum - 1.0).abs() < 1e-10, "prob sum={sum}");
    }

    #[test]
    fn reward_out_of_range() {
        let mut bandit = Exp3::builder().arms(2).gamma(0.1).build().unwrap();
        assert!(bandit.update(0, -0.1, 0.5).is_err());
        assert!(bandit.update(0, 1.1, 0.5).is_err());
        assert!(bandit.update(0, 0.5, 0.0).is_err());
        assert!(bandit.update(0, 0.5, -0.1).is_err());
        assert!(bandit.update(0, f64::NAN, 0.5).is_err());
        assert_eq!(bandit.total_pulls(), 0);
    }

    #[test]
    fn reset_clears() {
        let mut bandit = Exp3::builder().arms(3).gamma(0.1).build().unwrap();

        bandit.update(0, 0.9, 0.5).unwrap();
        bandit.update(1, 0.1, 0.4).unwrap();
        bandit.reset();

        assert_eq!(bandit.total_pulls(), 0);
        let mut probs = vec![0.0; 3];
        bandit.probabilities(&mut probs);
        let expected = 1.0 / 3.0;
        for &p in &probs {
            assert!((p - expected).abs() < 1e-10);
        }
    }

    #[test]
    fn builder_validation() {
        assert!(Exp3::builder().arms(1).gamma(0.1).build().is_err());
        assert!(Exp3::builder().arms(2).gamma(0.0).build().is_err());
        assert!(Exp3::builder().arms(2).gamma(1.5).build().is_err());
        assert!(Exp3::builder().arms(2).gamma(0.1).eta(0.0).build().is_err());
        assert!(Exp3::builder().arms(2).build().is_err()); // missing gamma
    }
}
