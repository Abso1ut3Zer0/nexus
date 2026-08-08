extern crate alloc;
use alloc::boxed::Box;
use nexus_stats_core::math::{exp, ln, ln_gamma};

use crate::simd_math;

// Precomputed per-r constants; valid because suf_count[r] == r.
#[derive(Debug, Clone)]
struct Precomputed {
    lng_base: Box<[f64]>,
    mu_a: Box<[f64]>,
    mu_b: Box<[f64]>,
    beta_c: Box<[f64]>,
    nu_d: Box<[f64]>,
    alpha: Box<[f64]>,
}

/// Bayesian Online Change Point Detection (Adams & MacKay 2007).
///
/// Maintains a truncated run-length posterior using a Gaussian
/// observation model with Normal-Inverse-Gamma conjugate prior.
/// Predictive distribution is Student-t. All posterior arithmetic
/// in log-space to prevent underflow.
///
/// O(W) per update where W = `max_run_length`.
///
/// # Examples
///
/// ```
/// use nexus_stats_detection::detection::BocpdF64;
///
/// let mut bocpd = BocpdF64::builder()
///     .max_run_length(200)
///     .hazard_lambda(100.0)
///     .build()
///     .unwrap();
///
/// // Stable signal
/// for i in 0..200 {
///     let cp = bocpd.update(50.0 + (i % 3) as f64).unwrap();
///     // cp probability stays low
/// }
/// let cp = bocpd.change_point_probability().unwrap();
/// assert!(cp < 0.3);
/// ```
#[derive(Debug, Clone)]
pub struct BocpdF64 {
    log_posterior: Box<[f64]>,
    suf_count: Box<[u64]>,
    suf_mean: Box<[f64]>,
    suf_sum_sq: Box<[f64]>,
    scratch: Box<[f64]>,
    scratch2: Box<[f64]>,
    pre: Precomputed,

    max_run_length: usize,
    log_hazard: f64,
    log_1m_hazard: f64,

    prior_mu: f64,
    prior_beta: f64,

    active: usize,
    count: u64,
    min_samples: u64,
}

/// Builder for [`BocpdF64`].
#[derive(Debug, Clone)]
pub struct BocpdF64Builder {
    max_run_length: Option<usize>,
    hazard_lambda: Option<f64>,
    prior_mu: f64,
    prior_kappa: f64,
    prior_alpha: f64,
    prior_beta: f64,
    min_samples: u64,
}

fn logsumexp(a: f64, b: f64) -> f64 {
    let max = a.max(b);
    if max == f64::NEG_INFINITY {
        return f64::NEG_INFINITY;
    }
    max + ln(exp(a - max) + exp(b - max))
}

fn logsumexp_slice(values: &[f64]) -> f64 {
    let max = values.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    if max == f64::NEG_INFINITY {
        return f64::NEG_INFINITY;
    }
    max + ln(values.iter().map(|&v| exp(v - max)).sum::<f64>())
}

impl BocpdF64 {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> BocpdF64Builder {
        BocpdF64Builder {
            max_run_length: Option::None,
            hazard_lambda: Option::None,
            prior_mu: 0.0,
            prior_kappa: 1.0,
            prior_alpha: 1.0,
            prior_beta: 1.0,
            min_samples: 1,
        }
    }

    /// Feeds a sample. Returns the change-point probability (posterior
    /// mass at run length 0) once primed, `None` during warmup.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    pub fn update(&mut self, sample: f64) -> Result<Option<f64>, nexus_stats_core::DataError> {
        check_finite!(sample);

        if self.active == 0 {
            self.log_posterior[0] = 0.0;
            self.suf_count[0] = 0;
            self.suf_mean[0] = 0.0;
            self.suf_sum_sq[0] = 0.0;
            self.active = 1;
        }

        // Step 1: three-pass log predictive + CP mass.
        //
        // Pass 1 — scalar math only (no transcendentals): compute the two
        // ln arguments a[r] and b[r] into scratch/scratch2.
        // Pass 2 — tight ln loop: ln(a[r]) and ln(b[r]) in-place. Consecutive
        // independent calls give the OOO engine maximum ILP.
        // Pass 3 — combine with table lookups, find CP mass max.
        let cp_terms;
        #[allow(clippy::suboptimal_flops)]
        {
            // Pass 1: a[r] = nu_d*beta_n, b[r] = a + dx^2.
            // SAFETY: r < self.active <= self.max_run_length + 1.
            // All arrays allocated with capacity max_run_length + 1.
            // Raw pointers hoisted outside loop so LLVM sees them as
            // loop-invariant and can auto-vectorize (writes through &mut self
            // force base pointer reloads otherwise).
            unsafe {
                let p_mu_a = self.pre.mu_a.as_ptr();
                let p_mu_b = self.pre.mu_b.as_ptr();
                let p_beta_c = self.pre.beta_c.as_ptr();
                let p_nu_d = self.pre.nu_d.as_ptr();
                let p_sm = self.suf_mean.as_ptr();
                let p_ssq = self.suf_sum_sq.as_ptr();
                let p_sc = self.scratch.as_mut_ptr();
                let p_sc2 = self.scratch2.as_mut_ptr();
                let prior_mu = self.prior_mu;
                let prior_beta = self.prior_beta;

                for r in 0..self.active {
                    let sm = *p_sm.add(r);
                    let mu_n = *p_mu_a.add(r) + *p_mu_b.add(r) * sm;
                    let diff = sm - prior_mu;
                    let beta_n = prior_beta + *p_ssq.add(r) * 0.5 + *p_beta_c.add(r) * diff * diff;
                    let a = *p_nu_d.add(r) * beta_n;
                    let dx = sample - mu_n;
                    *p_sc.add(r) = a;
                    *p_sc2.add(r) = a + dx * dx;
                }
            }

            // Pass 2: ln in-place (SIMD when available).
            simd_math::ln_inplace(&mut self.scratch[..self.active]);
            simd_math::ln_inplace(&mut self.scratch2[..self.active]);

            // Pass 3: combine and find CP mass max.
            let mut max_cp_term = f64::NEG_INFINITY;
            // SAFETY: same invariant as Pass 1.
            unsafe {
                let p_alpha = self.pre.alpha.as_ptr();
                let p_lng = self.pre.lng_base.as_ptr();
                let p_sc = self.scratch.as_mut_ptr();
                let p_sc2 = self.scratch2.as_ptr();
                let p_lp = self.log_posterior.as_ptr();
                let log_hazard = self.log_hazard;

                for r in 0..self.active {
                    let alpha_r = *p_alpha.add(r);
                    let log_pred =
                        *p_lng.add(r) + alpha_r * *p_sc.add(r) - (alpha_r + 0.5) * *p_sc2.add(r);

                    *p_sc.add(r) = log_pred;

                    let term = *p_lp.add(r) + log_pred + log_hazard;
                    if term > max_cp_term {
                        max_cp_term = term;
                    }
                }
            }

            // CP mass: exp-sum (SIMD when available).
            // Reuse scratch2 for the terms since pass 2 is done with it.
            cp_terms = if max_cp_term == f64::NEG_INFINITY {
                f64::NEG_INFINITY
            } else {
                // SAFETY: same invariant as Pass 1.
                unsafe {
                    let p_lp = self.log_posterior.as_ptr();
                    let p_sc = self.scratch.as_ptr();
                    let p_sc2 = self.scratch2.as_mut_ptr();
                    let log_hazard = self.log_hazard;

                    for r in 0..self.active {
                        *p_sc2.add(r) = *p_lp.add(r) + *p_sc.add(r) + log_hazard;
                    }
                }
                let sum = simd_math::exp_sum(&self.scratch2[..self.active], max_cp_term);
                max_cp_term + ln(sum)
            };
        }

        // Step 2b: growth probabilities (reverse to avoid overwrite of log_pred)
        let cap = self.max_run_length;
        if self.active < cap + 1 {
            for r in (0..self.active).rev() {
                self.scratch[r + 1] = self.log_posterior[r] + self.scratch[r] + self.log_1m_hazard;
            }
        } else {
            let folded = logsumexp(
                self.log_posterior[cap - 1] + self.scratch[cap - 1] + self.log_1m_hazard,
                self.log_posterior[cap] + self.scratch[cap] + self.log_1m_hazard,
            );
            self.scratch[cap] = folded;
            for r in (0..(cap - 1)).rev() {
                self.scratch[r + 1] = self.log_posterior[r] + self.scratch[r] + self.log_1m_hazard;
            }
        }

        // Set CP mass at r=0
        self.scratch[0] = cp_terms;

        // Step 3: normalize
        let new_active = if self.active < cap + 1 {
            self.active + 1
        } else {
            cap + 1
        };
        let total = logsumexp_slice(&self.scratch[..new_active]);
        for r in 0..new_active {
            self.scratch[r] -= total;
        }

        // Step 4: copy scratch → log_posterior
        self.log_posterior[..new_active].copy_from_slice(&self.scratch[..new_active]);

        // Step 5: update sufficient stats (reverse to avoid overwrite)
        let suf_limit = if self.active < cap + 1 {
            self.active
        } else {
            cap
        };
        for r in (0..suf_limit).rev() {
            self.suf_count[r + 1] = self.suf_count[r];
            self.suf_mean[r + 1] = self.suf_mean[r];
            self.suf_sum_sq[r + 1] = self.suf_sum_sq[r];

            let n = self.suf_count[r + 1] + 1;
            let delta = sample - self.suf_mean[r + 1];
            self.suf_mean[r + 1] += delta / n as f64;
            self.suf_sum_sq[r + 1] += delta * (sample - self.suf_mean[r + 1]);
            self.suf_count[r + 1] = n;
        }

        // Initialize r=0 with empty stats (new run)
        self.suf_count[0] = 0;
        self.suf_mean[0] = 0.0;
        self.suf_sum_sq[0] = 0.0;

        self.active = new_active;
        self.count += 1;

        if self.count < self.min_samples {
            Ok(Option::None)
        } else {
            Ok(Option::Some(exp(self.log_posterior[0])))
        }
    }

    /// Change-point probability: posterior mass at run length 0.
    ///
    /// Returns `None` if not primed.
    #[inline]
    #[must_use]
    pub fn change_point_probability(&self) -> Option<f64> {
        if !self.is_primed() {
            return Option::None;
        }
        Option::Some(exp(self.log_posterior[0]))
    }

    /// MAP (most probable) run length.
    ///
    /// Returns `None` if not primed.
    #[must_use]
    pub fn map_run_length(&self) -> Option<usize> {
        if !self.is_primed() {
            return Option::None;
        }
        let mut best_r = 0;
        let mut best_val = f64::NEG_INFINITY;
        for r in 0..self.active {
            if self.log_posterior[r] > best_val {
                best_val = self.log_posterior[r];
                best_r = r;
            }
        }
        Option::Some(best_r)
    }

    /// Expected (mean) run length.
    ///
    /// Returns `None` if not primed.
    #[must_use]
    pub fn mean_run_length(&self) -> Option<f64> {
        if !self.is_primed() {
            return Option::None;
        }
        let mut mean = 0.0;
        for r in 0..self.active {
            mean += r as f64 * exp(self.log_posterior[r]);
        }
        Option::Some(mean)
    }

    /// Raw log-posterior over active run lengths.
    ///
    /// Returns `None` if not primed.
    #[must_use]
    pub fn run_length_posterior(&self) -> Option<&[f64]> {
        if !self.is_primed() {
            return Option::None;
        }
        Option::Some(&self.log_posterior[..self.active])
    }

    /// Maximum run length (window size W).
    #[inline]
    #[must_use]
    pub fn max_run_length(&self) -> usize {
        self.max_run_length
    }

    /// Hazard lambda (expected samples between change points).
    #[inline]
    #[must_use]
    pub fn hazard_lambda(&self) -> f64 {
        1.0 / exp(self.log_hazard)
    }

    /// Total samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough samples have been observed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets all state. Configuration preserved.
    pub fn reset(&mut self) {
        for v in &mut *self.log_posterior {
            *v = f64::NEG_INFINITY;
        }
        for v in &mut *self.suf_count {
            *v = 0;
        }
        for v in &mut *self.suf_mean {
            *v = 0.0;
        }
        for v in &mut *self.suf_sum_sq {
            *v = 0.0;
        }
        self.active = 0;
        self.count = 0;
    }
}

impl BocpdF64Builder {
    /// Maximum run length / window size (required, >= 10).
    #[inline]
    #[must_use]
    pub fn max_run_length(mut self, w: usize) -> Self {
        self.max_run_length = Option::Some(w);
        self
    }

    /// Expected samples between change points (required, > 1.0).
    #[inline]
    #[must_use]
    pub fn hazard_lambda(mut self, lambda: f64) -> Self {
        self.hazard_lambda = Option::Some(lambda);
        self
    }

    /// Prior mean (default: 0.0).
    #[inline]
    #[must_use]
    pub fn prior_mu(mut self, mu: f64) -> Self {
        self.prior_mu = mu;
        self
    }

    /// Prior precision scaling (default: 1.0, must be > 0).
    #[inline]
    #[must_use]
    pub fn prior_kappa(mut self, kappa: f64) -> Self {
        self.prior_kappa = kappa;
        self
    }

    /// Prior shape for variance (default: 1.0, must be > 0).
    #[inline]
    #[must_use]
    pub fn prior_alpha(mut self, alpha: f64) -> Self {
        self.prior_alpha = alpha;
        self
    }

    /// Prior scale for variance (default: 1.0, must be > 0).
    #[inline]
    #[must_use]
    pub fn prior_beta(mut self, beta: f64) -> Self {
        self.prior_beta = beta;
        self
    }

    /// Minimum samples before output is produced (default: 1).
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, n: u64) -> Self {
        self.min_samples = n;
        self
    }

    /// Builds the BOCPD detector.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if required fields are missing, max_run_length < 10,
    /// hazard_lambda <= 1.0, or prior parameters are non-positive.
    pub fn build(self) -> Result<BocpdF64, nexus_stats_core::ConfigError> {
        let max_run_length = self
            .max_run_length
            .ok_or(nexus_stats_core::ConfigError::Missing("max_run_length"))?;
        if max_run_length < 10 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "max_run_length must be >= 10",
            ));
        }

        let lambda = self
            .hazard_lambda
            .ok_or(nexus_stats_core::ConfigError::Missing("hazard_lambda"))?;
        if !lambda.is_finite() || lambda <= 1.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "hazard_lambda must be finite and > 1.0",
            ));
        }

        if self.prior_kappa <= 0.0 || !self.prior_kappa.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "prior_kappa must be finite and > 0",
            ));
        }
        if self.prior_alpha <= 0.0 || !self.prior_alpha.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "prior_alpha must be finite and > 0",
            ));
        }
        if self.prior_beta <= 0.0 || !self.prior_beta.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "prior_beta must be finite and > 0",
            ));
        }

        let size = max_run_length + 1;
        let h = 1.0 / lambda;

        let pre = {
            let pa = self.prior_alpha;
            let pk = self.prior_kappa;
            let pm = self.prior_mu;
            let half_ln_pi = 0.5 * ln(core::f64::consts::PI);

            let mut lng_base = alloc::vec![0.0f64; size];
            let mut mu_a = alloc::vec![0.0f64; size];
            let mut mu_b = alloc::vec![0.0f64; size];
            let mut beta_c = alloc::vec![0.0f64; size];
            let mut nu_d = alloc::vec![0.0f64; size];
            let mut alpha = alloc::vec![0.0f64; size];

            for r in 0..size {
                let rf = r as f64;
                let kn = pk + rf;
                let inv_kn = 1.0 / kn;
                let an = rf.mul_add(0.5, pa);

                lng_base[r] = ln_gamma(an + 0.5) - ln_gamma(an) - half_ln_pi;
                mu_a[r] = pk * pm * inv_kn;
                mu_b[r] = rf * inv_kn;
                beta_c[r] = pk * rf * 0.5 * inv_kn;
                nu_d[r] = 2.0 * (kn + 1.0) * inv_kn;
                alpha[r] = an;
            }

            Precomputed {
                lng_base: lng_base.into_boxed_slice(),
                mu_a: mu_a.into_boxed_slice(),
                mu_b: mu_b.into_boxed_slice(),
                beta_c: beta_c.into_boxed_slice(),
                nu_d: nu_d.into_boxed_slice(),
                alpha: alpha.into_boxed_slice(),
            }
        };

        Ok(BocpdF64 {
            log_posterior: alloc::vec![f64::NEG_INFINITY; size].into_boxed_slice(),
            suf_count: alloc::vec![0u64; size].into_boxed_slice(),
            suf_mean: alloc::vec![0.0f64; size].into_boxed_slice(),
            suf_sum_sq: alloc::vec![0.0f64; size].into_boxed_slice(),
            scratch: alloc::vec![f64::NEG_INFINITY; size].into_boxed_slice(),
            scratch2: alloc::vec![0.0f64; size].into_boxed_slice(),
            pre,
            max_run_length,
            log_hazard: ln(h),
            log_1m_hazard: ln(1.0 - h),
            prior_mu: self.prior_mu,
            prior_beta: self.prior_beta,
            active: 0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn vague_prior() -> BocpdF64Builder {
        BocpdF64::builder()
            .prior_kappa(0.01)
            .prior_alpha(0.5)
            .prior_beta(10.0)
    }

    #[test]
    fn stable_signal_low_cp() {
        let mut bocpd = vague_prior()
            .max_run_length(200)
            .hazard_lambda(100.0)
            .build()
            .unwrap();
        for i in 0..200 {
            let sample = 50.0 + (i % 3) as f64;
            bocpd.update(sample).unwrap();
        }
        let cp = bocpd.change_point_probability().unwrap();
        assert!(cp < 0.1, "stable signal should have low CP prob, got {cp}");
    }

    #[test]
    fn mean_shift_detected() {
        let mut bocpd = vague_prior()
            .max_run_length(200)
            .hazard_lambda(100.0)
            .build()
            .unwrap();
        for _ in 0..100 {
            bocpd.update(0.0).unwrap();
        }
        let rl_before = bocpd.map_run_length().unwrap();
        let mean_rl_before = bocpd.mean_run_length().unwrap();

        for _ in 0..20 {
            bocpd.update(20.0).unwrap();
        }
        let rl_after = bocpd.map_run_length().unwrap();
        let mean_rl_after = bocpd.mean_run_length().unwrap();
        assert!(
            rl_after < rl_before,
            "MAP RL should drop after mean shift: before={rl_before}, after={rl_after}"
        );
        assert!(
            mean_rl_after < mean_rl_before * 0.5,
            "mean RL should drop significantly: before={mean_rl_before}, after={mean_rl_after}"
        );
    }

    #[test]
    fn variance_shift_detected() {
        let mut bocpd = BocpdF64::builder()
            .prior_mu(50.0)
            .prior_kappa(1.0)
            .prior_alpha(2.0)
            .prior_beta(1.0)
            .max_run_length(200)
            .hazard_lambda(100.0)
            .build()
            .unwrap();
        // Stable period: low variance around 50
        for i in 0..100 {
            bocpd.update(50.0 + (i % 2) as f64).unwrap();
        }
        let cp_before = bocpd.change_point_probability().unwrap();

        // Variance shift: amplitude ±0.5 → ±20
        let mut max_cp = 0.0f64;
        for i in 0..50 {
            let sample = if i % 2 == 0 { 70.0 } else { 30.0 };
            bocpd.update(sample).unwrap();
            let cp = bocpd.change_point_probability().unwrap();
            max_cp = max_cp.max(cp);
        }
        assert!(
            max_cp > cp_before,
            "CP prob should increase after variance shift: before={cp_before}, max={max_cp}"
        );
    }

    #[test]
    fn map_run_length_grows() {
        let mut bocpd = vague_prior()
            .max_run_length(200)
            .hazard_lambda(100.0)
            .build()
            .unwrap();
        let mut prev_rl = 0;
        for i in 0..50 {
            bocpd.update(50.0 + (i % 2) as f64).unwrap();
            if let Some(rl) = bocpd.map_run_length() {
                assert!(
                    rl >= prev_rl || rl == 0,
                    "MAP RL should grow monotonically for stable input: was {prev_rl}, now {rl} at step {i}"
                );
                prev_rl = rl;
            }
        }
        assert!(
            prev_rl > 10,
            "MAP RL should be substantial after 50 stable samples, got {prev_rl}"
        );
    }

    #[test]
    fn map_run_length_resets() {
        let mut bocpd = vague_prior()
            .max_run_length(200)
            .hazard_lambda(100.0)
            .build()
            .unwrap();
        for i in 0..100 {
            bocpd.update((i % 3) as f64).unwrap();
        }
        let rl_before = bocpd.map_run_length().unwrap();

        for i in 0..20 {
            bocpd.update(100.0 + (i % 3) as f64).unwrap();
        }
        let rl_after = bocpd.map_run_length().unwrap();
        assert!(
            rl_after < rl_before,
            "MAP RL should drop after mean shift: before={rl_before}, after={rl_after}"
        );
    }

    #[test]
    fn posterior_sums_to_one() {
        let mut bocpd = vague_prior()
            .max_run_length(100)
            .hazard_lambda(50.0)
            .build()
            .unwrap();
        for i in 0..80 {
            bocpd.update((i % 10) as f64).unwrap();
            if let Some(log_post) = bocpd.run_length_posterior() {
                let sum: f64 = log_post.iter().map(|&lp| exp(lp)).sum();
                assert!(
                    (sum - 1.0).abs() < 1e-6,
                    "posterior should sum to 1, got {sum} at step {i}"
                );
            }
        }
    }

    #[test]
    fn hazard_lambda_sensitivity() {
        let mut fast = vague_prior()
            .max_run_length(200)
            .hazard_lambda(20.0)
            .build()
            .unwrap();
        let mut slow = vague_prior()
            .max_run_length(200)
            .hazard_lambda(500.0)
            .build()
            .unwrap();
        for i in 0..100 {
            fast.update((i % 3) as f64).unwrap();
            slow.update((i % 3) as f64).unwrap();
        }
        let cp_fast = fast.change_point_probability().unwrap();
        let cp_slow = slow.change_point_probability().unwrap();
        assert!(
            cp_fast > cp_slow,
            "shorter λ should yield higher CP prob for stable input: fast={cp_fast}, slow={cp_slow}"
        );
    }

    #[test]
    fn rejects_nan_inf() {
        let mut bocpd = BocpdF64::builder()
            .max_run_length(20)
            .hazard_lambda(10.0)
            .build()
            .unwrap();
        assert!(bocpd.update(f64::NAN).is_err());
        assert!(bocpd.update(f64::INFINITY).is_err());
        assert!(bocpd.update(f64::NEG_INFINITY).is_err());
        assert_eq!(bocpd.count(), 0);
    }

    #[test]
    fn reset_clears() {
        let mut bocpd = vague_prior()
            .max_run_length(50)
            .hazard_lambda(20.0)
            .build()
            .unwrap();
        for i in 0..30 {
            bocpd.update(i as f64).unwrap();
        }
        assert!(bocpd.count() > 0);
        assert!(bocpd.is_primed());

        bocpd.reset();
        assert_eq!(bocpd.count(), 0);
        assert!(!bocpd.is_primed());
        assert!(bocpd.change_point_probability().is_none());
    }

    #[test]
    fn truncation_preserves_mass() {
        let mut bocpd = vague_prior()
            .max_run_length(20)
            .hazard_lambda(10.0)
            .build()
            .unwrap();
        // Feed more samples than max_run_length to trigger truncation
        for i in 0..50 {
            bocpd.update((i % 5) as f64).unwrap();
            if let Some(log_post) = bocpd.run_length_posterior() {
                let sum: f64 = log_post.iter().map(|&lp| exp(lp)).sum();
                assert!(
                    (sum - 1.0).abs() < 1e-6,
                    "posterior should still sum to 1 after truncation, got {sum} at step {i}"
                );
            }
        }
    }
}
