use crate::math::{EwWeight, MulAdd};
use crate::statistics::EwmaVar;
use crate::storage::Ring;

/// Largest `alpha * q` the builder accepts: 2, with a few rounding steps of
/// allowance so that `alpha = 2.0 / q` and `span(q - 1)` are accepted
/// whichever way their product rounds.
const MAX_ALPHA_TIMES_Q: f64 = 2.0 * (1.0 + 4.0 * f64::EPSILON);

/// Variance ratio VR(q), a test for mean reversion against trending
/// (Lo & MacKinlay, 1988).
///
/// `VR(q) = Var(q-period change) / (q * Var(1-period change))`, on the
/// changes of the values fed. Under a random walk the changes are
/// uncorrelated and VR(q) = 1. Below 1, changes tend to reverse (mean
/// reversion); above 1, they tend to continue (trending).
///
/// Both variances are exponentially weighted (see [`EwmaVar`]), so the
/// statistic follows changing regimes.
///
/// The q-period changes overlap: consecutive ones share `q - 1` of their
/// `q` steps, so they are strongly correlated and a variance measured about
/// their own mean reads low. The ratio is corrected for that, with the
/// exponentially weighted counterpart of the `(1 - q / n)` factor in Lo and
/// MacKinlay's overlapping estimator, so that it averages 1 on a random
/// walk from the first reading on.
///
/// # Choosing alpha
///
/// The weights span roughly `2 / alpha` changes. That must be at least
/// `q` (the builder rejects `alpha > 2 / q`: a variance of q-period
/// changes cannot be estimated from fewer than q of them), and should be
/// several times `q`: at `2 / alpha = 40` the average reading on a random
/// walk is within a few percent of 1 for `q` up to 20, while at
/// `2 / alpha = 10` it reads 3% to 20% high, because a ratio of two noisy
/// variances is biased upward. A single reading is noisy in any case;
/// compare it with 1 using a margin.
///
/// # Cost
///
/// `update` is O(1) once the weights have settled (within about
/// `36 / alpha` values). Until then each update also refreshes the overlap
/// correction, which is O(q).
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::VarianceRatio;
///
/// let mut vr = VarianceRatio::builder().q(5).alpha(0.05).build().unwrap();
///
/// // A series that alternates around a level: every change reverses.
/// let mut ratio = None;
/// for i in 0..500 {
///     let value = 100.0 + if i % 2 == 0 { 5.0 } else { -5.0 };
///     ratio = vr.update(value);
/// }
/// // One-step and five-step changes have the same size, so VR(5) is 1/5
/// // before the overlap correction and a little above it after.
/// let ratio = ratio.unwrap();
/// assert!(ratio > 0.2 && ratio < 0.23, "{ratio}");
/// ```
#[derive(Debug, Clone)]
pub struct VarianceRatio {
    short_var: EwmaVar,
    long_var: EwmaVar,
    /// The last `q` values: the oldest is the value `q` steps back.
    history: Ring<f64>,
    /// Expected value of the q-period variance estimate, as a fraction of
    /// the true q-period variance, under a random walk. Refreshed while the
    /// q-period weights are still settling, constant afterwards.
    overlap_factor: f64,
    one_minus_alpha: f64,
    /// `(1 - alpha)^(2 n)` after `n` q-period changes; underflows to 0.
    decay_sq: f64,
    count: u64,
}

/// Builder for [`VarianceRatio`].
#[derive(Debug, Clone)]
pub struct VarianceRatioBuilder {
    q: Option<usize>,
    weight: Option<EwWeight>,
}

impl VarianceRatio {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> VarianceRatioBuilder {
        VarianceRatioBuilder {
            q: None,
            weight: None,
        }
    }

    /// Feeds a value (a price or level, not a return). Returns the variance
    /// ratio as [`variance_ratio`](Self::variance_ratio) does.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in. A
    /// NaN or an infinity makes the readings NaN from then on, until
    /// [`reset`](Self::reset); a finite value above
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT) in magnitude can overflow them. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, value: f64) -> Option<f64> {
        self.count += 1;
        if let Some(&previous) = self.history.newest() {
            self.short_var.fold(value - previous);
        }
        if let Some(q_steps_back) = self.history.push(value) {
            let settled = self.long_var.is_settled();
            self.long_var.fold(value - q_steps_back);
            if !settled {
                self.decay_sq *= self.one_minus_alpha * self.one_minus_alpha;
                self.overlap_factor = self.overlap_factor_now();
            }
        }
        self.variance_ratio()
    }

    /// [`update`](Self::update) with the input validated first: refuses a
    /// value that is NaN, infinite, or above [`INPUT_LIMIT`](crate::INPUT_LIMIT) in
    /// magnitude, and leaves the state untouched. Fed only through this
    /// method, no reading is ever NaN, or infinite unless its documentation
    /// says so.
    ///
    /// # Errors
    ///
    /// `DataError::NotANumber`, `DataError::Infinite`, or
    /// `DataError::OutOfRange` for a finite magnitude above the limit.
    #[inline]
    pub fn checked_update(&mut self, value: f64) -> Result<Option<f64>, crate::DataError> {
        check_magnitude!(value, crate::INPUT_LIMIT);
        Ok(self.update(value))
    }

    /// The variance ratio VR(q).
    ///
    /// `None` until `2 * q + 1` values have been fed (enough q-period
    /// changes that two of them do not overlap), and while the 1-period
    /// variance is zero, which leaves the ratio undefined: every change so
    /// far was the same (a constant series, or an exact straight line), or
    /// the series has been flat long enough for the weighted variance to
    /// decay to nothing.
    #[inline]
    #[must_use]
    #[allow(clippy::cast_precision_loss)]
    pub fn variance_ratio(&self) -> Option<f64> {
        if !self.is_primed() {
            return None;
        }
        let short = self.short_var.last()?.variance;
        let long = self.long_var.last()?.variance;
        (short > 0.0).then(|| long / (self.q() as f64 * short * self.overlap_factor))
    }

    /// The return horizon q.
    #[inline]
    #[must_use]
    pub fn q(&self) -> usize {
        self.history.capacity()
    }

    /// Number of values processed since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough values have been fed: `2 * q + 1`, so that the
    /// q-period changes seen so far include two that do not overlap.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.long_var.count() > self.q() as u64
    }

    /// Forgets every value. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.short_var.reset();
        self.long_var.reset();
        self.history.clear(0.0);
        self.overlap_factor = 1.0;
        self.decay_sq = 1.0;
        self.count = 0;
    }

    /// The overlap correction for the q-period changes folded so far.
    ///
    /// Consecutive q-period changes share `q - 1` of their `q` steps, so
    /// under a random walk they are correlated: `rho(k) = 1 - k / q` for
    /// `k < q`. A variance measured about the sample's own mean then reads
    /// low, by more the fewer effectively independent changes the weights
    /// span. With weights `w_i = b^i` (`b = 1 - alpha`, newest first),
    /// totals `W = sum w_i` and `W2 = sum w_i^2`, and
    /// `C = sum_ij w_i w_j rho(|i - j|)`, the unbiased weighted variance
    /// has expectation `(W^2 - C) / (W^2 - W2)` times the true variance.
    /// This is the exponentially weighted counterpart of the
    /// `(1 - q / n)` factor in Lo and MacKinlay's overlapping estimator.
    #[allow(clippy::cast_precision_loss)]
    fn overlap_factor_now(&self) -> f64 {
        let (w, w2) = self.long_var.weight_totals();
        let b = self.one_minus_alpha;
        let b_sq = b * b;
        let inv_one_minus_b_sq = 1.0 / (1.0 - b_sq);
        let q = self.q();
        let lags = (self.long_var.count() as usize).min(q);
        // C = W2_n + 2 * sum_{k=1}^{lags-1} rho(k) * b^k * W2_{n-k}, where
        // W2_m = (1 - b^(2m)) / (1 - b^2) is the squared-weight total of the
        // m newest changes. `b^(2(n-k))` is walked up from `b^(2n)`, which
        // is tracked directly: recovering it from W2 is pure rounding noise
        // once the weights are near their limit.
        let mut cross = w2;
        let (mut b_k, mut b_2m) = (1.0, self.decay_sq);
        for k in 1..lags {
            b_k *= b;
            b_2m = (b_2m / b_sq).min(1.0);
            let w2_shorter = (1.0 - b_2m) * inv_one_minus_b_sq;
            cross += 2.0 * (1.0 - k as f64 / q as f64) * b_k * w2_shorter;
        }
        w.fma(w, -cross) / w.fma(w, -w2)
    }
}

impl VarianceRatioBuilder {
    /// Return horizon q (required, >= 2). VR(q) compares q-period changes
    /// with 1-period changes.
    #[inline]
    #[must_use]
    pub fn q(mut self, q: usize) -> Self {
        self.q = Some(q);
        self
    }

    /// Smoothing factor for both variance trackers. Must be in (0, 1).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Samples for a change's weight to decay by half. Must be positive
    /// and finite.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Span in samples (the pandas `span` convention). Must be at least 2.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(EwWeight::Span(n));
        self
    }

    /// Builds the variance ratio tracker.
    ///
    /// # Errors
    ///
    /// - `Missing` if `q` or the weight (`alpha`, `halflife` or `span`) was
    ///   not set.
    /// - `Invalid` if `q` is below 2, the weight is out of range (the
    ///   message names the knob set), or `alpha` exceeds `2 / q`.
    #[inline]
    pub fn build(self) -> Result<VarianceRatio, crate::ConfigError> {
        let q = self.q.ok_or(crate::ConfigError::Missing("q"))?;
        if q < 2 {
            return Err(crate::ConfigError::Invalid("q must be >= 2"));
        }
        let alpha = self
            .weight
            .ok_or(crate::ConfigError::Missing("alpha"))?
            .resolve()?;
        // With a rounding step of allowance, so that `alpha = 2.0 / q` and
        // `span(q - 1)` are accepted whatever way their product rounds.
        #[allow(clippy::cast_precision_loss)]
        if alpha * q as f64 > MAX_ALPHA_TIMES_Q {
            return Err(crate::ConfigError::Invalid(
                "alpha is too large for q: the weights must span at least q changes (alpha <= 2 / q)",
            ));
        }
        Ok(VarianceRatio {
            short_var: EwmaVar::builder().alpha(alpha).build()?,
            long_var: EwmaVar::builder().alpha(alpha).build()?,
            history: Ring::new(q, 0.0)?,
            overlap_factor: 1.0,
            one_minus_alpha: 1.0 - alpha,
            decay_sq: 1.0,
            count: 0,
        })
    }
}

#[cfg(test)]
// Expected values are written as plain arithmetic, independent of the fused
// forms the code under test uses.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    fn lcg(state: &mut u64) -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*state >> 11) as f64 / (1u64 << 53) as f64 - 0.5
    }

    fn feed(q: usize, alpha: f64, values: impl IntoIterator<Item = f64>) -> VarianceRatio {
        let mut vr = VarianceRatio::builder().q(q).alpha(alpha).build().unwrap();
        for v in values {
            let _ = vr.update(v);
        }
        vr
    }

    #[test]
    fn alternating_series_has_a_closed_form() {
        let alternating = |n: u32| (0..n).map(|i| if i % 2 == 0 { 105.0 } else { 95.0 });
        // Odd q: the q-step change is the same +-10 as the 1-step change,
        // so the uncorrected ratio is exactly 1 / q.
        for q in [3usize, 5, 7] {
            let vr = feed(q, 0.05, alternating(2_000));
            let ratio = vr.variance_ratio().unwrap();
            let want = 1.0 / (q as f64 * vr.overlap_factor);
            assert!((ratio - want).abs() < 1e-9, "q {q}: {ratio} vs {want}");
        }
        // Even q: every q-step change is 0, so VR(q) = 0.
        for q in [2usize, 4] {
            let vr = feed(q, 0.05, alternating(2_000));
            assert_eq!(vr.variance_ratio(), Some(0.0), "q {q}");
        }
    }

    /// The overlap factor against its definition, summed term by term:
    /// `(W^2 - C) / (W^2 - W2)` with `C = sum_ij w_i w_j rho(|i - j|)`.
    #[test]
    fn overlap_factor_matches_the_double_sum() {
        // Including the largest alpha each q allows, and q = 2 at an
        // extreme alpha, where the recovered decay terms are most at risk.
        for (q, alpha) in [
            (2usize, 0.3),
            (2, 0.999),
            (5, 0.1),
            (5, 0.4),
            (20, 0.05),
            (20, 0.1),
            (200, 0.01),
        ] {
            let mut vr = VarianceRatio::builder().q(q).alpha(alpha).build().unwrap();
            let mut state = 3;
            for t in 0..900usize {
                let _ = vr.update(lcg(&mut state));
                // n q-period changes folded so far.
                let Some(n) = (t + 1).checked_sub(q).filter(|&n| n >= 2) else {
                    continue;
                };
                // The double sum is O(n^2): every step early on, then a
                // sample of the later ones.
                if n > 60 && n % 41 != 0 {
                    continue;
                }
                let weights: Vec<f64> = (0..n).map(|i| (1.0 - alpha).powi(i as i32)).collect();
                let w: f64 = weights.iter().sum();
                let w2: f64 = weights.iter().map(|x| x * x).sum();
                let mut c = 0.0;
                for (i, wi) in weights.iter().enumerate() {
                    for (j, wj) in weights.iter().enumerate() {
                        let lag = i.abs_diff(j);
                        if lag < q {
                            c += wi * wj * (1.0 - lag as f64 / q as f64);
                        }
                    }
                }
                let want = (w * w - c) / (w * w - w2);
                let got = vr.overlap_factor;
                assert!(
                    (got - want).abs() < 1e-9 * want.abs().max(1e-3),
                    "q {q} alpha {alpha} n {n}: {got} vs {want}"
                );
            }
        }
    }

    #[test]
    fn random_walk_reads_about_one() {
        // Averaged over independent walks, VR(q) is near 1 from the first
        // readings on. Without the overlap correction these average 0.87
        // and 0.91 at q = 5 and 0.63 at q = 20.
        for (q, checkpoint, tolerance) in
            [(5usize, 40usize, 0.05), (5, 2_000, 0.05), (20, 300, 0.08)]
        {
            let mut sum = 0.0;
            let walks = 400;
            for seed in 0..walks {
                let mut state = 1 + seed as u64;
                let mut price = 100.0;
                let vr = feed(
                    q,
                    0.05,
                    (0..checkpoint).map(|_| {
                        price += lcg(&mut state);
                        price
                    }),
                );
                sum += vr.variance_ratio().unwrap();
            }
            let mean = sum / f64::from(walks);
            assert!(
                (mean - 1.0).abs() < tolerance,
                "q {q} at {checkpoint}: {mean}"
            );
        }
    }

    #[test]
    fn momentum_reads_above_one() {
        // Changes that persist: each change repeats the last one with
        // probability 0.9.
        let mut state = 5;
        let mut price = 100.0;
        let mut step = 1.0;
        let vr = feed(
            5,
            0.02,
            (0..5_000).map(|_| {
                if lcg(&mut state) > 0.4 {
                    step = -step;
                }
                price += step;
                price
            }),
        );
        assert!(vr.variance_ratio().unwrap() > 2.0);
    }

    #[test]
    fn primes_at_two_q_plus_one_values() {
        let mut vr = VarianceRatio::builder().q(3).alpha(0.05).build().unwrap();
        // Six values give three 3-step changes, all overlapping.
        for v in [1.0, 3.0, 2.0, 5.0, 4.0, 6.0] {
            assert_eq!(vr.update(v), None);
            assert!(!vr.is_primed());
        }
        // The seventh gives a fourth, which does not overlap the first.
        assert!(vr.update(9.0).is_some());
        assert!(vr.is_primed());
        assert_eq!(vr.count(), 7);
    }

    #[test]
    fn identical_changes_leave_the_ratio_undefined() {
        // A constant series and an exact line: zero 1-period variance.
        assert_eq!(feed(3, 0.1, [7.0; 50]).variance_ratio(), None);
        let line = feed(3, 0.1, (0..50).map(f64::from));
        assert!(line.is_primed());
        assert_eq!(line.variance_ratio(), None);
    }

    /// Against the definition computed from a plain history `Vec`: the
    /// 1-period and q-period changes feed two `EwmaVar`s, so the ratio must
    /// match step by step, including when it is `None`.
    #[test]
    fn matches_the_definition_on_a_history_vec() {
        let q = 5usize;
        let alpha = 0.1;
        let mut vr = VarianceRatio::builder().q(q).alpha(alpha).build().unwrap();
        let mut short = EwmaVar::builder().alpha(alpha).build().unwrap();
        let mut long = EwmaVar::builder().alpha(alpha).build().unwrap();
        let mut history: Vec<f64> = Vec::new();
        let mut state = 11;
        for t in 0..300u32 {
            let v = f64::from(t).mul_add(0.02, 3.0 * lcg(&mut state));
            let got = vr.update(v);
            history.push(v);
            let len = history.len();
            if len >= 2 {
                let _ = short.update(v - history[len - 2]);
            }
            if len > q {
                let _ = long.update(v - history[len - 1 - q]);
            }
            let expected = match (short.last(), long.last()) {
                (Some(s), Some(l)) if s.variance > 0.0 && len > 2 * q => {
                    Some(l.variance / (q as f64 * s.variance * vr.overlap_factor))
                }
                _ => None,
            };
            assert_eq!(got.is_some(), expected.is_some(), "t={t}");
            if let (Some(got), Some(want)) = (got, expected) {
                assert!(
                    (got - want).abs() <= 1e-12 * want.abs().max(1.0),
                    "t={t}: {got} vs {want}"
                );
            }
            assert_eq!(got, vr.variance_ratio());
        }
    }

    #[test]
    fn builder_validation() {
        use crate::ConfigError::{Invalid, Missing};
        let b = VarianceRatio::builder;
        assert_eq!(b().alpha(0.1).build().unwrap_err(), Missing("q"));
        assert_eq!(b().q(5).build().unwrap_err(), Missing("alpha"));
        assert_eq!(
            b().q(1).alpha(0.1).build().unwrap_err(),
            Invalid("q must be >= 2")
        );
        assert_eq!(
            b().q(5).alpha(1.5).build().unwrap_err(),
            Invalid("alpha must be in (0, 1)")
        );
        assert_eq!(
            b().q(5).span(1).build().unwrap_err(),
            Invalid("span must be at least 2")
        );
        assert_eq!(
            b().q(5).alpha(0.41).build().unwrap_err(),
            Invalid(
                "alpha is too large for q: the weights must span at least q changes (alpha <= 2 / q)"
            )
        );
        assert!(b().q(5).alpha(0.4).build().is_ok());
        // The documented maximum is accepted for every q, however
        // `2.0 / q * q` happens to round. (At q = 2 it is alpha = 1, which
        // is out of range for any weight.)
        for q in 3usize..2_000 {
            assert!(b().q(q).alpha(2.0 / q as f64).build().is_ok(), "q {q}");
            assert!(b().q(q).span(q as u64 - 1).build().is_ok(), "q {q}");
        }
        assert!(b().q(2).alpha(1.0 - f64::EPSILON).build().is_ok());
        assert_eq!(b().q(4).span(20).build().unwrap().q(), 4);
    }

    #[test]
    fn reset_clears_state() {
        let mut vr = feed(5, 0.05, (0..100).map(|i| f64::from(i * i % 17)));
        assert!(vr.is_primed());
        vr.reset();
        assert_eq!(vr.count(), 0);
        assert!(!vr.is_primed());
        // The first value after a reset has no predecessor.
        assert_eq!(vr.update(3.0), None);
        assert_eq!(vr.short_var.count(), 0);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut vr = VarianceRatio::builder().q(5).alpha(0.05).build().unwrap();
        assert_eq!(
            vr.checked_update(f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        assert_eq!(
            vr.checked_update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(vr.count(), 0);
    }
}
