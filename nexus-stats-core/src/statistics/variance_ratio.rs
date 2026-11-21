use alloc::boxed::Box;
use alloc::vec;

use crate::statistics::EwmVar;

/// Variance Ratio VR(q) test for mean-reversion detection.
///
/// Compares the variance of q-period returns to q times the variance of
/// 1-period returns. Under a random walk, VR(q) = 1. Values below 1
/// suggest mean reversion; above 1 suggests trending.
///
/// Uses exponentially weighted variance for both the 1-period and q-period
/// return variances so the statistic adapts to changing regimes.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::VarianceRatio;
///
/// let mut vr = VarianceRatio::builder()
///     .q(5)
///     .alpha(0.05)
///     .build()
///     .unwrap();
///
/// // Feed mean-reverting data (alternating)
/// for i in 0..500 {
///     let val = 100.0 + if i % 2 == 0 { 5.0 } else { -5.0 };
///     vr.update(val).unwrap();
/// }
///
/// if let Some(ratio) = vr.variance_ratio() {
///     assert!(ratio < 1.0, "mean-reverting data should have VR < 1");
/// }
/// ```
#[derive(Debug, Clone)]
pub struct VarianceRatio {
    q: usize,
    short_var: EwmVar,
    long_var: EwmVar,
    /// The last `q` values; the slot at `head` is the oldest.
    ring: Box<[f64]>,
    head: usize,
    prev: f64,
    count: u64,
}

/// Builder for [`VarianceRatio`].
#[derive(Debug, Clone)]
pub struct VarianceRatioBuilder {
    q: Option<usize>,
    alpha: Option<f64>,
}

impl VarianceRatio {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> VarianceRatioBuilder {
        VarianceRatioBuilder {
            q: None,
            alpha: None,
        }
    }

    /// Feed a price level or cumulative return.
    ///
    /// Internally computes 1-period and q-period returns.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if the value is NaN or infinite.
    #[inline]
    pub fn update(&mut self, value: f64) -> Result<(), crate::DataError> {
        check_finite!(value);
        self.count += 1;

        if self.count >= 2 {
            // 1-period return
            let ret1 = value - self.prev;
            self.short_var.checked_update(ret1)?;
        }

        // The slot at `head` holds the value from q steps ago once q + 1
        // values have been seen.
        let value_q_ago = self.ring[self.head];
        self.ring[self.head] = value;
        self.head += 1;
        if self.head == self.q {
            self.head = 0;
        }
        if self.count > self.q as u64 {
            let ret_q = value - value_q_ago;
            self.long_var.checked_update(ret_q)?;
        }

        self.prev = value;
        Ok(())
    }

    /// VR(q) = Var(q-period return) / (q * Var(1-period return)).
    ///
    /// Returns `None` if not primed or if 1-period variance is zero.
    #[inline]
    #[must_use]
    pub fn variance_ratio(&self) -> Option<f64> {
        let var1 = self.short_var.value()?.variance;
        let var_q = self.long_var.value()?.variance;

        if var1 <= 0.0 {
            return None;
        }

        Some(var_q / (self.q as f64 * var1))
    }

    /// Whether VR(q) < 1.0 (mean-reverting).
    #[inline]
    #[must_use]
    pub fn is_mean_reverting(&self) -> bool {
        self.variance_ratio().is_some_and(|vr| vr < 1.0)
    }

    /// Whether VR(q) > 1.0 (trending).
    #[inline]
    #[must_use]
    pub fn is_trending(&self) -> bool {
        self.variance_ratio().is_some_and(|vr| vr > 1.0)
    }

    /// The q parameter.
    #[inline]
    #[must_use]
    pub fn q(&self) -> usize {
        self.q
    }

    /// Total observations fed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough observations for VR computation.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.short_var.is_primed() && self.long_var.is_primed()
    }

    /// Reset all state.
    pub fn reset(&mut self) {
        self.short_var.reset();
        self.long_var.reset();
        self.ring.fill(0.0);
        self.head = 0;
        self.prev = 0.0;
        self.count = 0;
    }
}

impl VarianceRatioBuilder {
    /// The ratio period. VR(q) compares q-period to 1-period variance.
    /// Required. Must be >= 2.
    #[inline]
    #[must_use]
    pub fn q(mut self, q: usize) -> Self {
        self.q = Some(q);
        self
    }

    /// EW smoothing factor for both variance trackers.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Sets `alpha` from a half-life in samples: `1 - exp(-ln 2 / halflife)`.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.alpha = Some(crate::math::alpha_from_halflife(halflife));
        self
    }

    /// Build the variance ratio tracker.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if q or alpha is missing/invalid.
    #[inline]
    pub fn build(self) -> Result<VarianceRatio, crate::ConfigError> {
        let q = self.q.ok_or(crate::ConfigError::Missing("q"))?;
        if q < 2 {
            return Err(crate::ConfigError::Invalid("q must be >= 2"));
        }

        let alpha = self.alpha.ok_or(crate::ConfigError::Missing("alpha"))?;

        let short_var = EwmVar::builder().alpha(alpha).build()?;
        let long_var = EwmVar::builder().alpha(alpha).build()?;

        Ok(VarianceRatio {
            q,
            short_var,
            long_var,
            ring: vec![0.0; q].into_boxed_slice(),
            head: 0,
            prev: 0.0,
            count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trending_series_vr_above_1() {
        let mut vr = VarianceRatio::builder().q(5).alpha(0.05).build().unwrap();

        // Monotonic trend — q-period returns should have higher variance
        // relative to q * 1-period variance.
        let mut price = 100.0;
        for i in 0..500 {
            // Trending with noise
            price += (i as f64).mul_add(0.001, 1.0);
            vr.update(price).unwrap();
        }

        assert!(vr.is_primed());
        let ratio = vr.variance_ratio().unwrap();
        assert!(
            ratio > 0.8, // trending should push VR > 1, but EW makes it noisy
            "VR should be > 0.8 for trending, got {ratio}"
        );
    }

    #[test]
    fn mean_reverting_series_vr_below_1() {
        let mut vr = VarianceRatio::builder().q(5).alpha(0.05).build().unwrap();

        // Mean-reverting: alternates around a center
        for i in 0..500 {
            let val = 100.0 + if i % 2 == 0 { 5.0 } else { -5.0 };
            vr.update(val).unwrap();
        }

        assert!(vr.is_primed());
        let ratio = vr.variance_ratio().unwrap();
        assert!(
            ratio < 1.0,
            "VR should be < 1.0 for mean-reverting, got {ratio}"
        );
        assert!(vr.is_mean_reverting());
    }

    #[test]
    fn not_primed_early() {
        let mut vr = VarianceRatio::builder().q(5).alpha(0.05).build().unwrap();

        vr.update(100.0).unwrap();
        assert!(!vr.is_primed());
        assert!(vr.variance_ratio().is_none());
    }

    #[test]
    fn q_must_be_at_least_2() {
        let result = VarianceRatio::builder().q(1).alpha(0.05).build();
        assert!(result.is_err());
    }

    #[test]
    fn reset_clears_state() {
        let mut vr = VarianceRatio::builder().q(5).alpha(0.05).build().unwrap();

        for i in 0..100 {
            vr.update(i as f64).unwrap();
        }
        vr.reset();
        assert_eq!(vr.count(), 0);
        assert!(!vr.is_primed());
    }

    #[test]
    fn nan_rejected() {
        let mut vr = VarianceRatio::builder().q(5).alpha(0.05).build().unwrap();
        assert!(vr.update(f64::NAN).is_err());
    }

    #[test]
    fn inf_rejected() {
        let mut vr = VarianceRatio::builder().q(5).alpha(0.05).build().unwrap();
        assert!(vr.update(f64::INFINITY).is_err());
    }

    /// Against the definition computed from a plain history `Vec`: the 1-period
    /// and q-period returns feed two `EwmVar`s exactly as the type does, so
    /// the ratio must match step by step, including when it is `None`.
    #[test]
    fn matches_the_definition_on_a_history_vec() {
        let q = 5usize;
        let alpha = 0.1;
        let mut vr = VarianceRatio::builder().q(q).alpha(alpha).build().unwrap();
        let mut short = EwmVar::builder().alpha(alpha).build().unwrap();
        let mut long = EwmVar::builder().alpha(alpha).build().unwrap();
        let mut history: Vec<f64> = Vec::new();
        for t in 0..300u32 {
            let v = (f64::from(t) * 0.37)
                .sin()
                .mul_add(3.0, f64::from(t) * 0.02);
            vr.update(v).unwrap();
            history.push(v);
            let len = history.len();
            if len >= 2 {
                short.update(v - history[len - 2]);
            }
            if len > q {
                long.update(v - history[len - 1 - q]);
            }
            let expected = match (short.value(), long.value()) {
                (Some(short), Some(long)) if short.variance > 0.0 => {
                    Some(long.variance / (q as f64 * short.variance))
                }
                _ => None,
            };
            match (vr.variance_ratio(), expected) {
                (None, None) => {}
                (Some(got), Some(want)) => {
                    assert!(
                        (got - want).abs() <= 1e-12 * want.abs().max(1.0),
                        "t={t}: {got} vs {want}"
                    );
                }
                (got, want) => panic!("t={t}: got {got:?}, expected {want:?}"),
            }
        }
        assert!(vr.is_primed());
    }
}
