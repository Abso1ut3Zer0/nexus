use crate::statistics::Covariance;

/// Mean-reversion half-life from an AR(1) fit.
///
/// Fits `x_t = c + phi * x_{t-1}` by least squares over all consecutive
/// pairs seen (`phi = Cov(x_t, x_{t-1}) / Var(x_{t-1})`) and reads the
/// behaviour off `phi`: a deviation from the mean shrinks by a factor of
/// `phi` each step, so it halves in `-ln 2 / ln phi` steps when
/// `0 < phi < 1`. See [`Reversion`] for the other cases.
///
/// All-time: every pair since construction or [`reset`](Self::reset)
/// counts equally.
///
/// `update` returns nothing and the result is read with
/// [`reversion`](Self::reversion): the half-life needs a logarithm, which
/// is kept off the per-sample path.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::{HalfLife, Reversion};
///
/// // Each value is half the last: phi = 0.5, a half-life of one step.
/// let mut hl = HalfLife::new();
/// for x in [8.0, 4.0, 2.0, 1.0] {
///     hl.update(x);
/// }
/// assert_eq!(hl.ar1_coefficient(), Some(0.5));
/// let Some(Reversion::Reverting { half_life }) = hl.reversion() else {
///     panic!("expected a reverting series");
/// };
/// assert!((half_life - 1.0).abs() < 1e-12);
///
/// // Each value is double the last: phi = 2, so it never reverts.
/// let mut hl = HalfLife::new();
/// for x in [1.0, 2.0, 4.0, 8.0] {
///     hl.update(x);
/// }
/// assert_eq!(hl.reversion(), Some(Reversion::NotReverting));
/// ```
#[derive(Debug, Clone)]
pub struct HalfLife {
    /// x = x_t, y = x_{t-1}, over the consecutive pairs seen so far.
    pairs: Covariance,
    prev: f64,
    /// Total observations including the first (which has no pair).
    count: u64,
}

/// How a series behaves around its mean, by its AR(1) coefficient `phi`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Reversion {
    /// `0 <= phi < 1`: a deviation decays toward the mean, halving every
    /// `half_life` steps. `phi = 0` is a half-life of 0: no memory at all.
    Reverting {
        /// Steps for a deviation to halve: `-ln 2 / ln phi`.
        half_life: f64,
    },
    /// `phi >= 1`: a random walk (`phi = 1`) or an explosive series.
    /// Deviations do not decay; there is no half-life.
    NotReverting,
    /// `phi < 0`: each step overshoots the mean and lands on the other
    /// side. The size of the deviation may shrink, but not by decaying
    /// toward the mean, so a half-life does not describe it.
    Oscillating,
}

impl Default for HalfLife {
    fn default() -> Self {
        Self::new()
    }
}

impl HalfLife {
    /// Creates a new estimator.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pairs: Covariance::new(),
            prev: 0.0,
            count: 0,
        }
    }

    /// Feed a value from the time series.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in. A
    /// NaN or an infinity makes the readings NaN from then on, until
    /// [`reset`](Self::reset); a finite value above
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT) in magnitude can overflow them. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, value: f64) {
        self.count += 1;
        if self.count >= 2 {
            // Both already within the limit: `prev` was checked when fed.
            self.pairs.update(value, self.prev);
        }
        self.prev = value;
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
    pub fn checked_update(&mut self, value: f64) -> Result<(), crate::DataError> {
        check_magnitude!(value, crate::INPUT_LIMIT);
        self.update(value);
        Ok(())
    }

    /// The AR(1) coefficient `phi`: the least-squares slope of `x_t` on
    /// `x_{t-1}`.
    ///
    /// `None` until three values have been fed (two pairs), and while the
    /// lagged values are all equal, which leaves the slope undefined (a
    /// constant series).
    #[inline]
    #[must_use]
    pub fn ar1_coefficient(&self) -> Option<f64> {
        let lagged_variance = self.pairs.variance_y()?;
        if lagged_variance <= 0.0 {
            return None;
        }
        Some(self.pairs.covariance()? / lagged_variance)
    }

    /// The series' behaviour around its mean, with the half-life when it
    /// reverts. `None` exactly when
    /// [`ar1_coefficient`](Self::ar1_coefficient) is.
    #[inline]
    #[must_use]
    pub fn reversion(&self) -> Option<Reversion> {
        let phi = self.ar1_coefficient()?;
        Some(if phi >= 1.0 {
            Reversion::NotReverting
        } else if phi < 0.0 {
            Reversion::Oscillating
        } else {
            // ln(0) is -inf, giving a half-life of 0 at phi = 0.
            Reversion::Reverting {
                half_life: -core::f64::consts::LN_2 / crate::math::ln(phi),
            }
        })
    }

    /// Number of observations fed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough observations have been fed for a fit: three.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.pairs.count() >= 2
    }

    /// Reset all state.
    #[inline]
    pub fn reset(&mut self) {
        self.pairs.reset();
        self.prev = 0.0;
        self.count = 0;
    }
}

#[cfg(test)]
// Expected values are written as plain arithmetic, independent of the fused
// forms the code under test uses.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;

    fn fed(values: impl IntoIterator<Item = f64>) -> HalfLife {
        let mut hl = HalfLife::new();
        for v in values {
            hl.update(v);
        }
        hl
    }

    fn half_life(hl: &HalfLife) -> f64 {
        match hl.reversion() {
            Some(Reversion::Reverting { half_life }) => half_life,
            other => panic!("expected Reverting, got {other:?}"),
        }
    }

    /// Simple xorshift64 for deterministic pseudo-random noise in [-1, 1].
    fn xorshift64(state: &mut u64) -> f64 {
        let mut s = *state;
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        *state = s;
        (s as f64 / u64::MAX as f64).mul_add(2.0, -1.0)
    }

    #[test]
    fn geometric_decay_is_recovered_exactly() {
        // x_t = phi * x_{t-1}: the fit is exact on four points. Dividing by
        // the variance of x_t instead of x_{t-1} would give 1 / phi here.
        for (phi, want) in [(0.5, 1.0), (0.25, 0.5), (0.5f64.sqrt(), 2.0)] {
            let hl = fed((0..4).map(|i| 64.0 * phi.powi(i)));
            assert!((hl.ar1_coefficient().unwrap() - phi).abs() < 1e-12);
            assert!((half_life(&hl) - want).abs() < 1e-9, "phi {phi}");
        }
    }

    #[test]
    fn decay_toward_a_non_zero_mean_is_recovered() {
        // x_t - 100 = 0.8 * (x_{t-1} - 100): the intercept absorbs the mean.
        let hl = fed((0..20).map(|i| 100.0 + 50.0 * 0.8f64.powi(i)));
        assert!((hl.ar1_coefficient().unwrap() - 0.8).abs() < 1e-9);
        let want = -core::f64::consts::LN_2 / 0.8f64.ln();
        assert!((half_life(&hl) - want).abs() < 1e-6);
    }

    #[test]
    fn growth_and_random_walks_do_not_revert() {
        // Doubling: phi = 2.
        let hl = fed([1.0, 2.0, 4.0, 8.0]);
        assert_eq!(hl.ar1_coefficient(), Some(2.0));
        assert_eq!(hl.reversion(), Some(Reversion::NotReverting));
        // A straight line: x_t = x_{t-1} + 1, phi = 1.
        let hl = fed((0..50).map(f64::from));
        assert!((hl.ar1_coefficient().unwrap() - 1.0).abs() < 1e-12);
        assert_eq!(hl.reversion(), Some(Reversion::NotReverting));
    }

    #[test]
    fn alternation_oscillates() {
        let hl = fed((0..1000).map(|i| if i % 2 == 0 { 10.0 } else { -10.0 }));
        assert!((hl.ar1_coefficient().unwrap() + 1.0).abs() < 1e-9);
        assert_eq!(hl.reversion(), Some(Reversion::Oscillating));
        // Damped alternation is still not a decay toward the mean.
        let hl = fed((0..12).map(|i| (-0.5f64).powi(i)));
        assert!((hl.ar1_coefficient().unwrap() + 0.5).abs() < 1e-9);
        assert_eq!(hl.reversion(), Some(Reversion::Oscillating));
    }

    #[test]
    fn no_memory_is_a_half_life_of_zero() {
        // Pairs (x_t, x_{t-1}) with exactly zero covariance.
        let hl = fed([1.0, -1.0, -1.0, 1.0, 1.0]);
        assert_eq!(hl.ar1_coefficient(), Some(0.0));
        assert_eq!(
            hl.reversion(),
            Some(Reversion::Reverting { half_life: 0.0 })
        );
    }

    #[test]
    fn ar1_process_half_life() {
        // AR(1) with phi = 0.9: half-life -ln 2 / ln 0.9 = 6.58.
        let phi = 0.9;
        let mut x = 0.0;
        let mut rng = 12345u64;
        let hl = fed((0..20_000).map(|_| {
            x = phi * x + xorshift64(&mut rng) * 0.1;
            x
        }));
        let got = hl.ar1_coefficient().unwrap();
        assert!((got - phi).abs() < 0.01, "{got}");
        let h = half_life(&hl);
        assert!((h - 6.58).abs() < 0.7, "{h}");
    }

    #[test]
    fn constant_or_too_short_has_no_fit() {
        let mut hl = HalfLife::new();
        hl.update(1.0);
        hl.update(2.0);
        // One pair: not primed.
        assert!(!hl.is_primed());
        assert_eq!(hl.ar1_coefficient(), None);
        assert_eq!(hl.reversion(), None);
        hl.update(3.0);
        assert!(hl.is_primed());
        assert!(hl.reversion().is_some());
        // Constant: primed, but the slope is undefined.
        let hl = fed([5.0; 100]);
        assert!(hl.is_primed());
        assert_eq!(hl.ar1_coefficient(), None);
        assert_eq!(hl.reversion(), None);
    }

    #[test]
    fn reset_clears_state() {
        let mut hl = fed((0..100).map(f64::from));
        hl.reset();
        assert_eq!(hl.count(), 0);
        assert!(!hl.is_primed());
        // The first value after a reset has no predecessor to pair with.
        for x in [8.0, 4.0, 2.0, 1.0] {
            hl.update(x);
        }
        assert_eq!(hl.ar1_coefficient(), Some(0.5));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut hl = HalfLife::new();
        assert_eq!(
            hl.checked_update(f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        assert_eq!(
            hl.checked_update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(hl.count(), 0);
    }
}
