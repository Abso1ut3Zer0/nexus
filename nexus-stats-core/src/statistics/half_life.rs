use crate::statistics::Covariance;

/// Estimates how fast a series reverts to its mean.
///
/// Fits `x_t = c + phi * x_{t-1}` by least squares over the values fed so
/// far. A deviation from the mean is multiplied by `phi` each step, so it
/// halves in `-ln 2 / ln phi` steps.
///
/// # Bias
///
/// The least-squares estimate of `phi` is biased low, most visibly near 1
/// (the Dickey-Fuller bias): a random walk usually reads as reverting with
/// a long half-life. The estimate is left uncorrected, as statsmodels'
/// `AutoReg` and R's `ar` leave it. Use a unit-root test, not this, to
/// decide whether a series reverts.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::{HalfLife, Reversion};
///
/// let mut hl = HalfLife::new();
/// for x in [8.0, 4.0, 2.0, 1.0] {
///     hl.update(x);
/// }
/// assert_eq!(hl.coefficient(), Some(0.5));
/// assert_eq!(hl.reversion(), Some(Reversion::Reverting { half_life: 1.0 }));
/// ```
#[derive(Debug, Clone)]
pub struct HalfLife {
    /// Pairs `(x_t, x_{t-1})`.
    pairs: Covariance,
    prev: f64,
    /// Values fed, including the first, which has no pair.
    count: u64,
}

/// How a series behaves around its mean, from [`HalfLife::reversion`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Reversion {
    /// `0 <= phi < 1`: deviations decay.
    Reverting {
        /// Steps for a deviation to halve: `-ln 2 / ln phi`, exact for data
        /// sampled at fixed steps.
        ///
        /// A common shortcut (Chan, *Algorithmic Trading*) is
        /// `-ln 2 / (phi - 1)`. It agrees when reversion is slow and reads
        /// long when it is fast: 39% long at `phi = 0.5`.
        half_life: f64,
    },
    /// `phi >= 1`: deviations persist or grow, as in a trend.
    NotReverting,
    /// `phi < 0`: each step overshoots the mean.
    Oscillating,
}

impl Default for HalfLife {
    fn default() -> Self {
        Self::new()
    }
}

impl HalfLife {
    /// Creates a new estimator.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pairs: Covariance::new(),
            prev: 0.0,
            count: 0,
        }
    }

    /// Feeds the next value of the series.
    ///
    /// Does not validate `value`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::statistics::HalfLife;
    ///
    /// let mut hl = HalfLife::new();
    /// for x in [8.0, 4.0, 2.0, 1.0] {
    ///     hl.update(x);
    /// }
    /// assert_eq!(hl.coefficient(), Some(0.5));
    /// ```
    #[inline]
    pub fn update(&mut self, value: f64) {
        self.count += 1;
        if self.count >= 2 {
            self.pairs.update(value, self.prev);
        }
        self.prev = value;
    }

    /// Checked update. Feeds `value`, or returns an error and leaves the
    /// estimator unchanged if `value` is NaN, infinite, or larger in
    /// magnitude than `1e120` (see [input limits](crate#input-limits)).
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `value`
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if `value` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if `value`
    ///   is finite and larger in magnitude than `1e120`.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::{DataError, statistics::HalfLife};
    ///
    /// let mut hl = HalfLife::new();
    /// assert_eq!(hl.checked_update(1.0), Ok(()));
    /// assert_eq!(hl.checked_update(f64::NAN), Err(DataError::NotANumber));
    /// assert_eq!(hl.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(&mut self, value: f64) -> Result<(), crate::DataError> {
        crate::math::check_input(value, crate::math::LIMIT_FOR_SQUARES)?;
        self.update(value);
        Ok(())
    }

    /// The coefficient `phi`: the least-squares slope of `x_t` on
    /// `x_{t-1}`.
    ///
    /// `None` until three values have been fed, or if the lagged values
    /// are too close to constant for a slope to be resolved: a variance at
    /// or below `(f64::EPSILON * mean)^2`, the relative test SciPy uses for
    /// near-constant data. (R's `lm` likewise withholds the coefficient.)
    #[must_use]
    pub fn coefficient(&self) -> Option<f64> {
        let lagged_variance = self.pairs.variance_y()?;
        if lagged_variance <= crate::math::rounding_variance(self.pairs.mean_y()?) {
            return None;
        }

        Some(self.pairs.covariance()? / lagged_variance)
    }

    /// How the series behaves around its mean. `None` exactly when
    /// [`coefficient`](Self::coefficient) is.
    #[must_use]
    pub fn reversion(&self) -> Option<Reversion> {
        let phi = self.coefficient()?;
        if phi >= 1.0 {
            return Some(Reversion::NotReverting);
        }
        if phi < 0.0 {
            return Some(Reversion::Oscillating);
        }

        // At `phi = 0` the logarithm is `-inf` and the half-life is 0.
        Some(Reversion::Reverting {
            half_life: -core::f64::consts::LN_2 / crate::math::ln(phi),
        })
    }

    /// Number of values fed.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether three values have been fed.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.pairs.count() >= 2
    }

    /// Resets to the empty state.
    pub fn reset(&mut self) {
        self.pairs.reset();
        self.prev = 0.0;
        self.count = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fed(values: impl IntoIterator<Item = f64>) -> HalfLife {
        let mut hl = HalfLife::new();
        for x in values {
            hl.update(x);
        }
        hl
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
    fn a_halving_series_has_a_half_life_of_one_step() {
        let hl = fed([8.0, 4.0, 2.0, 1.0]);
        assert_eq!(hl.coefficient(), Some(0.5));
        assert_eq!(
            hl.reversion(),
            Some(Reversion::Reverting { half_life: 1.0 })
        );
    }

    #[test]
    fn a_doubling_series_does_not_revert() {
        let hl = fed([1.0, 2.0, 4.0, 8.0]);
        assert_eq!(hl.coefficient(), Some(2.0));
        assert_eq!(hl.reversion(), Some(Reversion::NotReverting));
    }

    #[test]
    fn a_straight_line_does_not_revert() {
        let hl = fed((0..100).map(f64::from));
        assert_eq!(hl.coefficient(), Some(1.0));
        assert_eq!(hl.reversion(), Some(Reversion::NotReverting));
    }

    #[test]
    fn an_alternating_series_oscillates() {
        let hl = fed((0..1000).map(|i| if i % 2 == 0 { 10.0 } else { -10.0 }));
        assert!((hl.coefficient().unwrap() + 1.0).abs() < 1e-12);
        assert_eq!(hl.reversion(), Some(Reversion::Oscillating));
    }

    #[test]
    fn a_coefficient_of_zero_reverts_at_once() {
        let hl = fed([1.0, 2.0, 3.0, 2.0]);
        assert_eq!(hl.coefficient(), Some(0.0));
        assert_eq!(
            hl.reversion(),
            Some(Reversion::Reverting { half_life: 0.0 })
        );
    }

    #[test]
    fn equal_lagged_values_have_no_coefficient() {
        // The last value differs, but it is never a lagged one.
        let hl = fed([5.0, 5.0, 5.0, 9.0]);
        assert_eq!(hl.coefficient(), None);
    }

    #[test]
    fn lagged_values_that_differ_only_by_rounding_have_no_coefficient() {
        let step = f64::EPSILON;
        assert_eq!(fed([1.0, 1.0 + step, 1.0, 1e120]).coefficient(), None);
        assert_eq!(
            fed([1e6, 1e6_f64.mul_add(step, 1e6), 1e6, 1e6]).coefficient(),
            None
        );

        // A small but real spread is resolved.
        let hl = fed([1.0, 1.0 + 1e-6, 1.0 + 2e-6, 1.0 + 3e-6]);
        assert!((hl.coefficient().unwrap() - 1.0).abs() < 1e-6);
    }

    #[test]
    fn a_constant_series_has_no_coefficient() {
        let hl = fed([5.0; 100]);
        assert_eq!(hl.coefficient(), None);
        assert_eq!(hl.reversion(), None);
    }

    #[test]
    fn the_coefficient_is_the_least_squares_slope() {
        // A noisy AR(1) with phi = 0.9, against the slope computed in two
        // passes over the stored pairs.
        let mut rng = 12345u64;
        let mut x = 0.0_f64;
        let mut series = [0.0; 2_000];
        for slot in &mut series {
            x = 0.9_f64.mul_add(x, xorshift64(&mut rng) * 0.1);
            *slot = x;
        }
        let pairs = series.len() - 1;
        let mean_now = series[1..].iter().sum::<f64>() / pairs as f64;
        let mean_lag = series[..pairs].iter().sum::<f64>() / pairs as f64;
        let (mut cross, mut lag_sq) = (0.0, 0.0);
        for t in 1..series.len() {
            cross += (series[t] - mean_now) * (series[t - 1] - mean_lag);
            lag_sq += (series[t - 1] - mean_lag) * (series[t - 1] - mean_lag);
        }
        let slope = cross / lag_sq;

        let hl = fed(series);
        let phi = hl.coefficient().unwrap();
        assert!((phi - slope).abs() < 1e-12, "{phi} vs {slope}");
        assert!((phi - 0.9).abs() < 0.03, "phi = {phi}");
        let Some(Reversion::Reverting { half_life }) = hl.reversion() else {
            panic!("expected a reverting series");
        };
        assert!((half_life + core::f64::consts::LN_2 / phi.ln()).abs() < 1e-12);
    }

    #[test]
    fn needs_three_values() {
        let mut hl = fed([1.0, 3.0]);
        assert!(!hl.is_primed());
        assert_eq!(hl.coefficient(), None);
        hl.update(2.0);
        assert!(hl.is_primed());
        assert!(hl.coefficient().is_some());
    }

    #[test]
    fn reset_clears_state() {
        let mut hl = fed((0..100).map(f64::from));
        hl.reset();
        assert_eq!(hl.count(), 0);
        assert!(!hl.is_primed());
        assert_eq!(hl.coefficient(), None);
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let mut hl = HalfLife::new();
        for x in [8.0, 4.0, 2.0, 1.0] {
            hl.checked_update(x).unwrap();
        }
        let before = (hl.count(), hl.coefficient(), hl.reversion());

        assert_eq!(hl.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(hl.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(hl.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(hl.checked_update(1e121), Err(OutOfRange));
        assert_eq!(hl.checked_update(-1e121), Err(OutOfRange));

        assert_eq!((hl.count(), hl.coefficient(), hl.reversion()), before);
        // The next good value still pairs with the last good one.
        hl.checked_update(0.5).unwrap();
        assert_eq!(hl.coefficient(), Some(0.5));
    }

    #[test]
    fn checked_update_accepts_the_limit_without_overflow() {
        let limit = crate::math::LIMIT_FOR_SQUARES;
        let mut hl = HalfLife::new();
        for i in 0..100_000 {
            hl.checked_update(if i % 2 == 0 { limit } else { -limit })
                .unwrap();
        }
        assert!((hl.coefficient().unwrap() + 1.0).abs() < 1e-9);
        assert_eq!(hl.reversion(), Some(Reversion::Oscillating));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let values = [2.0, -7.5, 1e9, 0.0, 3.25, 11.0];
        let unchecked = fed(values);
        let mut checked = HalfLife::new();
        for x in values {
            checked.checked_update(x).unwrap();
        }
        assert_eq!(checked.count(), unchecked.count());
        assert_eq!(checked.coefficient(), unchecked.coefficient());
        assert_eq!(checked.reversion(), unchecked.reversion());
    }

    #[test]
    fn update_does_not_validate() {
        let hl = fed([1.0, f64::NAN, 2.0, 3.0]);
        assert_eq!(hl.count(), 4);
    }
}
