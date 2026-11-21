use crate::math::MulAdd;

/// Splits a period's price variation into a continuous part and a jump
/// part (Barndorff-Nielsen & Shephard, 2004).
///
/// Works on log returns, `r_i = ln(price_i) - ln(price_{i-1})`:
///
/// - realized variance, `sum r_i^2`, counts everything;
/// - bipower variation, `pi/2 * sum |r_i| * |r_{i-1}|`, is moved far less by
///   a jump: the jump enters once, times its neighbours, not squared.
///
/// Both are totals since the last [`reset`](Self::reset), so reset at the
/// start of each period.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::BipowerVariation;
///
/// let mut bv = BipowerVariation::builder().min_samples(3).build().unwrap();
/// for price in [100.0, 101.0, 100.0, 101.0, 150.0, 151.0, 150.0] {
///     bv.update(price);
/// }
/// // Most of the variation is the one jump.
/// assert!(bv.decomposition().unwrap().jump_ratio().unwrap() > 0.9);
/// ```
#[derive(Debug, Clone)]
pub struct BipowerVariation {
    /// Sum of squared returns.
    realized: f64,
    /// Sum of products of consecutive absolute returns.
    products: f64,
    prev_log_price: f64,
    prev_abs_return: f64,
    count: u64,
    min_samples: u64,
}

/// A [`BipowerVariation`] reading.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct JumpDecomposition {
    /// Sum of squared log returns.
    pub realized_variance: f64,
    /// `pi/2 * sum |r_i| * |r_{i-1}|`: the original definition
    /// (Barndorff-Nielsen & Shephard, 2004).
    pub bipower_variation: f64,
    /// Number of returns, `M`.
    pub returns: u64,
}

/// Builder for [`BipowerVariation`].
#[derive(Debug, Clone)]
pub struct BipowerVariationBuilder {
    min_samples: u64,
}

impl JumpDecomposition {
    /// `bipower_variation * M / (M - 1)`: scaled to be comparable with
    /// `realized_variance`, which has one more term.
    #[inline]
    #[must_use]
    pub fn debiased_bipower_variation(&self) -> f64 {
        let m = self.returns as f64;
        self.bipower_variation * m / (m - 1.0)
    }

    /// Variation attributed to jumps:
    /// `max(realized_variance - debiased_bipower_variation, 0)`.
    #[inline]
    #[must_use]
    pub fn jump_variation(&self) -> f64 {
        (self.realized_variance - self.debiased_bipower_variation()).max(0.0)
    }

    /// Share of the realized variance attributed to jumps, in `[0, 1]`.
    /// `None` if the price never moved.
    #[inline]
    #[must_use]
    pub fn jump_ratio(&self) -> Option<f64> {
        if self.realized_variance <= 0.0 {
            return None;
        }

        Some(self.jump_variation() / self.realized_variance)
    }
}

impl BipowerVariation {
    /// `1 / mu_1^2`, with `mu_1 = E|Z| = sqrt(2 / pi)` for a standard normal
    /// `Z`: the factor that puts bipower variation on the scale of realized
    /// variance (Barndorff-Nielsen & Shephard, 2004).
    const SCALE: f64 = core::f64::consts::FRAC_PI_2;

    /// Creates a tracker with the default `min_samples` (30).
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            realized: 0.0,
            products: 0.0,
            prev_log_price: 0.0,
            prev_abs_return: 0.0,
            count: 0,
            min_samples: 30,
        }
    }

    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> BipowerVariationBuilder {
        BipowerVariationBuilder { min_samples: 30 }
    }

    /// Feeds a price.
    ///
    /// Does not validate `price`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::statistics::BipowerVariation;
    ///
    /// let mut bv = BipowerVariation::builder().min_samples(3).build().unwrap();
    /// for _ in 0..3 {
    ///     bv.update(100.0);
    /// }
    /// let reading = bv.decomposition().unwrap();
    /// assert_eq!(reading.realized_variance, 0.0);
    /// assert_eq!(reading.returns, 2);
    /// ```
    #[inline]
    pub fn update(&mut self, price: f64) {
        let log_price = crate::math::ln(price);
        self.count += 1;

        if self.count >= 2 {
            let abs_return = (log_price - self.prev_log_price).abs();
            self.realized = abs_return.fma(abs_return, self.realized);
            // The first return pairs with the initial zero.
            self.products = abs_return.fma(self.prev_abs_return, self.products);
            self.prev_abs_return = abs_return;
        }
        self.prev_log_price = log_price;
    }

    /// Checked update. Feeds `price`, or returns an error and leaves the
    /// tracker unchanged if `price` is NaN, infinite, zero or negative.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `price`
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if `price` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if `price`
    ///   is zero or negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::{DataError, statistics::BipowerVariation};
    ///
    /// let mut bv = BipowerVariation::new();
    /// assert_eq!(bv.checked_update(100.0), Ok(()));
    /// assert_eq!(bv.checked_update(0.0), Err(DataError::OutOfRange));
    /// assert_eq!(bv.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(&mut self, price: f64) -> Result<(), crate::DataError> {
        // Any positive price is allowed: its logarithm is small.
        crate::math::check_input(price, f64::MAX)?;
        if price <= 0.0 {
            return Err(crate::DataError::OutOfRange);
        }
        self.update(price);
        Ok(())
    }

    /// The reading since the last reset, or `None` until `min_samples`
    /// prices have been fed.
    #[inline]
    #[must_use]
    pub fn decomposition(&self) -> Option<JumpDecomposition> {
        if self.count < self.min_samples {
            return None;
        }

        Some(JumpDecomposition {
            realized_variance: self.realized,
            bipower_variation: Self::SCALE * self.products,
            returns: self.count - 1,
        })
    }

    /// Number of prices fed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether `min_samples` prices have been fed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to the empty state. `min_samples` is unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.realized = 0.0;
        self.products = 0.0;
        self.prev_log_price = 0.0;
        self.prev_abs_return = 0.0;
        self.count = 0;
    }
}

impl Default for BipowerVariation {
    fn default() -> Self {
        Self::new()
    }
}

impl BipowerVariationBuilder {
    /// Prices to feed before a reading is given. Default: 30.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the tracker.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `min_samples` is below 3: bipower variation
    /// needs two returns.
    #[inline]
    pub fn build(self) -> Result<BipowerVariation, crate::ConfigError> {
        if self.min_samples < 3 {
            return Err(crate::ConfigError::Invalid("min_samples must be >= 3"));
        }
        Ok(BipowerVariation {
            min_samples: self.min_samples,
            ..BipowerVariation::new()
        })
    }
}

#[cfg(test)]
// Expected values are written as plain arithmetic.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;
    use core::f64::consts::FRAC_PI_2;

    fn tracker() -> BipowerVariation {
        BipowerVariation::builder().min_samples(3).build().unwrap()
    }

    /// Feeds prices whose log returns are `returns`, starting from 100.
    fn fed(returns: &[f64]) -> JumpDecomposition {
        let mut bv = tracker();
        let mut log_price = 100.0_f64.ln();
        bv.update(log_price.exp());
        for r in returns {
            log_price += r;
            bv.update(log_price.exp());
        }
        bv.decomposition().unwrap()
    }

    fn close(a: f64, b: f64) -> bool {
        (a - b).abs() <= 1e-9 * b.abs().max(1.0)
    }

    #[test]
    fn matches_the_definitions_on_three_returns() {
        // Returns 1, -2, 3: squares sum to 14; products 2 + 6.
        let r = fed(&[1.0, -2.0, 3.0]);
        assert!(close(r.realized_variance, 14.0));
        assert!(close(r.bipower_variation, FRAC_PI_2 * 8.0));
        assert_eq!(r.returns, 3);
    }

    #[test]
    fn the_debiased_form_is_scaled_by_m_over_m_minus_one() {
        let r = fed(&[1.0, -2.0, 3.0]);
        assert!(close(
            r.debiased_bipower_variation(),
            r.bipower_variation * 3.0 / 2.0
        ));
    }

    #[test]
    fn a_single_jump_is_attributed_to_jumps() {
        // Ten quiet returns, one of 0.5, ten quiet returns.
        let mut returns = [0.01; 21];
        returns[10] = 0.5;
        let r = fed(&returns);

        let realized = 20.0 * 0.01 * 0.01 + 0.5 * 0.5;
        // 18 quiet pairs, and two pairs that include the jump.
        let products = 18.0 * 0.01 * 0.01 + 2.0 * 0.01 * 0.5;
        let debiased = FRAC_PI_2 * products * 21.0 / 20.0;
        assert!(close(r.realized_variance, realized));
        assert!(close(r.jump_variation(), realized - debiased));
        assert!(close(
            r.jump_ratio().unwrap(),
            (realized - debiased) / realized
        ));
        assert!(r.jump_ratio().unwrap() > 0.9);
    }

    #[test]
    fn noise_without_jumps_has_almost_no_jump_share() {
        // Roughly normal returns: twelve uniforms, summed and centred.
        let mut state = 7u64;
        let mut uniform = || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 11) as f64 / (1u64 << 53) as f64
        };
        let mut bv = tracker();
        let mut log_price = 100.0_f64.ln();
        for _ in 0..20_000 {
            log_price += ((0..12).map(|_| uniform()).sum::<f64>() - 6.0) * 1e-3;
            bv.update(log_price.exp());
        }
        let r = bv.decomposition().unwrap();
        let ratio = r.debiased_bipower_variation() / r.realized_variance;
        assert!((ratio - 1.0).abs() < 0.03, "ratio = {ratio}");
        assert!(r.jump_ratio().unwrap() < 0.03);
    }

    #[test]
    fn the_jump_part_is_never_negative() {
        // Equal returns: bipower variation exceeds realized variance.
        let r = fed(&[0.01; 10]);
        assert!(r.debiased_bipower_variation() > r.realized_variance);
        assert_eq!(r.jump_variation(), 0.0);
        assert_eq!(r.jump_ratio(), Some(0.0));
    }

    #[test]
    fn a_price_that_never_moves_has_no_jump_ratio() {
        let r = fed(&[0.0; 5]);
        assert_eq!(r.realized_variance, 0.0);
        assert_eq!(r.jump_variation(), 0.0);
        assert_eq!(r.jump_ratio(), None);
    }

    #[test]
    fn no_reading_until_min_samples() {
        let mut bv = BipowerVariation::builder().min_samples(4).build().unwrap();
        for price in [100.0, 101.0, 100.0] {
            bv.update(price);
            assert_eq!(bv.decomposition(), None);
        }
        assert!(!bv.is_primed());
        bv.update(101.0);
        assert!(bv.decomposition().is_some());
        assert!(bv.is_primed());
    }

    #[test]
    fn the_builder_needs_two_returns() {
        assert!(BipowerVariation::builder().min_samples(2).build().is_err());
        assert!(BipowerVariation::builder().min_samples(3).build().is_ok());
    }

    #[test]
    fn reset_clears_the_period() {
        let next_period = [200.0, 210.0, 190.0, 205.0];
        let mut fresh = tracker();
        for price in next_period {
            fresh.update(price);
        }

        let mut bv = tracker();
        for price in [100.0, 101.0, 100.0, 150.0] {
            bv.update(price);
        }
        bv.reset();
        assert_eq!((bv.count(), bv.decomposition()), (0, None));

        // Nothing from before the reset reaches the next period.
        for price in next_period {
            bv.update(price);
        }
        assert_eq!(bv.decomposition(), fresh.decomposition());
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let mut bv = tracker();
        let mut untouched = tracker();
        for price in [100.0, 101.0, 99.0] {
            bv.checked_update(price).unwrap();
            untouched.checked_update(price).unwrap();
        }

        assert_eq!(bv.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(bv.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(bv.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(bv.checked_update(0.0), Err(OutOfRange));
        assert_eq!(bv.checked_update(-0.0), Err(OutOfRange));
        assert_eq!(bv.checked_update(-1.0), Err(OutOfRange));
        assert_eq!(
            (bv.count(), bv.decomposition()),
            (untouched.count(), untouched.decomposition())
        );

        // The next good price pairs with the last good price and return.
        bv.checked_update(104.0).unwrap();
        untouched.checked_update(104.0).unwrap();
        assert_eq!(bv.decomposition(), untouched.decomposition());
    }

    #[test]
    fn checked_update_accepts_a_subnormal_price() {
        let mut bv = tracker();
        for _ in 0..3 {
            bv.checked_update(5e-324).unwrap();
        }
        assert_eq!(bv.decomposition().unwrap().realized_variance, 0.0);
    }

    #[test]
    fn checked_update_accepts_any_positive_price_without_overflow() {
        let mut bv = tracker();
        for i in 0..100_000 {
            let price = if i % 2 == 0 {
                f64::MAX
            } else {
                f64::MIN_POSITIVE
            };
            bv.checked_update(price).unwrap();
        }
        let r = bv.decomposition().unwrap();
        assert!(r.realized_variance.is_finite());
        assert!(r.debiased_bipower_variation().is_finite());
        assert_eq!(r.jump_ratio(), Some(0.0));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let prices = [100.0, 101.5, 99.0, 99.0, 140.0, 141.0];
        let mut checked = tracker();
        let mut unchecked = tracker();
        for price in prices {
            checked.checked_update(price).unwrap();
            unchecked.update(price);
        }
        assert_eq!(checked.count(), unchecked.count());
        assert_eq!(checked.decomposition(), unchecked.decomposition());
    }

    #[test]
    fn update_does_not_validate() {
        let mut bv = tracker();
        bv.update(-1.0);
        assert_eq!(bv.count(), 1);
    }
}
