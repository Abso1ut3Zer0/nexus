/// Realized variance and bipower variation of a price path (Barndorff-
/// Nielsen & Shephard, 2004), and the jump component between them.
///
/// Over the price changes `r_i` since the last [`reset`](Self::reset):
///
/// - **realized variance** `RV = sum r_i^2` measures all of the path's
///   variation, jumps included;
/// - **bipower variation** `BV = (pi / 2) * sum |r_i| * |r_{i-1}|` measures
///   only the continuous part: a jump inflates one factor of a product, not
///   both, so it adds little.
///
/// `RV - BV` therefore estimates the variation that came from jumps.
///
/// Both are totals over the period, as in the literature: they grow with
/// the number of prices fed. Call `reset()` at the start of each period (a
/// session, a day, a bar) and read the totals at its end. Divide by the
/// number of price changes, `count() - 1`, for a per-step figure.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::BipowerVariation;
///
/// let mut bv = BipowerVariation::builder().min_samples(3).build().unwrap();
/// // Changes of +1, -1, +1, +1 and then a jump of +10.
/// let mut reading = None;
/// for price in [100.0, 101.0, 100.0, 101.0, 102.0, 112.0] {
///     reading = bv.update(price);
/// }
/// let r = reading.unwrap();
/// assert_eq!(r.realized_variance, 104.0);  // 1 + 1 + 1 + 1 + 100
/// let expected_bv = core::f64::consts::FRAC_PI_2 * 13.0; // 1 + 1 + 1 + 10
/// assert!((r.bipower_variation - expected_bv).abs() < 1e-12);
/// // Most of the variation is the jump.
/// assert!(r.jump_ratio().unwrap() > 0.8);
/// ```
#[derive(Debug, Clone)]
pub struct BipowerVariation {
    /// `sum |r_i| * |r_{i-1}|`, unscaled.
    sum_products: f64,
    /// `sum r_i^2`.
    sum_squares: f64,
    prev_abs_diff: f64,
    prev_price: f64,
    count: u64,
    min_samples: u64,
}

/// A [`BipowerVariation`] reading: the path's variation since the last
/// reset, split into its continuous and jump parts.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct JumpDecomposition {
    /// Realized variance: the sum of squared price changes.
    pub realized_variance: f64,
    /// Bipower variation: `pi / 2` times the sum of products of adjacent
    /// absolute price changes. Estimates the continuous part of the
    /// realized variance.
    pub bipower_variation: f64,
}

impl JumpDecomposition {
    /// Variation attributed to jumps: realized variance minus bipower
    /// variation, floored at zero (sampling noise can put the difference
    /// below it).
    #[inline]
    #[must_use]
    pub fn jump_variation(&self) -> f64 {
        (self.realized_variance - self.bipower_variation).max(0.0)
    }

    /// Share of the realized variance attributed to jumps, in `[0, 1]`.
    /// `None` when the realized variance is zero (the price never moved),
    /// which leaves the share undefined.
    #[inline]
    #[must_use]
    pub fn jump_ratio(&self) -> Option<f64> {
        (self.realized_variance > 0.0).then(|| self.jump_variation() / self.realized_variance)
    }
}

/// Builder for [`BipowerVariation`].
#[derive(Debug, Clone)]
pub struct BipowerVariationBuilder {
    min_samples: u64,
}

impl BipowerVariation {
    /// Creates a tracker with the default `min_samples` (30).
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            sum_products: 0.0,
            sum_squares: 0.0,
            prev_abs_diff: 0.0,
            prev_price: 0.0,
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

    /// Feeds a price. Returns the reading once primed.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in. A
    /// NaN or an infinity makes the readings NaN from then on, until
    /// [`reset`](Self::reset); a finite value above
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT) in magnitude can overflow them. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, price: f64) -> Option<JumpDecomposition> {
        self.count += 1;
        if self.count >= 2 {
            let diff = price - self.prev_price;
            let abs_diff = diff.abs();
            self.sum_squares += diff * diff;
            // Zero for the first change: `prev_abs_diff` starts at 0.
            self.sum_products += abs_diff * self.prev_abs_diff;
            self.prev_abs_diff = abs_diff;
        }
        self.prev_price = price;
        self.last()
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
    pub fn checked_update(
        &mut self,
        price: f64,
    ) -> Result<Option<JumpDecomposition>, crate::DataError> {
        check_magnitude!(price, crate::INPUT_LIMIT);
        Ok(self.update(price))
    }

    /// The current reading, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<JumpDecomposition> {
        self.is_primed().then_some(JumpDecomposition {
            realized_variance: self.sum_squares,
            bipower_variation: core::f64::consts::FRAC_PI_2 * self.sum_products,
        })
    }

    /// Number of prices seen since construction or `reset`. The number of
    /// price changes is one less.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether `min_samples` prices have been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Starts a new period: forgets every price. `min_samples` is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.sum_products = 0.0;
        self.sum_squares = 0.0;
        self.prev_abs_diff = 0.0;
        self.prev_price = 0.0;
        self.count = 0;
    }
}

impl Default for BipowerVariation {
    fn default() -> Self {
        Self::new()
    }
}

impl BipowerVariationBuilder {
    /// Minimum prices before a reading is returned. Default: 30. At least
    /// 3 (two price changes make the first product).
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
    /// `ConfigError::Invalid` if `min_samples` is below 3.
    #[inline]
    pub fn build(self) -> Result<BipowerVariation, crate::ConfigError> {
        if self.min_samples < 3 {
            return Err(crate::ConfigError::Invalid(
                "min_samples must be >= 3: two price changes make one product",
            ));
        }
        Ok(BipowerVariation {
            min_samples: self.min_samples,
            ..BipowerVariation::new()
        })
    }
}

#[cfg(test)]
// Expected values are written as plain arithmetic, independent of the fused
// forms the code under test uses.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;
    use core::f64::consts::FRAC_PI_2;

    fn fed(min: u64, prices: impl IntoIterator<Item = f64>) -> BipowerVariation {
        let mut bv = BipowerVariation::builder()
            .min_samples(min)
            .build()
            .unwrap();
        for p in prices {
            let _ = bv.update(p);
        }
        bv
    }

    fn lcg(state: &mut u64) -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*state >> 11) as f64 / (1u64 << 53) as f64
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn totals_are_the_defining_sums() {
        // Changes 2, -3, 1, 4: squares 4 + 9 + 1 + 16, products 6 + 3 + 4.
        let r = fed(3, [10.0, 12.0, 9.0, 10.0, 14.0]).last().unwrap();
        assert_eq!(r.realized_variance, 30.0);
        assert!((r.bipower_variation - FRAC_PI_2 * 13.0).abs() < 1e-12);
        assert!((r.jump_variation() - (30.0 - FRAC_PI_2 * 13.0)).abs() < 1e-12);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn totals_grow_with_the_period_and_restart_on_reset() {
        let steps = |n: u32| (0..=n).map(|i| if i % 2 == 0 { 100.0 } else { 101.0 });
        let short = fed(3, steps(10)).last().unwrap();
        let long = fed(3, steps(20)).last().unwrap();
        // Ten and twenty changes of size 1.
        assert_eq!(short.realized_variance, 10.0);
        assert_eq!(long.realized_variance, 20.0);
        assert!((long.bipower_variation - FRAC_PI_2 * 19.0).abs() < 1e-12);

        let mut bv = fed(3, steps(20));
        bv.reset();
        assert_eq!(bv.count(), 0);
        assert_eq!(bv.last(), None);
        for p in steps(10) {
            let _ = bv.update(p);
        }
        assert_eq!(bv.last().unwrap(), short);
    }

    #[test]
    fn a_jump_shows_up_in_the_decomposition() {
        // Small Gaussian-like steps: BV tracks RV and the jump share is
        // small. One large jump moves RV by its square but BV hardly.
        let mut state = 9;
        let mut price = 100.0;
        let mut step = || (lcg(&mut state) + lcg(&mut state) + lcg(&mut state) - 1.5) * 0.02;
        let mut prices = [0.0f64; 2_000];
        for p in &mut prices {
            price += step();
            *p = price;
        }
        let smooth = fed(30, prices).last().unwrap();
        assert!(smooth.jump_ratio().unwrap() < 0.05, "{smooth:?}");

        for p in &mut prices[1_000..] {
            *p += 1.0;
        }
        let jumped = fed(30, prices).last().unwrap();
        let added_rv = jumped.realized_variance - smooth.realized_variance;
        let added_bv = jumped.bipower_variation - smooth.bipower_variation;
        assert!(added_rv > 0.9, "{added_rv}");
        assert!(added_bv < 0.1, "{added_bv}");
        assert!((jumped.jump_variation() - added_rv).abs() < 0.1);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn jump_variation_is_floored_and_the_ratio_needs_movement() {
        // Equal-sized changes: BV = (pi/2) * (n - 1) exceeds RV = n, so
        // the raw difference is negative.
        let r = fed(3, (0..=20).map(f64::from)).last().unwrap();
        assert!(r.bipower_variation > r.realized_variance);
        assert_eq!(r.jump_variation(), 0.0);
        assert_eq!(r.jump_ratio(), Some(0.0));
        // A price that never moves has no variation to take a share of.
        let flat = fed(3, [5.0; 10]).last().unwrap();
        assert_eq!(flat.realized_variance, 0.0);
        assert_eq!(flat.jump_ratio(), None);
    }

    #[test]
    fn update_returns_the_same_reading_as_last() {
        let mut bv = BipowerVariation::builder().min_samples(4).build().unwrap();
        for (i, p) in [1.0, 2.0, 4.0, 3.0, 7.0].into_iter().enumerate() {
            let got = bv.update(p);
            assert_eq!(got.is_some(), i >= 3, "price {i}");
            assert_eq!(got, bv.last());
        }
        assert_eq!(BipowerVariation::new().min_samples, 30);
    }

    #[test]
    fn builder_validation() {
        for min in [0, 1, 2] {
            assert_eq!(
                BipowerVariation::builder()
                    .min_samples(min)
                    .build()
                    .unwrap_err(),
                crate::ConfigError::Invalid(
                    "min_samples must be >= 3: two price changes make one product"
                )
            );
        }
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut bv = BipowerVariation::new();
        assert_eq!(
            bv.checked_update(f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        assert_eq!(
            bv.checked_update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(bv.count(), 0);
    }
}
