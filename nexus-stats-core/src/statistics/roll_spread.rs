use crate::math::{EwWeight, MulAdd};

/// Roll's implicit bid-ask spread estimator (Roll, 1984).
///
/// In Roll's model a trade prints at the efficient price plus or minus half
/// the spread, on the buy or sell side at random. That bounce makes
/// consecutive price changes negatively correlated, with
/// `Cov(dp_t, dp_{t-1}) = -(spread / 2)^2`, so
/// `spread = 2 * sqrt(-Cov(dp_t, dp_{t-1}))`.
///
/// The autocovariance is an exponentially weighted average of the products
/// `dp_t * dp_{t-1}`, normalized by the weight actually accumulated, so it
/// does not read low while warming up. Price changes are taken to have zero
/// mean (no drift over the weighting horizon), as in Roll's model.
///
/// When the autocovariance is not negative the data does not show the
/// bounce the model assumes (a trending market does this), and the spread
/// is reported as zero. That is the usual convention for this estimator
/// (Hasbrouck, 2009; Goyenko, Holden and Trzcinka, 2009).
/// [`RollEstimate::model_fits`] is `false` when the autocovariance is
/// positive, which tells a market the model does not describe apart from
/// a price that has not moved (zero autocovariance, zero spread, and
/// nothing that contradicts the model).
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::RollSpread;
///
/// let mut rs = RollSpread::builder().alpha(0.05).build().unwrap();
///
/// // Trades at a fixed mid of 100 with a spread of 0.02, on a random side.
/// let mut state = 7u64;
/// let mut estimate = None;
/// for _ in 0..5_000 {
///     state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
///     let side = if state >> 63 == 0 { 0.01 } else { -0.01 };
///     estimate = rs.update(100.0 + side);
/// }
/// let estimate = estimate.unwrap();
/// assert!(estimate.model_fits());
/// assert!((estimate.spread - 0.02).abs() < 0.006);
/// ```
#[derive(Debug, Clone)]
pub struct RollSpread {
    alpha: f64,
    one_minus_alpha: f64,
    /// Exponentially weighted sum of `dp_t * dp_{t-1}`, with weight alpha on
    /// the newest product.
    weighted_products: f64,
    /// `(1 - alpha)^k` after `k` products: the weight still on the zero the
    /// sum started from. The accumulated weight is one minus this.
    unfilled: f64,
    prev_price: f64,
    prev_diff: f64,
    count: u64,
    min_samples: u64,
}

/// A [`RollSpread`] reading: the spread and the autocovariance it rests on.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RollEstimate {
    /// Roll's spread, `2 * sqrt(-autocovariance)`, in price units; `0.0`
    /// when the autocovariance is not negative.
    pub spread: f64,
    /// Exponentially weighted autocovariance of consecutive price changes.
    /// Negative when the bid-ask bounce is present.
    pub autocovariance: f64,
}

impl RollEstimate {
    /// Whether the data is consistent with Roll's model: the
    /// autocovariance is not positive. When `false`, consecutive price
    /// changes tend to continue (a trending market) and `spread` is `0.0`
    /// because the estimator does not apply, not because the spread was
    /// measured to be zero.
    #[inline]
    #[must_use]
    pub fn model_fits(&self) -> bool {
        self.autocovariance <= 0.0
    }
}

/// Builder for [`RollSpread`].
#[derive(Debug, Clone)]
pub struct RollSpreadBuilder {
    weight: Option<EwWeight>,
    min_samples: u64,
}

impl RollSpread {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> RollSpreadBuilder {
        RollSpreadBuilder {
            weight: None,
            min_samples: 30,
        }
    }

    /// Feeds a trade price. Returns the estimate once primed.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in.
    /// After a NaN, an infinity, or a finite value above
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT) in magnitude (which can
    /// overflow), the readings carry no meaning until
    /// [`reset`](Self::reset): NaN as a rule, though a comparison inside can
    /// turn that into `None` or a wrong number. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, price: f64) -> Option<RollEstimate> {
        self.count += 1;
        let diff = price - self.prev_price;
        self.prev_price = price;
        // The first price has no change, the second no previous change.
        if self.count >= 3 {
            self.weighted_products = self.alpha.fma(
                diff * self.prev_diff,
                self.one_minus_alpha * self.weighted_products,
            );
            // Stop at zero once it no longer changes `1 - unfilled`. Left to
            // decay it would reach the subnormal range, where every multiply
            // costs a microcode assist (about 100 cycles).
            if self.unfilled != 0.0 {
                self.unfilled *= self.one_minus_alpha;
                if self.unfilled < f64::EPSILON / 4.0 {
                    self.unfilled = 0.0;
                }
            }
        }
        if self.count >= 2 {
            self.prev_diff = diff;
        }
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
    pub fn checked_update(&mut self, price: f64) -> Result<Option<RollEstimate>, crate::DataError> {
        check_magnitude!(price, crate::INPUT_LIMIT);
        Ok(self.update(price))
    }

    /// The current estimate, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<RollEstimate> {
        self.is_primed().then(|| {
            let autocovariance = self.weighted_products / (1.0 - self.unfilled);
            // Ordered so that a NaN autocovariance gives a NaN spread, not
            // a clean zero.
            let spread = if autocovariance >= 0.0 {
                0.0
            } else {
                2.0 * crate::math::sqrt(-autocovariance)
            };
            RollEstimate {
                spread,
                autocovariance,
            }
        })
    }

    /// Number of prices seen since construction or `reset`.
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

    /// Resets to uninitialized state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.weighted_products = 0.0;
        self.unfilled = 1.0;
        self.prev_price = 0.0;
        self.prev_diff = 0.0;
        self.count = 0;
    }
}

impl RollSpreadBuilder {
    /// Weight on the newest product of price changes. Must be in (0, 1).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Trades for a product's weight to decay by half. Must be positive
    /// and finite.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Span in trades (the pandas `span` convention). Must be at least 2.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(EwWeight::Span(n));
        self
    }

    /// Minimum prices before an estimate is returned. Default: 30. At
    /// least 3 (two price changes make one product).
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the Roll spread estimator.
    ///
    /// # Errors
    ///
    /// - `Missing("alpha")` if none of `alpha`, `halflife`, `span` was set.
    /// - `Invalid` if the weight is out of range (the message names the
    ///   knob set), or `min_samples` is below 3.
    #[inline]
    pub fn build(self) -> Result<RollSpread, crate::ConfigError> {
        let alpha = self
            .weight
            .ok_or(crate::ConfigError::Missing("alpha"))?
            .resolve()?;
        if self.min_samples < 3 {
            return Err(crate::ConfigError::Invalid(
                "min_samples must be >= 3: two price changes make one product",
            ));
        }
        Ok(RollSpread {
            alpha,
            one_minus_alpha: 1.0 - alpha,
            weighted_products: 0.0,
            unfilled: 1.0,
            prev_price: 0.0,
            prev_diff: 0.0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
// Expected values are written as plain arithmetic, independent of the fused
// forms the code under test uses.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;

    fn lcg(state: &mut u64) -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*state >> 11) as f64 / (1u64 << 53) as f64
    }

    fn fed(alpha: f64, min: u64, prices: impl IntoIterator<Item = f64>) -> RollSpread {
        let mut rs = RollSpread::builder()
            .alpha(alpha)
            .min_samples(min)
            .build()
            .unwrap();
        for p in prices {
            let _ = rs.update(p);
        }
        rs
    }

    #[test]
    fn the_first_estimate_is_already_full_scale() {
        // Three prices, one product: changes +1 then -1, product -1. The
        // weighted average of one product is that product whatever alpha
        // is, so the spread is 2. A sum started at zero and not normalized
        // would read 2 * sqrt(alpha).
        for alpha in [0.01, 0.05, 0.5] {
            let rs = fed(alpha, 3, [100.0, 101.0, 100.0]);
            let e = rs.last().unwrap();
            assert!((e.autocovariance + 1.0).abs() < 1e-12, "{alpha}: {e:?}");
            assert!((e.spread - 2.0).abs() < 1e-12, "{alpha}: {e:?}");
            assert!(e.model_fits());
        }
    }

    #[test]
    fn matches_the_weighted_average_of_products() {
        let alpha = 0.2;
        let prices = [10.0, 10.5, 10.1, 10.4, 9.9, 10.3, 10.2, 9.8];
        let mut rs = RollSpread::builder()
            .alpha(alpha)
            .min_samples(3)
            .build()
            .unwrap();
        for (i, &p) in prices.iter().enumerate() {
            let got = rs.update(p);
            if i < 2 {
                assert_eq!(got, None);
                continue;
            }
            // Products of consecutive changes, newest weighted 1, each
            // older one by a further factor of (1 - alpha).
            let (mut num, mut den, mut w) = (0.0, 0.0, 1.0);
            for j in (2..=i).rev() {
                let product = (prices[j] - prices[j - 1]) * (prices[j - 1] - prices[j - 2]);
                num += w * product;
                den += w;
                w *= 1.0 - alpha;
            }
            let want = num / den;
            let got = got.unwrap();
            assert!((got.autocovariance - want).abs() < 1e-12, "step {i}");
            let spread = if want < 0.0 {
                2.0 * (-want).sqrt()
            } else {
                0.0
            };
            assert!((got.spread - spread).abs() < 1e-12, "step {i}");
        }
    }

    #[test]
    fn recovers_the_spread_of_a_random_side_bounce() {
        // Roll's model: mid fixed, each trade on a random side, half the
        // spread away.
        let spread = 0.5;
        let mut state = 42;
        let rs = fed(
            0.002,
            30,
            (0..200_000).map(|_| {
                100.0
                    + if lcg(&mut state) < 0.5 {
                        spread / 2.0
                    } else {
                        -spread / 2.0
                    }
            }),
        );
        let e = rs.last().unwrap();
        assert!(e.model_fits());
        assert!((e.spread - spread).abs() < 0.05 * spread, "{e:?}");
    }

    #[test]
    fn a_trend_reports_zero_and_says_the_model_does_not_fit() {
        let rs = fed(0.05, 30, (0..200).map(|i| 100.0 + f64::from(i) * 0.1));
        let e = rs.last().unwrap();
        assert!(e.autocovariance > 0.0);
        assert_eq!(e.spread, 0.0);
        assert!(!e.model_fits());
        // A flat price: zero autocovariance and zero spread, with nothing
        // against the model. Told apart from the trend by `model_fits`.
        let e = fed(0.05, 30, [100.0; 50]).last().unwrap();
        assert_eq!((e.spread, e.autocovariance), (0.0, 0.0));
        assert!(e.model_fits());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn the_warm_up_weight_stops_at_zero_not_in_the_subnormals() {
        let mut rs = RollSpread::builder().alpha(0.05).build().unwrap();
        let mut smallest = 1.0f64;
        for i in 0..40_000 {
            let _ = rs.update(if i % 2 == 0 { 100.5 } else { 99.5 });
            if rs.unfilled > 0.0 {
                smallest = smallest.min(rs.unfilled);
            }
        }
        // It went to exactly zero, and never below the point where it
        // stopped mattering, far above the smallest normal number.
        assert_eq!(rs.unfilled, 0.0);
        assert!(smallest > 1e-18, "{smallest}");
        assert!(smallest.is_normal());
        // Changes of +-1 alternating: products of -1, a spread of 2.
        assert!((rs.last().unwrap().spread - 2.0).abs() < 1e-12);
    }

    #[test]
    fn update_returns_the_same_estimate_as_last() {
        let mut rs = RollSpread::builder()
            .alpha(0.1)
            .min_samples(5)
            .build()
            .unwrap();
        for (i, p) in [5.0, 6.0, 5.0, 6.0, 5.0, 6.0].into_iter().enumerate() {
            let got = rs.update(p);
            assert_eq!(got.is_some(), i >= 4, "price {i}");
            assert_eq!(got, rs.last());
            assert_eq!(rs.is_primed(), i >= 4);
        }
    }

    #[test]
    fn reset_clears() {
        let mut rs = fed(
            0.05,
            3,
            (0..100).map(|i| if i % 2 == 0 { 100.5 } else { 99.5 }),
        );
        assert!(rs.is_primed());
        rs.reset();
        assert_eq!(rs.count(), 0);
        assert_eq!(rs.last(), None);
        // Starts over: the first product after a reset is the only one.
        for p in [100.0, 101.0, 100.0] {
            let _ = rs.update(p);
        }
        assert!((rs.last().unwrap().spread - 2.0).abs() < 1e-12);
    }

    #[test]
    fn builder_validation() {
        use crate::ConfigError::{Invalid, Missing};
        let b = RollSpread::builder;
        assert_eq!(b().build().unwrap_err(), Missing("alpha"));
        assert_eq!(
            b().alpha(0.0).build().unwrap_err(),
            Invalid("alpha must be in (0, 1)")
        );
        assert_eq!(
            b().span(1).build().unwrap_err(),
            Invalid("span must be at least 2")
        );
        for min in [0, 2] {
            assert_eq!(
                b().alpha(0.05).min_samples(min).build().unwrap_err(),
                Invalid("min_samples must be >= 3: two price changes make one product")
            );
        }
        assert!(b().alpha(0.05).min_samples(3).build().is_ok());
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut rs = RollSpread::builder().alpha(0.05).build().unwrap();
        assert_eq!(
            rs.checked_update(f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        assert_eq!(
            rs.checked_update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(rs.count(), 0);
    }
}
