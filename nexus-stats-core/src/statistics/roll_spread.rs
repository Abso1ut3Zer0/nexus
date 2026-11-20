use crate::math::MulAdd;

/// Roll's implicit bid-ask spread estimator (Roll, 1984).
///
/// Trades print at the bid or the ask, so consecutive price changes are
/// negatively correlated. In Roll's model the first-order autocovariance of
/// the changes is `-(spread / 2)^2`, which gives
/// `spread = 2 * sqrt(-autocovariance)`.
///
/// Works on changes in the log price, so the spread is a proportion of the
/// price (`0.0005` is 5 basis points) and means the same at any price
/// level. Roll's own estimates, and most later work, use this form.
///
/// The autocovariance is exponentially weighted, with the mean change
/// removed.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::RollSpread;
///
/// let mut rs = RollSpread::builder().alpha(0.05).min_samples(3).build().unwrap();
/// // A price bouncing between bid and ask.
/// for i in 0..200 {
///     rs.update(if i % 2 == 0 { 100.0 } else { 100.1 });
/// }
/// assert!(rs.estimate().unwrap().spread > 0.0);
/// ```
#[derive(Debug, Clone)]
pub struct RollSpread {
    alpha: f64,
    /// Changes in the log price.
    changes: WeightedMean,
    /// Products of consecutive changes.
    products: WeightedMean,
    prev_log_price: f64,
    prev_change: f64,
    count: u64,
    min_samples: u64,
}

/// A [`RollSpread`] reading.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RollEstimate {
    /// The spread as a proportion of the price. `0.0` when the
    /// autocovariance is not negative, where Roll's formula has no value;
    /// zero is the usual substitute (Hasbrouck, 2009; Goyenko, Holden &
    /// Trzcinka, 2009).
    pub spread: f64,
    /// Autocovariance of consecutive log-price changes. Negative when the
    /// bid-ask bounce dominates.
    pub autocovariance: f64,
}

/// Builder for [`RollSpread`].
#[derive(Debug, Clone)]
pub struct RollSpreadBuilder {
    weight: Option<crate::math::EwWeight>,
    min_samples: u64,
}

/// An exponentially weighted mean that does not read low while warming up:
/// the weighted sum is divided by the weight accumulated so far.
#[derive(Debug, Clone, Copy)]
struct WeightedMean {
    sum: f64,
    weight: f64,
}

impl WeightedMean {
    const EMPTY: Self = Self {
        sum: 0.0,
        weight: 0.0,
    };

    #[inline]
    fn update(&mut self, sample: f64, alpha: f64) {
        let keep = 1.0 - alpha;
        self.sum = alpha.fma(sample, keep * self.sum);
        self.weight = keep.fma(self.weight, alpha);
    }

    #[inline]
    fn value(&self) -> f64 {
        self.sum / self.weight
    }
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

    /// Feeds a trade price.
    ///
    /// Does not validate `price`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, price: f64) {
        let log_price = crate::math::ln(price);
        self.count += 1;

        if self.count >= 2 {
            let change = log_price - self.prev_log_price;
            self.changes.update(change, self.alpha);
            // The first change has no predecessor to pair with.
            if self.count >= 3 {
                self.products.update(change * self.prev_change, self.alpha);
            }
            self.prev_change = change;
        }
        self.prev_log_price = log_price;
    }

    /// Checked update. Feeds `price`, or returns an error and leaves the
    /// estimator unchanged if `price` is NaN, infinite, zero or negative.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `price`
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if `price` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if `price`
    ///   is zero or negative.
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

    /// The current estimate, or `None` until `min_samples` prices have been
    /// fed.
    #[inline]
    #[must_use]
    pub fn estimate(&self) -> Option<RollEstimate> {
        if self.count < self.min_samples {
            return None;
        }

        // No `n / (n - 1)` factor as in R's `bidask`: exponential weights
        // have no sample count.
        let mean_change = self.changes.value();
        let autocovariance = (-mean_change).fma(mean_change, self.products.value());
        let spread = if autocovariance < 0.0 {
            2.0 * crate::math::sqrt(-autocovariance)
        } else {
            0.0
        };

        Some(RollEstimate {
            spread,
            autocovariance,
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

    /// Resets to the empty state. Parameters are unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.changes = WeightedMean::EMPTY;
        self.products = WeightedMean::EMPTY;
        self.prev_log_price = 0.0;
        self.prev_change = 0.0;
        self.count = 0;
    }
}

impl RollSpreadBuilder {
    /// Weight of the newest sample. Must be in (0, 1) exclusive.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(crate::math::EwWeight::Alpha(alpha));
        self
    }

    /// Samples for a weight to decay by half. Must be positive and finite.
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(crate::math::EwWeight::Halflife(halflife));
        self
    }

    /// Span in samples (the pandas `span` convention). Must be at least 2.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(crate::math::EwWeight::Span(n));
        self
    }

    /// Prices to feed before an estimate is given. Default: 30.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the estimator.
    ///
    /// # Errors
    ///
    /// - `ConfigError::Missing` if none of `alpha`, `halflife` or `span` was
    ///   set.
    /// - `ConfigError::Invalid` if the one that was set is out of range, or
    ///   if `min_samples` is below 3: one product needs two changes.
    #[inline]
    pub fn build(self) -> Result<RollSpread, crate::ConfigError> {
        let alpha = self
            .weight
            .ok_or(crate::ConfigError::Missing("alpha"))?
            .resolve()?;
        if self.min_samples < 3 {
            return Err(crate::ConfigError::Invalid("min_samples must be >= 3"));
        }

        Ok(RollSpread {
            alpha,
            changes: WeightedMean::EMPTY,
            products: WeightedMean::EMPTY,
            prev_log_price: 0.0,
            prev_change: 0.0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
// Expected values are written as plain arithmetic.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;

    fn estimator(alpha: f64) -> RollSpread {
        RollSpread::builder()
            .alpha(alpha)
            .min_samples(3)
            .build()
            .unwrap()
    }

    /// Feeds prices whose log changes are `changes`, starting from 100.
    fn fed(alpha: f64, changes: &[f64]) -> RollEstimate {
        let mut rs = estimator(alpha);
        let mut log_price = 100.0_f64.ln();
        rs.update(log_price.exp());
        for change in changes {
            log_price += change;
            rs.update(log_price.exp());
        }
        rs.estimate().unwrap()
    }

    /// Buy or sell at random: `+1.0` or `-1.0`.
    fn side(state: &mut u64) -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        if (*state >> 63) == 0 { 1.0 } else { -1.0 }
    }

    /// Log prices that sit `half_spread` above or below a mid that drifts
    /// by `drift` each trade.
    fn bouncing(alpha: f64, half_spread: f64, drift: f64, trades: usize) -> RollEstimate {
        let mut rs = estimator(alpha);
        let mut state = 7u64;
        let mut mid = 100.0_f64.ln();
        for _ in 0..trades {
            mid += drift;
            rs.update((mid + half_spread * side(&mut state)).exp());
        }
        rs.estimate().unwrap()
    }

    #[test]
    fn matches_the_weighted_definitions() {
        let alpha = 0.2_f64;
        let changes = [0.01, -0.02, 0.015, -0.005, 0.02, -0.03];
        // Weights `alpha * (1 - alpha)^age`, newest first, written out.
        let weighted_mean = |values: &[f64]| {
            let (mut sum, mut total) = (0.0, 0.0);
            for (age, value) in values.iter().rev().enumerate() {
                let weight = alpha * (1.0 - alpha).powi(age as i32);
                sum += weight * value;
                total += weight;
            }
            sum / total
        };
        let products: [f64; 5] = core::array::from_fn(|i| changes[i + 1] * changes[i]);
        let mean = weighted_mean(&changes);
        let autocovariance = weighted_mean(&products) - mean * mean;

        let estimate = fed(alpha, &changes);
        assert!((estimate.autocovariance - autocovariance).abs() < 1e-15);
        assert!(autocovariance < 0.0);
        assert!((estimate.spread - 2.0 * (-autocovariance).sqrt()).abs() < 1e-12);
    }

    #[test]
    fn recovers_the_spread_of_a_bouncing_price() {
        // Roll's model: each trade at the mid plus or minus half the spread.
        let half_spread = 0.0005;
        let estimate = bouncing(0.001, half_spread, 0.0, 50_000);
        let spread = 2.0 * half_spread;
        assert!(
            (estimate.spread - spread).abs() < 0.1 * spread,
            "spread = {}",
            estimate.spread
        );
    }

    #[test]
    fn a_drifting_mid_does_not_hide_the_spread() {
        // With the drift left in, its square would cancel the bounce.
        let half_spread = 0.0005;
        let estimate = bouncing(0.001, half_spread, half_spread, 50_000);
        let spread = 2.0 * half_spread;
        assert!(
            (estimate.spread - spread).abs() < 0.1 * spread,
            "spread = {}",
            estimate.spread
        );
    }

    #[test]
    fn the_first_estimate_is_not_low() {
        // Changes +2h, -2h: one product, -4h^2, at full weight.
        let h = 0.001;
        let estimate = fed(0.05, &[2.0 * h, -2.0 * h]);
        assert!((estimate.spread - 4.0 * h).abs() < 0.02 * 4.0 * h);
    }

    #[test]
    fn a_non_negative_autocovariance_gives_a_zero_spread() {
        // Runs of rises and falls: consecutive changes move together.
        let estimate = fed(0.1, &[0.01, 0.01, -0.01, -0.01, 0.01, 0.01, -0.01, -0.01]);
        assert!(estimate.autocovariance > 0.0);
        assert_eq!(estimate.spread, 0.0);

        // A price that never moves.
        let estimate = fed(0.1, &[0.0; 5]);
        assert_eq!((estimate.autocovariance, estimate.spread), (0.0, 0.0));
    }

    #[test]
    fn no_estimate_until_min_samples() {
        let mut rs = RollSpread::builder()
            .alpha(0.1)
            .min_samples(4)
            .build()
            .unwrap();
        for price in [100.0, 100.1, 100.0] {
            rs.update(price);
            assert_eq!(rs.estimate(), None);
        }
        assert!(!rs.is_primed());
        rs.update(100.1);
        assert!(rs.estimate().is_some());
        assert!(rs.is_primed());
    }

    #[test]
    fn the_builder_validates() {
        assert!(RollSpread::builder().build().is_err());
        assert!(RollSpread::builder().alpha(0.0).build().is_err());
        assert!(RollSpread::builder().alpha(1.0).build().is_err());
        assert!(RollSpread::builder().span(1).build().is_err());
        assert!(
            RollSpread::builder()
                .alpha(0.1)
                .min_samples(2)
                .build()
                .is_err()
        );
        assert!(
            RollSpread::builder()
                .alpha(0.1)
                .min_samples(3)
                .build()
                .is_ok()
        );
        assert!(RollSpread::builder().span(20).build().is_ok());
        assert!(RollSpread::builder().halflife(10.0).build().is_ok());
    }

    #[test]
    fn reset_clears_everything_but_the_parameters() {
        let next = [200.0, 200.2, 199.9, 200.1, 200.0];
        let mut fresh = estimator(0.1);
        for price in next {
            fresh.update(price);
        }

        let mut rs = estimator(0.1);
        for price in [100.0, 101.0, 100.0, 150.0] {
            rs.update(price);
        }
        rs.reset();
        assert_eq!((rs.count(), rs.estimate()), (0, None));
        for price in next {
            rs.update(price);
        }
        assert_eq!(rs.estimate(), fresh.estimate());
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let mut rs = estimator(0.1);
        let mut untouched = estimator(0.1);
        for price in [100.0, 100.1, 99.9] {
            rs.checked_update(price).unwrap();
            untouched.checked_update(price).unwrap();
        }

        assert_eq!(rs.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(rs.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(rs.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(rs.checked_update(0.0), Err(OutOfRange));
        assert_eq!(rs.checked_update(-0.0), Err(OutOfRange));
        assert_eq!(rs.checked_update(-1.0), Err(OutOfRange));
        assert_eq!(
            (rs.count(), rs.estimate()),
            (untouched.count(), untouched.estimate())
        );

        // The next good price pairs with the last good price and change.
        rs.checked_update(100.2).unwrap();
        untouched.checked_update(100.2).unwrap();
        assert_eq!(rs.estimate(), untouched.estimate());
    }

    #[test]
    fn checked_update_accepts_any_positive_price_without_overflow() {
        let mut rs = estimator(0.1);
        for i in 0..100_000 {
            let price = if i % 2 == 0 { f64::MAX } else { 5e-324 };
            rs.checked_update(price).unwrap();
        }
        let estimate = rs.estimate().unwrap();
        assert!(estimate.autocovariance.is_finite());
        assert!(estimate.spread.is_finite() && estimate.spread > 0.0);
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = estimator(0.1);
        let mut unchecked = estimator(0.1);
        for price in [100.0, 100.1, 99.9, 100.0, 100.3, 100.2] {
            checked.checked_update(price).unwrap();
            unchecked.update(price);
        }
        assert_eq!(checked.count(), unchecked.count());
        assert_eq!(checked.estimate(), unchecked.estimate());
    }

    #[test]
    fn update_does_not_validate() {
        let mut rs = estimator(0.1);
        rs.update(-1.0);
        assert_eq!(rs.count(), 1);
    }
}
