use crate::math::MulAdd;

/// Roll's implicit spread estimator.
///
/// Estimates effective bid-ask spread from the autocovariance of
/// consecutive price changes: `spread = 2·sqrt(-Cov(dp_t, dp_{t-1}))`.
///
/// When autocovariance is non-negative (trending market), spread
/// is undefined and `spread()` returns `None`.
///
/// Hasbrouck (2009) adjustment uses autocorrelation:
/// `spread_h = spread · sqrt(1 + rho)`.
///
/// Roll (1984).
///
/// # Parameters
///
/// - `alpha` — EW decay factor for the autocovariance estimator.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::RollSpread;
///
/// let mut rs = RollSpread::builder()
///     .alpha(0.05)
///     .build()
///     .unwrap();
///
/// // Feed alternating prices (mean-reverting -> negative autocov)
/// for i in 0..200 {
///     let price = 100.0 + if i % 2 == 0 { 0.5 } else { -0.5 };
///     rs.update(price).unwrap();
/// }
/// assert!(rs.spread().is_some());
/// ```
#[derive(Debug, Clone)]
pub struct RollSpread {
    alpha: f64,
    one_minus_alpha: f64,
    ew_cov: f64,
    ew_var: f64,
    prev_price: f64,
    prev_diff: f64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`RollSpread`].
#[derive(Debug, Clone)]
pub struct RollSpreadBuilder {
    alpha: Option<f64>,
    min_samples: u64,
}

impl RollSpread {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> RollSpreadBuilder {
        RollSpreadBuilder {
            alpha: None,
            min_samples: 30,
        }
    }

    /// Feeds a trade price.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the price is NaN, or
    /// `DataError::Infinite` if the price is infinite.
    #[inline]
    pub fn update(&mut self, price: f64) -> Result<(), crate::DataError> {
        check_finite!(price);
        self.count += 1;

        if self.count == 1 {
            self.prev_price = price;
            return Ok(());
        }

        let diff = price - self.prev_price;
        self.prev_price = price;

        if self.count == 2 {
            self.prev_diff = diff;
            return Ok(());
        }

        self.ew_cov = self
            .alpha
            .fma(diff * self.prev_diff, self.one_minus_alpha * self.ew_cov);
        self.ew_var = self
            .alpha
            .fma(diff * diff, self.one_minus_alpha * self.ew_var);
        self.prev_diff = diff;
        Ok(())
    }

    /// Roll's spread: `2 * sqrt(-cov)`.
    ///
    /// Returns `None` if not primed or autocovariance is non-negative
    /// (trending market — spread undefined).
    #[inline]
    #[must_use]
    pub fn spread(&self) -> Option<f64> {
        if !self.is_primed() {
            return None;
        }
        if self.ew_cov >= 0.0 {
            return None;
        }
        Some(2.0 * crate::math::sqrt(-self.ew_cov))
    }

    /// Hasbrouck's adjusted spread: `spread * sqrt(1 + rho)` where
    /// `rho = cov / var` is the first-order autocorrelation.
    ///
    /// Returns `None` if Roll spread is `None`, variance is zero,
    /// or `1 + rho <= 0` (extreme mean-reversion).
    #[inline]
    #[must_use]
    pub fn hasbrouck_spread(&self) -> Option<f64> {
        let s = self.spread()?;
        if self.ew_var <= 0.0 {
            return None;
        }
        let rho = self.ew_cov / self.ew_var;
        let factor = 1.0 + rho;
        if factor <= 0.0 {
            return None;
        }
        Some(s * crate::math::sqrt(factor))
    }

    /// Raw exponentially weighted autocovariance, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn autocovariance(&self) -> Option<f64> {
        if self.is_primed() {
            Some(self.ew_cov)
        } else {
            None
        }
    }

    /// Number of prices seen.
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

    /// Resets to uninitialized state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.ew_cov = 0.0;
        self.ew_var = 0.0;
        self.prev_price = 0.0;
        self.prev_diff = 0.0;
        self.count = 0;
    }
}

impl RollSpreadBuilder {
    /// EW decay factor (required, in (0, 1)).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Minimum prices before results are valid. Default: 30.
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
    /// - Alpha must have been set and be in (0, 1).
    #[inline]
    pub fn build(self) -> Result<RollSpread, crate::ConfigError> {
        let alpha = self.alpha.ok_or(crate::ConfigError::Missing("alpha"))?;
        if alpha <= 0.0 || alpha >= 1.0 || !alpha.is_finite() {
            return Err(crate::ConfigError::Invalid(
                "RollSpread alpha must be in (0, 1)",
            ));
        }

        Ok(RollSpread {
            alpha,
            one_minus_alpha: 1.0 - alpha,
            ew_cov: 0.0,
            ew_var: 0.0,
            prev_price: 0.0,
            prev_diff: 0.0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mean_reverting_spread() {
        let mut rs = RollSpread::builder()
            .alpha(0.05)
            .min_samples(10)
            .build()
            .unwrap();

        for i in 0..200 {
            let price = 100.0 + if i % 2 == 0 { 0.5 } else { -0.5 };
            rs.update(price).unwrap();
        }

        let spread = rs.spread();
        assert!(spread.is_some(), "mean-reverting should produce a spread");
        assert!(spread.unwrap() > 0.0, "spread should be positive");
    }

    #[test]
    fn trending_no_spread() {
        let mut rs = RollSpread::builder()
            .alpha(0.05)
            .min_samples(10)
            .build()
            .unwrap();

        for i in 0..200 {
            rs.update((i as f64).mul_add(0.1, 100.0)).unwrap();
        }

        assert!(
            rs.spread().is_none(),
            "trending series should have no spread (positive autocov)"
        );
    }

    #[test]
    fn hasbrouck_vs_roll() {
        let mut rs = RollSpread::builder()
            .alpha(0.05)
            .min_samples(10)
            .build()
            .unwrap();

        // Trend + bounce: negative autocov but rho > -1
        for i in 0..200 {
            let bounce = if i % 2 == 0 { 0.2 } else { -0.2 };
            rs.update((i as f64).mul_add(0.1, 100.0) + bounce).unwrap();
        }

        let roll = rs.spread().unwrap();
        let hasbrouck = rs.hasbrouck_spread().unwrap();
        assert!(
            hasbrouck > 0.0 && hasbrouck <= roll * 1.5,
            "Hasbrouck ({hasbrouck}) should be positive and reasonable vs Roll ({roll})"
        );
    }

    #[test]
    fn autocovariance_negative() {
        let mut rs = RollSpread::builder()
            .alpha(0.05)
            .min_samples(10)
            .build()
            .unwrap();

        for i in 0..200 {
            let price = 100.0 + if i % 2 == 0 { 0.5 } else { -0.5 };
            rs.update(price).unwrap();
        }

        let cov = rs.autocovariance().unwrap();
        assert!(
            cov < 0.0,
            "mean-reverting should have negative autocov, got {cov}"
        );
    }

    #[test]
    fn reset_clears() {
        let mut rs = RollSpread::builder()
            .alpha(0.05)
            .min_samples(10)
            .build()
            .unwrap();

        for i in 0..50 {
            let price = 100.0 + if i % 2 == 0 { 0.5 } else { -0.5 };
            rs.update(price).unwrap();
        }
        rs.reset();
        assert_eq!(rs.count(), 0);
        assert!(rs.spread().is_none());
    }

    #[test]
    fn nan_rejected() {
        let mut rs = RollSpread::builder().alpha(0.05).build().unwrap();
        assert!(matches!(
            rs.update(f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
    }

    #[test]
    fn inf_rejected() {
        let mut rs = RollSpread::builder().alpha(0.05).build().unwrap();
        assert!(matches!(
            rs.update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        ));
    }

    #[test]
    fn builder_validation() {
        assert!(matches!(
            RollSpread::builder().build(),
            Err(crate::ConfigError::Missing("alpha"))
        ));
        assert!(matches!(
            RollSpread::builder().alpha(0.0).build(),
            Err(crate::ConfigError::Invalid(_))
        ));
        assert!(matches!(
            RollSpread::builder().alpha(1.0).build(),
            Err(crate::ConfigError::Invalid(_))
        ));
    }
}
