use crate::regression::EwLinearRegression;

/// Kyle's Lambda — streaming price impact coefficient.
///
/// Regresses price changes (Y) against signed order flow (X). The slope
/// is Kyle's lambda (λ), which measures permanent price impact per unit
/// of informed trading volume. Higher lambda → more informed trading
/// or less liquidity.
///
/// Kyle (1985): ΔP = λ · SignedVolume + ε
///
/// This is a thin wrapper around `EwLinearRegression` that names
/// the concept and documents the domain semantics.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::regression::KyleLambda;
///
/// let mut kyle = KyleLambda::builder()
///     .alpha(0.05)
///     .build()
///     .unwrap();
///
/// // Positive signed volume → positive price change
/// for i in 0..200 {
///     let volume = (i as f64 - 100.0) * 1000.0;
///     let price_change = volume * 0.001; // lambda ≈ 0.001
///     kyle.update(volume, price_change).unwrap();
/// }
///
/// if let Some(lambda) = kyle.lambda() {
///     assert!((lambda - 0.001).abs() < 0.01);
/// }
/// ```
#[derive(Debug, Clone)]
pub struct KyleLambda {
    regression: EwLinearRegression,
}

/// Builder for [`KyleLambda`].
#[derive(Debug, Clone)]
pub struct KyleLambdaBuilder {
    alpha: Option<f64>,
}

impl KyleLambda {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> KyleLambdaBuilder {
        KyleLambdaBuilder { alpha: None }
    }

    /// Feed a (signed_volume, price_change) observation.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if either value is NaN or infinite.
    #[inline]
    pub fn update(
        &mut self,
        signed_volume: f64,
        price_change: f64,
    ) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(signed_volume);
        check_finite!(price_change);

        self.regression.update(signed_volume, price_change)
    }

    /// Kyle's lambda (price impact coefficient). Slope of the regression.
    #[inline]
    #[must_use]
    pub fn lambda(&self) -> Option<f64> {
        self.regression.slope()
    }

    /// R² of the price-impact regression.
    #[inline]
    #[must_use]
    pub fn r_squared(&self) -> Option<f64> {
        self.regression.r_squared()
    }

    /// Intercept of the regression (should be near zero in efficient markets).
    #[inline]
    #[must_use]
    pub fn intercept(&self) -> Option<f64> {
        self.regression.intercept()
    }

    /// Number of observations.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.regression.count()
    }

    /// Whether enough observations for regression.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.regression.is_primed()
    }

    /// Reset all state.
    #[inline]
    pub fn reset(&mut self) {
        self.regression.reset();
    }
}

impl KyleLambdaBuilder {
    /// EW smoothing factor. Must be in (0, 1). Required.
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
        self.alpha = Some(nexus_stats_core::math::alpha_from_halflife(halflife));
        self
    }

    /// Build the Kyle lambda tracker.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if alpha is missing or invalid.
    #[inline]
    pub fn build(self) -> Result<KyleLambda, nexus_stats_core::ConfigError> {
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;

        let regression = EwLinearRegression::builder().alpha(alpha).build()?;

        Ok(KyleLambda { regression })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_lambda() {
        let mut kyle = KyleLambda::builder().alpha(0.05).build().unwrap();

        // lambda = 0.001: price_change = 0.001 * signed_volume
        for i in 0..500 {
            let vol = (i as f64 - 250.0) * 1000.0;
            let dp = vol * 0.001;
            kyle.update(vol, dp).unwrap();
        }

        assert!(kyle.is_primed());
        let lambda = kyle.lambda().unwrap();
        assert!(
            (lambda - 0.001).abs() < 0.0005,
            "lambda should be ~0.001, got {lambda}"
        );
        let r2 = kyle.r_squared().unwrap();
        assert!(r2 > 0.99, "R² should be ~1.0, got {r2}");
    }

    #[test]
    fn no_relationship_low_r2() {
        let mut kyle = KyleLambda::builder().alpha(0.05).build().unwrap();

        // Uncorrelated: volume and price change independent
        for i in 0..500 {
            let vol = (i as f64 - 250.0) * 100.0;
            // Price change unrelated to volume — just monotonic
            let dp = (i as f64) * 0.01;
            kyle.update(vol, dp).unwrap();
        }

        assert!(kyle.is_primed());
        // Lambda and R² should be available once primed.
        assert!(kyle.lambda().is_some());
        assert!(kyle.r_squared().is_some());
    }

    #[test]
    fn reset_clears_state() {
        let mut kyle = KyleLambda::builder().alpha(0.05).build().unwrap();
        for i in 0..100 {
            kyle.update(i as f64, i as f64 * 0.5).unwrap();
        }
        kyle.reset();
        assert_eq!(kyle.count(), 0);
        assert!(!kyle.is_primed());
    }

    #[test]
    fn nan_rejected() {
        let mut kyle = KyleLambda::builder().alpha(0.05).build().unwrap();
        assert!(kyle.update(f64::NAN, 1.0).is_err());
        assert!(kyle.update(1.0, f64::NAN).is_err());
    }

    #[test]
    fn inf_rejected() {
        let mut kyle = KyleLambda::builder().alpha(0.05).build().unwrap();
        assert!(kyle.update(f64::INFINITY, 1.0).is_err());
    }
}
