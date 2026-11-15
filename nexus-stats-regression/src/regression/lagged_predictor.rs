use alloc::collections::VecDeque;

use crate::regression::EwLinearRegression;

/// Streaming lagged prediction quality measurement.
///
/// Maintains a ring buffer of past estimates. On each update, regresses
/// the estimate from K ticks ago against the current realized value.
/// R² = prediction quality. Slope = calibration (1.0 = perfect).
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::regression::LaggedPredictor;
///
/// let mut predictor = LaggedPredictor::builder()
///     .lag(5)
///     .halflife(100.0)
///     .build()
///     .unwrap();
///
/// // Feed data: the regression pairs estimate_{t-5} with realized_t.
/// // With a linear series, lagged estimates are highly correlated with
/// // future realized values, so R² will be high.
/// for i in 0..200 {
///     predictor.update(i as f64, i as f64).unwrap();
/// }
///
/// if predictor.is_primed() {
///     let r2 = predictor.r_squared().unwrap();
///     assert!(r2 > 0.9);
/// }
/// ```
#[derive(Debug, Clone)]
pub struct LaggedPredictor {
    lag: usize,
    history: VecDeque<f64>,
    regression: EwLinearRegression,
    count: u64,
}

/// Builder for [`LaggedPredictor`].
#[derive(Debug, Clone)]
pub struct LaggedPredictorBuilder {
    lag: Option<usize>,
    halflife: Option<f64>,
}

impl LaggedPredictor {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> LaggedPredictorBuilder {
        LaggedPredictorBuilder {
            lag: None,
            halflife: None,
        }
    }

    /// Feed an estimate and the current realized value.
    ///
    /// The estimate is stored in the ring buffer. Once the buffer reaches
    /// `lag` depth, each update regresses the oldest estimate against the
    /// current realized value, then discards the oldest.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if either value is NaN or infinite.
    #[inline]
    pub fn update(
        &mut self,
        estimate: f64,
        realized: f64,
    ) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(estimate);
        check_finite!(realized);

        self.history.push_back(estimate);
        self.count += 1;

        if self.history.len() > self.lag {
            let lagged_estimate = self
                .history
                .pop_front()
                .expect("history non-empty: checked len > lag");
            self.regression.update(lagged_estimate, realized)?;
        }

        Ok(())
    }

    /// R² of the lagged regression. `None` if not primed.
    #[inline]
    #[must_use]
    pub fn r_squared(&self) -> Option<f64> {
        self.regression.r_squared()
    }

    /// Slope of the lagged regression. 1.0 = perfectly calibrated.
    #[inline]
    #[must_use]
    pub fn slope(&self) -> Option<f64> {
        self.regression.slope()
    }

    /// Intercept of the lagged regression.
    #[inline]
    #[must_use]
    pub fn intercept(&self) -> Option<f64> {
        self.regression.intercept_value()
    }

    /// The lag (number of ticks between estimate and evaluation).
    #[inline]
    #[must_use]
    pub fn lag(&self) -> usize {
        self.lag
    }

    /// Total number of observations fed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough observations have been fed for regression to be meaningful.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.regression.slope().is_some()
    }

    /// Reset all state (ring buffer and regression).
    pub fn reset(&mut self) {
        self.history.clear();
        self.regression.reset();
        self.count = 0;
    }
}

impl LaggedPredictorBuilder {
    /// How many ticks to look back. Required.
    #[inline]
    #[must_use]
    pub fn lag(mut self, lag: usize) -> Self {
        self.lag = Some(lag);
        self
    }

    /// EW regression halflife (in ticks). Required.
    ///
    /// Controls how quickly old observations fade. Larger halflife = slower
    /// decay = more history.
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.halflife = Some(halflife);
        self
    }

    /// Build the predictor.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if lag or halflife is missing, or if halflife
    /// produces an invalid alpha.
    pub fn build(self) -> Result<LaggedPredictor, nexus_stats_core::ConfigError> {
        let lag = self
            .lag
            .ok_or(nexus_stats_core::ConfigError::Missing("lag"))?;
        if lag == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "lag must be at least 1",
            ));
        }

        let halflife = self
            .halflife
            .ok_or(nexus_stats_core::ConfigError::Missing("halflife"))?;
        if halflife <= 0.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "halflife must be positive",
            ));
        }

        let ln2 = core::f64::consts::LN_2;
        let alpha = 1.0 - nexus_stats_core::math::exp(-ln2 / halflife);

        let regression = EwLinearRegression::builder().alpha(alpha).build()?;

        let mut history = VecDeque::new();
        history.reserve_exact(lag);

        Ok(LaggedPredictor {
            lag,
            history,
            regression,
            count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn perfect_prediction_high_r2() {
        let mut p = LaggedPredictor::builder()
            .lag(1)
            .halflife(50.0)
            .build()
            .unwrap();

        // Linear series: regresses estimate_{t-1} against realized_t.
        // With update(i, i), the pairs are (i-1, i) — nearly perfect linear
        // relationship, so R² ≈ 1.0 and slope ≈ 1.0.
        for i in 0..200 {
            p.update(i as f64, i as f64).unwrap();
        }

        assert!(p.is_primed());
        let r2 = p.r_squared().unwrap();
        assert!(
            r2 > 0.99,
            "R² should be ~1.0 for perfect prediction, got {r2}"
        );
        let slope = p.slope().unwrap();
        assert!(
            (slope - 1.0).abs() < 0.05,
            "slope should be ~1.0, got {slope}"
        );
    }

    #[test]
    fn biased_prediction() {
        let mut p = LaggedPredictor::builder()
            .lag(1)
            .halflife(50.0)
            .build()
            .unwrap();

        // estimate = 2 * realized → slope should be ~0.5
        for i in 0..200 {
            let realized = i as f64;
            let estimate = 2.0 * realized;
            p.update(estimate, realized).unwrap();
        }

        assert!(p.is_primed());
        let slope = p.slope().unwrap();
        assert!(
            (slope - 0.5).abs() < 0.05,
            "slope should be ~0.5, got {slope}"
        );
    }

    #[test]
    fn lag_10_wraps_correctly() {
        let mut p = LaggedPredictor::builder()
            .lag(10)
            .halflife(100.0)
            .build()
            .unwrap();

        for i in 0..500 {
            p.update(i as f64, i as f64).unwrap();
        }

        assert!(p.is_primed());
        let r2 = p.r_squared().unwrap();
        assert!(r2 > 0.99, "R² should be high, got {r2}");
    }

    #[test]
    fn not_primed_before_lag() {
        let mut p = LaggedPredictor::builder()
            .lag(5)
            .halflife(50.0)
            .build()
            .unwrap();

        // Feed fewer than lag observations
        for i in 0..4 {
            p.update(i as f64, i as f64).unwrap();
            assert!(!p.is_primed());
        }
    }

    #[test]
    fn reset_clears_state() {
        let mut p = LaggedPredictor::builder()
            .lag(1)
            .halflife(50.0)
            .build()
            .unwrap();

        for i in 0..100 {
            p.update(i as f64, i as f64).unwrap();
        }
        assert!(p.is_primed());

        p.reset();
        assert!(!p.is_primed());
        assert_eq!(p.count(), 0);
    }

    #[test]
    fn nan_rejected() {
        let mut p = LaggedPredictor::builder()
            .lag(1)
            .halflife(50.0)
            .build()
            .unwrap();
        assert!(p.update(f64::NAN, 1.0).is_err());
        assert!(p.update(1.0, f64::NAN).is_err());
    }

    #[test]
    fn zero_lag_rejected() {
        let result = LaggedPredictor::builder().lag(0).halflife(50.0).build();
        assert!(result.is_err());
    }
}
