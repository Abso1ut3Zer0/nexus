use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::regression::LaggedPredictor;

/// Runs `LaggedPredictor` at multiple lags simultaneously to map
/// how prediction quality decays over time.
///
/// Each lag gets its own predictor with the same EW halflife. The
/// decay curve shows R² at each lag — the point where R² drops below
/// a threshold is the "useful horizon" of the signal.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::regression::SignalDecayCurve;
///
/// let mut curve = SignalDecayCurve::builder()
///     .lags(&[1, 2, 5, 10, 20])
///     .halflife(100.0)
///     .build()
///     .unwrap();
///
/// // Feed noisy predictions: estimate = realized + noise.
/// // At short lags the correlation holds; at longer lags it decays.
/// for i in 0..500u64 {
///     let realized = (i as f64).sin();
///     let noise = (i as f64 * 0.1).cos() * 0.5;
///     curve.update(realized + noise, realized).unwrap();
/// }
///
/// let dc = curve.decay_curve();
/// assert_eq!(dc.len(), 5);
/// ```
#[derive(Debug, Clone)]
pub struct SignalDecayCurve {
    predictors: Box<[LaggedPredictor]>,
    lags: Box<[usize]>,
    count: u64,
}

/// Builder for [`SignalDecayCurve`].
#[derive(Debug, Clone)]
pub struct SignalDecayCurveBuilder {
    lags: Option<Vec<usize>>,
    halflife: Option<f64>,
}

impl SignalDecayCurve {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> SignalDecayCurveBuilder {
        SignalDecayCurveBuilder {
            lags: None,
            halflife: None,
        }
    }

    /// Feed an estimate and realized value to all lag predictors.
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
        for p in &mut self.predictors {
            p.update(estimate, realized)?;
        }
        self.count += 1;
        Ok(())
    }

    /// R² at a specific lag index. `None` if that predictor isn't primed.
    #[inline]
    #[must_use]
    pub fn r_squared_at(&self, lag_idx: usize) -> Option<f64> {
        self.predictors.get(lag_idx)?.r_squared()
    }

    /// The smallest lag (by index) where R² drops below `threshold`.
    ///
    /// Returns `None` if all lags are above threshold or none are primed.
    #[must_use]
    pub fn useful_horizon(&self, threshold: f64) -> Option<usize> {
        for (i, p) in self.predictors.iter().enumerate() {
            if let Some(r2) = p.r_squared()
                && r2 < threshold
            {
                return Some(self.lags[i]);
            }
        }
        None
    }

    /// Full decay curve: `(lag, R²)` for each configured lag.
    #[must_use]
    pub fn decay_curve(&self) -> Vec<(usize, Option<f64>)> {
        self.lags
            .iter()
            .zip(self.predictors.iter())
            .map(|(&lag, p)| (lag, p.r_squared()))
            .collect()
    }

    /// The configured lags.
    #[inline]
    #[must_use]
    pub fn lags(&self) -> &[usize] {
        &self.lags
    }

    /// Number of observations.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether all predictors are primed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.predictors.iter().all(LaggedPredictor::is_primed)
    }

    /// Reset all predictors.
    pub fn reset(&mut self) {
        for p in &mut self.predictors {
            p.reset();
        }
        self.count = 0;
    }
}

impl SignalDecayCurveBuilder {
    /// Set the lags to evaluate. Required. All must be >= 1.
    #[inline]
    #[must_use]
    pub fn lags(mut self, lags: &[usize]) -> Self {
        self.lags = Some(lags.to_vec());
        self
    }

    /// EW regression halflife shared by all predictors. Required.
    #[inline]
    #[must_use]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.halflife = Some(halflife);
        self
    }

    /// Build the decay curve tracker.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if lags or halflife is missing, or if any lag
    /// is zero.
    pub fn build(self) -> Result<SignalDecayCurve, nexus_stats_core::ConfigError> {
        let lags = self
            .lags
            .ok_or(nexus_stats_core::ConfigError::Missing("lags"))?;
        if lags.is_empty() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "at least one lag is required",
            ));
        }
        let halflife = self
            .halflife
            .ok_or(nexus_stats_core::ConfigError::Missing("halflife"))?;

        let mut predictors = Vec::with_capacity(lags.len());
        for &lag in &lags {
            let p = LaggedPredictor::builder()
                .lag(lag)
                .halflife(halflife)
                .build()?;
            predictors.push(p);
        }

        Ok(SignalDecayCurve {
            predictors: predictors.into_boxed_slice(),
            lags: lags.into_boxed_slice(),
            count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decay_curve_length_matches_lags() {
        let mut curve = SignalDecayCurve::builder()
            .lags(&[1, 2, 5, 10])
            .halflife(50.0)
            .build()
            .unwrap();

        for i in 0..200 {
            curve.update(i as f64, i as f64).unwrap();
        }

        let dc = curve.decay_curve();
        assert_eq!(dc.len(), 4);
        assert_eq!(dc[0].0, 1);
        assert_eq!(dc[3].0, 10);
    }

    #[test]
    fn perfect_prediction_high_r2_all_lags() {
        let mut curve = SignalDecayCurve::builder()
            .lags(&[1, 5, 10])
            .halflife(100.0)
            .build()
            .unwrap();

        for i in 0..500 {
            curve.update(i as f64, i as f64).unwrap();
        }

        assert!(curve.is_primed());
        for (_, r2) in curve.decay_curve() {
            let r2 = r2.unwrap();
            assert!(
                r2 > 0.95,
                "R² should be high for perfect prediction, got {r2}"
            );
        }
    }

    #[test]
    fn useful_horizon_when_no_decay() {
        let mut curve = SignalDecayCurve::builder()
            .lags(&[1, 5, 10])
            .halflife(100.0)
            .build()
            .unwrap();

        for i in 0..500 {
            curve.update(i as f64, i as f64).unwrap();
        }

        // All R² > 0.5, so no useful horizon at threshold 0.5
        assert!(curve.useful_horizon(0.5).is_none());
    }

    #[test]
    fn empty_lags_rejected() {
        let result = SignalDecayCurve::builder().lags(&[]).halflife(50.0).build();
        assert!(result.is_err());
    }

    #[test]
    fn reset_clears_state() {
        let mut curve = SignalDecayCurve::builder()
            .lags(&[1, 5])
            .halflife(50.0)
            .build()
            .unwrap();

        for i in 0..100 {
            curve.update(i as f64, i as f64).unwrap();
        }
        curve.reset();
        assert_eq!(curve.count(), 0);
        assert!(!curve.is_primed());
    }

    #[test]
    fn nan_rejected() {
        let mut curve = SignalDecayCurve::builder()
            .lags(&[1, 5])
            .halflife(50.0)
            .build()
            .unwrap();
        assert!(curve.update(f64::NAN, 1.0).is_err());
    }
}
