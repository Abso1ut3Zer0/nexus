use nexus_stats_core::statistics::Percentile;

/// Conditional Value at Risk (Expected Shortfall).
///
/// Streaming CVaR at confidence level alpha. CVaR_α is the expected
/// value of outcomes in the worst α fraction:
///
/// CVaR_α = E[X | X <= VaR_α]
///
/// Composes a P² percentile estimator internally for VaR estimation.
/// Tail samples (those at or below the estimated VaR) are accumulated
/// for the conditional mean.
///
/// # Examples
///
/// ```
/// use nexus_stats_trading::Cvar;
///
/// let mut cvar = Cvar::builder().alpha(0.05).build().unwrap();
/// // Cycling input so tail samples accumulate after P² converges
/// for i in 0..5000u64 {
///     cvar.update((i % 1000 + 1) as f64).unwrap();
/// }
/// let cv = cvar.cvar().unwrap();
/// let var = cvar.var().unwrap();
/// assert!(cv < 500.0 && cv > 0.0);
/// ```
#[derive(Debug, Clone)]
pub struct Cvar {
    percentile: Percentile,
    tail_sum: f64,
    tail_count: u64,
    count: u64,
    alpha: f64,
}

/// Builder for [`Cvar`].
#[derive(Debug, Clone)]
pub struct CvarBuilder {
    alpha: Option<f64>,
}

impl Cvar {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> CvarBuilder {
        CvarBuilder { alpha: None }
    }

    /// Feeds a sample.
    ///
    /// Samples below the current VaR estimate contribute to the
    /// CVaR (conditional tail mean). The VaR estimate is updated
    /// via the internal P² percentile tracker.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(sample);
        self.percentile.update(sample)?;
        self.count += 1;

        if self.percentile.is_primed()
            && let Some(var) = self.percentile.percentile()
            && sample <= var
        {
            self.tail_sum += sample;
            self.tail_count += 1;
        }

        Ok(())
    }

    /// CVaR (Expected Shortfall): mean of tail observations.
    ///
    /// Returns `None` if not primed or no tail observations.
    #[inline]
    #[must_use]
    pub fn cvar(&self) -> Option<f64> {
        if !self.is_primed() || self.tail_count == 0 {
            return None;
        }
        Some(self.tail_sum / self.tail_count as f64)
    }

    /// VaR (Value at Risk): the alpha-quantile.
    ///
    /// Delegates to the internal P² percentile estimator.
    #[inline]
    #[must_use]
    pub fn var(&self) -> Option<f64> {
        self.percentile.percentile()
    }

    /// Confidence level.
    #[inline]
    #[must_use]
    pub fn alpha(&self) -> f64 {
        self.alpha
    }

    /// Number of samples classified into the tail.
    #[inline]
    #[must_use]
    pub fn tail_count(&self) -> u64 {
        self.tail_count
    }

    /// Total samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the VaR estimate is primed and at least one tail
    /// observation has been recorded.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.percentile.is_primed() && self.tail_count >= 1
    }

    /// Resets all state. Alpha is preserved.
    #[inline]
    pub fn reset(&mut self) {
        self.percentile.reset();
        self.tail_sum = 0.0;
        self.tail_count = 0;
        self.count = 0;
    }
}

impl CvarBuilder {
    /// Confidence level in (0, 1) exclusive.
    ///
    /// For 5% CVaR (worst 5%): `alpha(0.05)`.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Builds the CVaR tracker.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if alpha is missing or not in (0, 1).
    #[inline]
    pub fn build(self) -> Result<Cvar, nexus_stats_core::ConfigError> {
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        if !nexus_stats_core::math::in_unit_interval(alpha) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1) exclusive",
            ));
        }

        let percentile = Percentile::new(alpha)?;

        Ok(Cvar {
            percentile,
            tail_sum: 0.0,
            tail_count: 0,
            count: 0,
            alpha,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_distribution() {
        let mut cv = Cvar::builder().alpha(0.05).build().unwrap();
        // Cycling [1..1000] ensures tail samples accumulate after P² converges
        for i in 0..10_000u64 {
            let v = (i % 1000 + 1) as f64;
            cv.update(v).unwrap();
        }
        assert!(cv.tail_count() > 0, "should have tail observations");
        let cvar = cv.cvar().unwrap();
        assert!(cvar < 500.0, "CVaR should be below median, got {cvar}");
        assert!(cvar > 0.0, "CVaR should be positive, got {cvar}");
    }

    #[test]
    fn var_matches_percentile() {
        let mut cv = Cvar::builder().alpha(0.10).build().unwrap();
        let mut p = Percentile::new(0.10).unwrap();
        for i in 1..=500 {
            let v = i as f64;
            cv.update(v).unwrap();
            p.update(v).unwrap();
        }
        let var = cv.var().unwrap();
        let pct = p.percentile().unwrap();
        assert!(
            (var - pct).abs() < 1.0,
            "VaR {var} should match percentile {pct}"
        );
    }

    #[test]
    fn empty_returns_none() {
        let cv = Cvar::builder().alpha(0.05).build().unwrap();
        assert!(cv.cvar().is_none());
        assert!(cv.var().is_none());
        assert!(!cv.is_primed());
    }

    #[test]
    fn priming_phase() {
        let mut cv = Cvar::builder().alpha(0.05).build().unwrap();
        // The tail quantile primes at the P² rule `1 / (p (1 - p))`, not at a
        // fixed count; the estimator says how many it needs.
        let needed = cv.percentile.min_samples();
        assert!(needed > 5, "a 5% tail needs more than the five markers");
        for i in 1..needed {
            cv.update(i as f64).unwrap();
            assert!(!cv.percentile.is_primed(), "not primed at {i} of {needed}");
            assert!(cv.cvar().is_none());
        }
        cv.update(needed as f64).unwrap();
        assert!(cv.percentile.is_primed());
        // CVaR also needs a sample in the tail, which only accrues once the
        // quantile exists; the priming sample itself is not yet counted.
        assert!(cv.cvar().is_none(), "no tail sample yet");
        // Extreme samples on both sides guarantee a tail hit whichever tail
        // the alpha names.
        for i in 0..20 {
            cv.update(if i % 2 == 0 { -1.0e6 } else { 1.0e6 }).unwrap();
        }
        assert!(cv.cvar().is_some(), "extreme samples land in the tail");
    }

    #[test]
    fn all_equal() {
        let mut cv = Cvar::builder().alpha(0.05).build().unwrap();
        for _ in 0..200 {
            cv.update(42.0).unwrap();
        }
        let cvar = cv.cvar().expect("200 samples prime the estimator");
        assert!(
            (cvar - 42.0).abs() < 1e-6,
            "constant stream: CVaR should equal the constant, got {cvar}"
        );
        let var = cv.var().expect("200 samples prime the estimator");
        assert!(
            (var - 42.0).abs() < 1e-6,
            "constant stream: VaR should equal the constant, got {var}"
        );
    }

    #[test]
    fn tail_heavier_than_var() {
        let mut cv = Cvar::builder().alpha(0.10).build().unwrap();
        for i in 0..10_000u64 {
            let v = (i % 1000 + 1) as f64;
            cv.update(v).unwrap();
        }
        let cvar = cv.cvar().unwrap();
        let var = cv.var().unwrap();
        // Streaming CVaR may slightly exceed VaR from early misclassification
        // during P² convergence. Allow 1.5x tolerance.
        assert!(
            cvar < var * 1.5,
            "CVaR ({cvar}) should be roughly <= VaR ({var})"
        );
        assert!(
            cv.tail_count() > 100,
            "should have many tail observations at alpha=0.10"
        );
    }

    #[test]
    fn rejects_nan_inf() {
        let mut cv = Cvar::builder().alpha(0.05).build().unwrap();
        assert!(cv.update(f64::NAN).is_err());
        assert!(cv.update(f64::INFINITY).is_err());
        assert!(cv.update(f64::NEG_INFINITY).is_err());
        assert_eq!(cv.count(), 0);
    }

    #[test]
    fn reset_clears() {
        let mut cv = Cvar::builder().alpha(0.05).build().unwrap();
        for i in 1..=100 {
            cv.update(i as f64).unwrap();
        }
        assert!(cv.count() > 0);
        cv.reset();
        assert_eq!(cv.count(), 0);
        assert_eq!(cv.tail_count(), 0);
        assert!(cv.cvar().is_none());
        assert!(cv.var().is_none());
        assert!((cv.alpha() - 0.05).abs() < 1e-10);
    }
}
