use crate::smoothing::Ema;

/// Streaming Amihud ILLIQ ratio — illiquidity measure.
///
/// Computes the exponentially weighted average of |return| / dollar_volume.
/// Higher values indicate less liquid instruments (larger price impact per
/// unit of volume). This is the standard Amihud (2002) illiquidity measure.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::Amihud;
///
/// let mut amihud = Amihud::builder()
///     .alpha(0.05)
///     .build()
///     .unwrap();
///
/// amihud.update(0.01, 1_000_000.0).unwrap(); // 1% return, $1M volume
/// let illiq = amihud.illiq().unwrap();
/// assert!(illiq > 0.0);
/// ```
#[derive(Debug, Clone)]
pub struct Amihud {
    ema: Ema,
    count: u64,
}

/// Builder for [`Amihud`].
#[derive(Debug, Clone)]
pub struct AmihudBuilder {
    alpha: Option<f64>,
}

impl Amihud {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> AmihudBuilder {
        AmihudBuilder { alpha: None }
    }

    /// Feed an absolute return and dollar volume for one period.
    ///
    /// `abs_return` should be the absolute value of the return (e.g., `|r|`).
    /// A `dollar_volume` of zero means no trading happened: the period is
    /// skipped and `count()` does not advance, so a caller can tell.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` / `Infinite` if either value is NaN or
    /// infinite, `DataError::Negative` for a negative volume, and
    /// `DataError::Infinite` if the ratio itself overflows.
    #[inline]
    pub fn update(&mut self, abs_return: f64, dollar_volume: f64) -> Result<(), crate::DataError> {
        check_finite!(abs_return);
        check_finite!(dollar_volume);
        if dollar_volume < 0.0 {
            return Err(crate::DataError::Negative);
        }
        if dollar_volume == 0.0 {
            return Ok(());
        }
        let ratio = abs_return / dollar_volume;
        self.ema.checked_update(ratio)?;
        self.count += 1;
        Ok(())
    }

    /// Current ILLIQ ratio (EMA of |return| / volume), or `None` before the
    /// first positive-volume period.
    #[inline]
    #[must_use]
    pub fn illiq(&self) -> Option<f64> {
        self.ema.value()
    }

    /// Number of valid observations (positive-volume periods).
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough observations have been fed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.ema.is_primed()
    }

    /// Reset all state.
    pub fn reset(&mut self) {
        self.ema.reset();
        self.count = 0;
    }
}

impl AmihudBuilder {
    /// Direct smoothing factor. Must be in (0, 1).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Samples for weight to decay by half.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.alpha = Some(crate::math::alpha_from_halflife(halflife));
        self
    }

    /// Build the Amihud ILLIQ tracker.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if alpha is missing or invalid.
    #[inline]
    pub fn build(self) -> Result<Amihud, crate::ConfigError> {
        let alpha = self.alpha.ok_or(crate::ConfigError::Missing("alpha"))?;

        let ema = Ema::builder().alpha(alpha).build()?;

        Ok(Amihud { ema, count: 0 })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_illiq() {
        let mut a = Amihud::builder().alpha(0.1).build().unwrap();
        a.update(0.01, 1_000_000.0).unwrap();
        let illiq = a.illiq().unwrap();
        assert!(illiq > 0.0);
        assert!((illiq - 1e-8).abs() < 1e-10);
    }

    #[test]
    fn higher_impact_higher_illiq() {
        let mut liquid = Amihud::builder().alpha(0.5).build().unwrap();
        let mut illiquid = Amihud::builder().alpha(0.5).build().unwrap();

        for _ in 0..50 {
            liquid.update(0.001, 10_000_000.0).unwrap();
            illiquid.update(0.01, 100_000.0).unwrap();
        }

        assert!(
            illiquid.illiq().unwrap() > liquid.illiq().unwrap(),
            "illiquid ({}) should have higher ILLIQ than liquid ({})",
            illiquid.illiq().unwrap(),
            liquid.illiq().unwrap()
        );
    }

    #[test]
    fn zero_volume_skipped() {
        let mut a = Amihud::builder().alpha(0.1).build().unwrap();
        a.update(0.01, 0.0).unwrap();
        assert_eq!(a.count(), 0);
        assert!(!a.is_primed());
    }

    #[test]
    fn reset_clears_state() {
        let mut a = Amihud::builder().alpha(0.1).build().unwrap();
        a.update(0.01, 1_000_000.0).unwrap();
        a.reset();
        assert_eq!(a.count(), 0);
        assert!(!a.is_primed());
    }

    #[test]
    fn nan_rejected() {
        let mut a = Amihud::builder().alpha(0.1).build().unwrap();
        assert!(a.update(f64::NAN, 1.0).is_err());
        assert!(a.update(1.0, f64::NAN).is_err());
    }

    #[test]
    fn inf_rejected() {
        let mut a = Amihud::builder().alpha(0.1).build().unwrap();
        assert!(a.update(f64::INFINITY, 1.0).is_err());
    }
}
