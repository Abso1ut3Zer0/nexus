use nexus_stats_core::parts::EwWeight;
use nexus_stats_smoothing::Ema;

/// Amihud illiquidity: the exponentially weighted average of
/// `|return| / dollar_volume`.
///
/// A higher value means a less liquid instrument: more price movement per
/// unit of volume. The ratio is Amihud's (2002, "Illiquidity and stock
/// returns", *Journal of Financial Markets*); he averages it equally over a
/// period, and this type weights it exponentially. Periods with no volume
/// are left out: the ratio is undefined there.
///
/// The value is in return per unit of volume. Amihud reports it multiplied
/// by `1e6`.
///
/// # Examples
///
/// ```
/// use nexus_stats_trading::Amihud;
///
/// let mut amihud = Amihud::builder().alpha(0.5).build().unwrap();
/// amihud.update(-0.01, 1_000_000.0); // a 1% fall on $1M of volume
/// assert_eq!(amihud.illiq(), Some(1e-8));
/// ```
#[derive(Debug, Clone)]
pub struct Amihud {
    ratio: Ema,
}

/// Builder for [`Amihud`].
#[derive(Debug, Clone)]
pub struct AmihudBuilder {
    weight: Option<EwWeight>,
}

impl Amihud {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> AmihudBuilder {
        AmihudBuilder { weight: None }
    }

    /// Feeds one period's return and dollar volume.
    ///
    /// The return may be signed; its magnitude is used. A period with zero
    /// volume is left out and `count()` does not advance.
    ///
    /// Does not validate its inputs; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, period_return: f64, dollar_volume: f64) {
        // No trading: the ratio is undefined, so the period is left out.
        if dollar_volume == 0.0 {
            return;
        }
        self.ratio.update(period_return.abs() / dollar_volume);
    }

    /// Checked update. Feeds the period, or returns an error and leaves the
    /// tracker unchanged.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber) if either
    ///   value is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if either value
    ///   is infinite.
    /// - [`DataError::Negative`](nexus_stats_core::DataError::Negative) if
    ///   `dollar_volume` is negative.
    /// - [`DataError::OutOfRange`](nexus_stats_core::DataError::OutOfRange) if the
    ///   ratio overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_trading::{DataError, Amihud};
    ///
    /// let mut amihud = Amihud::builder().alpha(0.5).build().unwrap();
    /// assert_eq!(amihud.checked_update(0.01, 1_000_000.0), Ok(()));
    /// assert_eq!(amihud.checked_update(0.01, -1.0), Err(DataError::Negative));
    /// assert_eq!(amihud.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(
        &mut self,
        period_return: f64,
        dollar_volume: f64,
    ) -> Result<(), nexus_stats_core::DataError> {
        nexus_stats_core::math::check_inputs!(period_return, dollar_volume)?;
        if dollar_volume < 0.0 {
            return Err(nexus_stats_core::DataError::Negative);
        }
        if dollar_volume > 0.0 && (period_return.abs() / dollar_volume).is_infinite() {
            return Err(nexus_stats_core::DataError::OutOfRange);
        }
        self.update(period_return, dollar_volume);
        Ok(())
    }

    /// The illiquidity ratio, or `None` before the first period with volume.
    #[must_use]
    pub fn illiq(&self) -> Option<f64> {
        self.ratio.value()
    }

    /// Number of periods fed that had volume.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.ratio.count()
    }

    /// Whether a period with volume has been fed.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.ratio.is_primed()
    }

    /// Resets to no periods. Parameters unchanged.
    pub fn reset(&mut self) {
        self.ratio.reset();
    }
}

impl AmihudBuilder {
    /// Direct smoothing factor. Must be in (0, 1) exclusive.
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Periods for weight to decay by half. Must be positive and finite.
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Span in periods (`alpha = 2 / (n + 1)`). Must be at least 2.
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(EwWeight::Span(n));
        self
    }

    /// Builds the tracker.
    ///
    /// # Errors
    ///
    /// - `Missing("alpha")` if none of `alpha`, `halflife`, `span` was set.
    /// - `Invalid` if the weight is out of range; the message names the knob
    ///   set.
    pub fn build(self) -> Result<Amihud, nexus_stats_core::ConfigError> {
        let alpha = self
            .weight
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?
            .resolve()?;
        Ok(Amihud {
            ratio: Ema::builder().alpha(alpha).build()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_illiq() {
        let mut a = Amihud::builder().alpha(0.1).build().unwrap();
        a.update(0.01, 1_000_000.0);
        let illiq = a.illiq().unwrap();
        assert!(illiq > 0.0);
        assert!((illiq - 1e-8).abs() < 1e-10);
    }

    #[test]
    fn higher_impact_higher_illiq() {
        let mut liquid = Amihud::builder().alpha(0.5).build().unwrap();
        let mut illiquid = Amihud::builder().alpha(0.5).build().unwrap();

        for _ in 0..50 {
            liquid.update(0.001, 10_000_000.0);
            illiquid.update(0.01, 100_000.0);
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
        a.update(0.01, 0.0);
        assert_eq!(a.count(), 0);
        assert!(!a.is_primed());
    }

    #[test]
    fn reset_clears_state() {
        let mut a = Amihud::builder().alpha(0.1).build().unwrap();
        a.update(0.01, 1_000_000.0);
        a.reset();
        assert_eq!(a.count(), 0);
        assert!(!a.is_primed());
    }

    #[test]
    fn the_magnitude_of_a_signed_return_is_used() {
        let mut up = Amihud::builder().alpha(0.5).build().unwrap();
        let mut down = up.clone();
        up.update(0.01, 1_000_000.0);
        down.update(-0.01, 1_000_000.0);
        assert_eq!(up.illiq(), Some(1e-8));
        assert_eq!(down.illiq(), Some(1e-8));
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use nexus_stats_core::DataError::{Infinite, Negative, NotANumber, OutOfRange};

        let mut a = Amihud::builder().alpha(0.5).build().unwrap();
        a.checked_update(0.01, 1_000_000.0).unwrap();
        let before = (a.count(), a.illiq());

        assert_eq!(a.checked_update(f64::NAN, 1.0), Err(NotANumber));
        assert_eq!(a.checked_update(1.0, f64::NAN), Err(NotANumber));
        assert_eq!(a.checked_update(f64::INFINITY, 1.0), Err(Infinite));
        assert_eq!(a.checked_update(1.0, f64::INFINITY), Err(Infinite));
        assert_eq!(a.checked_update(0.01, -1.0), Err(Negative));
        // Finite inputs whose ratio is not.
        assert_eq!(a.checked_update(1e300, 1e-300), Err(OutOfRange));

        assert_eq!((a.count(), a.illiq()), before);
    }

    #[test]
    fn checked_update_skips_zero_volume_like_update() {
        let mut a = Amihud::builder().alpha(0.5).build().unwrap();
        assert_eq!(a.checked_update(0.01, 0.0), Ok(()));
        assert_eq!(a.checked_update(0.0, 0.0), Ok(()));
        // Negative zero is zero, not a negative volume.
        assert_eq!(a.checked_update(0.01, -0.0), Ok(()));
        assert_eq!((a.count(), a.illiq()), (0, None));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = Amihud::builder().alpha(0.2).build().unwrap();
        let mut unchecked = checked.clone();
        for (r, v) in [(0.01, 1e6), (-0.02, 5e5), (0.0, 1e6), (0.03, 0.0)] {
            checked.checked_update(r, v).unwrap();
            unchecked.update(r, v);
        }
        assert_eq!(checked.count(), unchecked.count());
        assert_eq!(checked.illiq(), unchecked.illiq());
    }

    #[test]
    fn update_does_not_validate() {
        let mut a = Amihud::builder().alpha(0.5).build().unwrap();
        a.update(f64::NAN, 1.0);
        assert!(a.illiq().unwrap().is_nan());
    }

    #[test]
    fn a_bad_knob_is_reported_under_its_own_name() {
        use nexus_stats_core::ConfigError::{Invalid, Missing};
        let b = Amihud::builder;
        assert_eq!(b().build().unwrap_err(), Missing("alpha"));
        assert_eq!(
            b().span(1).build().unwrap_err(),
            Invalid("span must be at least 2")
        );
        assert_eq!(b().span(3).build().unwrap().illiq(), None);
    }
}
