use crate::smoothing::{Ema, EmaBuilder};

/// Streaming Amihud illiquidity ratio (Amihud, 2002).
///
/// Amihud's measure is the average over periods of `|return| / dollar
/// volume`: the price move per unit of money traded. Higher values mean a
/// less liquid instrument. This type keeps an exponentially weighted
/// average of the per-period ratio, so it follows changing liquidity.
///
/// Periods with zero dollar volume are left out, as in the original
/// measure: with no trading the ratio is undefined.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::Amihud;
///
/// let mut amihud = Amihud::builder().alpha(0.5).build().unwrap();
///
/// // A 1% move on $1M traded, either direction.
/// assert_eq!(amihud.update(-0.01, 1_000_000.0), Some(1e-8));
/// // A 2% move on $1M: the ratio doubles and the average moves halfway.
/// let illiq = amihud.update(0.02, 1_000_000.0).unwrap();
/// assert!((illiq - 1.5e-8).abs() < 1e-20);
/// // No trading: the period is skipped and the reading is unchanged.
/// assert_eq!(amihud.update(0.05, 0.0), Some(illiq));
/// assert_eq!(amihud.count(), 2);
/// ```
#[derive(Debug, Clone)]
pub struct Amihud {
    ema: Ema,
}

/// Builder for [`Amihud`].
#[derive(Debug, Clone)]
pub struct AmihudBuilder {
    ema: EmaBuilder,
}

impl Amihud {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> AmihudBuilder {
        AmihudBuilder {
            ema: Ema::builder(),
        }
    }

    /// Feeds one period's return and dollar volume. Returns the
    /// illiquidity ratio as [`illiq`](Self::illiq) does.
    ///
    /// The return may have either sign; its absolute value is used. A
    /// `dollar_volume` of zero means no trading happened: the period is
    /// skipped, `count()` does not advance and the current reading is
    /// returned unchanged.
    ///
    /// Unchecked, like `f64` arithmetic: a NaN, an infinity, a negative
    /// volume or a ratio too large to represent is folded in as it is, and
    /// the reading is not meaningful from then on, until
    /// [`reset`](Self::reset). Use
    /// [`checked_update`](Self::checked_update) to have such a period
    /// refused instead.
    #[inline]
    pub fn update(&mut self, ret: f64, dollar_volume: f64) -> Option<f64> {
        #[allow(clippy::float_cmp)]
        if dollar_volume == 0.0 {
            return self.illiq();
        }
        self.ema.fold(ret.abs() / dollar_volume)
    }

    /// [`update`](Self::update) with the period validated first, leaving
    /// the state untouched if it is refused. Fed only through this method
    /// the ratio is always a finite, non-negative number.
    ///
    /// # Errors
    ///
    /// `DataError::NotANumber` / `Infinite` if either value is NaN or
    /// infinite, `DataError::Negative` for a negative volume, and
    /// `DataError::OutOfRange` if the ratio is too large to represent (a
    /// vanishing volume against a large return).
    #[inline]
    pub fn checked_update(
        &mut self,
        ret: f64,
        dollar_volume: f64,
    ) -> Result<Option<f64>, crate::DataError> {
        check_finite!(ret);
        check_finite!(dollar_volume);
        if dollar_volume < 0.0 {
            return Err(crate::DataError::Negative);
        }
        if dollar_volume > 0.0 && !(ret.abs() / dollar_volume).is_finite() {
            return Err(crate::DataError::OutOfRange);
        }
        Ok(self.update(ret, dollar_volume))
    }

    /// Current illiquidity ratio (the weighted average of `|return| /
    /// dollar volume`), or `None` before the first positive-volume period.
    /// Never negative.
    #[inline]
    #[must_use]
    pub fn illiq(&self) -> Option<f64> {
        self.ema.value()
    }

    /// Number of periods used: those with positive volume.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.ema.count()
    }

    /// Whether a reading is available.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.ema.is_primed()
    }

    /// Reset all state.
    #[inline]
    pub fn reset(&mut self) {
        self.ema.reset();
    }
}

impl AmihudBuilder {
    /// Direct smoothing factor. Must be in (0, 1).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.ema = self.ema.alpha(alpha);
        self
    }

    /// Periods for weight to decay by half. Must be positive and finite.
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.ema = self.ema.halflife(halflife);
        self
    }

    /// Span in periods (the pandas `span` convention). Must be at least 2.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.ema = self.ema.span(n);
        self
    }

    /// Build the Amihud illiquidity tracker.
    ///
    /// # Errors
    ///
    /// - `Missing("alpha")` if none of `alpha`, `halflife`, `span` was set.
    /// - `Invalid` if the one set is out of range; the message names it.
    #[inline]
    pub fn build(self) -> Result<Amihud, crate::ConfigError> {
        Ok(Amihud {
            ema: self.ema.build()?,
        })
    }
}

#[cfg(test)]
// Expected values are written as plain arithmetic, independent of the fused
// forms the code under test uses.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::float_cmp)]
    fn is_the_weighted_average_of_absolute_return_over_volume() {
        // Ratios 2, 4, 8 (returns 2, -4, 8 on unit volume) at alpha 0.5:
        // 2, then 3, then 5.5.
        let mut a = Amihud::builder().alpha(0.5).build().unwrap();
        assert_eq!(a.update(2.0, 1.0), Some(2.0));
        assert_eq!(a.update(-4.0, 1.0), Some(3.0));
        assert_eq!(a.update(16.0, 2.0), Some(5.5));
        assert_eq!(a.illiq(), Some(5.5));
        assert_eq!(a.count(), 3);
    }

    #[test]
    fn the_sign_of_the_return_does_not_matter() {
        let feed = |sign: f64| {
            let mut a = Amihud::builder().alpha(0.1).build().unwrap();
            for i in 1..50 {
                let _ = a.update(sign * 0.001 * f64::from(i), 1e6);
            }
            a.illiq().unwrap()
        };
        let (up, down) = (feed(1.0), feed(-1.0));
        assert!(up > 0.0);
        assert_eq!(up.to_bits(), down.to_bits());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn zero_volume_periods_are_left_out() {
        let mut a = Amihud::builder().alpha(0.5).build().unwrap();
        // Before any trading there is nothing to report.
        assert_eq!(a.update(0.01, 0.0), None);
        assert_eq!(a.count(), 0);
        assert!(!a.is_primed());
        assert_eq!(a.update(2.0, 1.0), Some(2.0));
        // A later empty period leaves the reading and the count alone.
        assert_eq!(a.update(100.0, 0.0), Some(2.0));
        assert_eq!(a.count(), 1);
    }

    #[test]
    fn reset_clears_state() {
        let mut a = Amihud::builder().alpha(0.1).build().unwrap();
        let _ = a.update(0.01, 1_000_000.0);
        a.reset();
        assert_eq!(a.count(), 0);
        assert!(!a.is_primed());
        assert_eq!(a.illiq(), None);
    }

    #[test]
    fn rejects_bad_input_without_counting_it() {
        use crate::DataError::{Infinite, Negative, NotANumber, OutOfRange};
        let mut a = Amihud::builder().alpha(0.1).build().unwrap();
        assert_eq!(a.checked_update(f64::NAN, 1.0), Err(NotANumber));
        assert_eq!(a.checked_update(1.0, f64::NAN), Err(NotANumber));
        assert_eq!(a.checked_update(f64::INFINITY, 1.0), Err(Infinite));
        assert_eq!(a.checked_update(1.0, f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(a.checked_update(0.01, -5.0), Err(Negative));
        // A ratio too large to represent.
        assert_eq!(a.checked_update(1e300, 1e-300), Err(OutOfRange));
        assert_eq!(a.count(), 0);
    }

    #[test]
    fn builder_validation() {
        use crate::ConfigError::{Invalid, Missing};
        assert_eq!(Amihud::builder().build().unwrap_err(), Missing("alpha"));
        assert_eq!(
            Amihud::builder().span(1).build().unwrap_err(),
            Invalid("span must be at least 2")
        );
        assert!(Amihud::builder().span(20).build().is_ok());
    }
}
