use nexus_stats_monitoring::{Fall, PeakToTrough};

/// Drawdown: how far equity is below its peak, as an amount and as a
/// fraction of the peak, with the worst of each.
///
/// Feed it equity, net asset value or cumulative P&L. The first sample is
/// the first peak. The fraction is `(peak - equity) / peak`, a positive
/// number: `0.2` is 20% below the peak. It is a fraction of the peak, so it
/// is meaningful for a positive peak; for a peak at or below zero it is
/// whatever the division gives.
///
/// The amount alone, for any number type, is `PeakToTrough` in
/// `nexus-stats-monitoring`. See
/// [Drawdown](https://en.wikipedia.org/wiki/Drawdown_(economics)).
///
/// # Examples
///
/// ```
/// use nexus_stats_trading::Drawdown;
///
/// let mut dd = Drawdown::new();
/// for equity in [100.0, 125.0, 100.0, 110.0] {
///     dd.update(equity);
/// }
/// let reading = dd.reading().unwrap();
/// assert_eq!((reading.peak, reading.drawdown, reading.fraction), (125.0, 15.0, 0.12));
/// assert_eq!((reading.max_drawdown, reading.max_fraction), (25.0, 0.2));
/// ```
#[derive(Debug, Clone)]
pub struct Drawdown {
    falls: PeakToTrough<f64>,
    max_fraction: f64,
}

/// A [`Drawdown`] reading.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DrawdownReading {
    /// The highest equity so far.
    pub peak: f64,
    /// The amount equity is below the peak. Zero at a new peak.
    pub drawdown: f64,
    /// The drawdown as a fraction of the peak.
    pub fraction: f64,
    /// The largest drawdown so far, as an amount.
    pub max_drawdown: f64,
    /// The largest drawdown so far, as a fraction of the peak it fell from.
    pub max_fraction: f64,
}

impl Drawdown {
    /// Creates an empty tracker.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            falls: PeakToTrough::new(),
            max_fraction: 0.0,
        }
    }

    /// Feeds an equity value and returns the reading.
    ///
    /// Does not validate; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, equity: f64) -> DrawdownReading {
        let fall = self.falls.update(equity);
        let fraction = fraction_of_peak(fall);
        // PERF: a select. A NaN fraction (a peak of zero) is not kept.
        self.max_fraction = if fraction > self.max_fraction {
            fraction
        } else {
            self.max_fraction
        };
        self.reading_from(fall)
    }

    /// Checked update. Feeds `equity`, or returns an error and leaves the
    /// tracker unchanged if `equity` is NaN or infinite.
    ///
    /// An infinite peak never comes down, so every later drawdown would be
    /// infinite until [`reset`](Self::reset).
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `equity` is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if
    ///   `equity` is infinite.
    #[inline]
    pub fn checked_update(
        &mut self,
        equity: f64,
    ) -> Result<DrawdownReading, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_input(equity, f64::MAX)?;
        Ok(self.update(equity))
    }

    /// The peak, the drawdown from it and the worst drawdown, or `None`
    /// before the first sample.
    #[must_use]
    pub fn reading(&self) -> Option<DrawdownReading> {
        Some(self.reading_from(self.falls.reading()?))
    }

    /// Samples fed since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.falls.count()
    }

    /// Whether at least one sample has been fed.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.falls.is_primed()
    }

    /// Forgets the peak and both drawdowns.
    pub fn reset(&mut self) {
        *self = Self::new();
    }

    /// The reading in equity terms for a fall from the peak.
    #[inline]
    fn reading_from(&self, fall: Fall<f64>) -> DrawdownReading {
        DrawdownReading {
            peak: fall.high,
            drawdown: fall.current,
            fraction: fraction_of_peak(fall),
            max_drawdown: fall.largest,
            max_fraction: self.max_fraction,
        }
    }
}

/// The current fall as a fraction of the peak it fell from.
#[inline]
fn fraction_of_peak(fall: Fall<f64>) -> f64 {
    fall.current / fall.high
}

impl Default for Drawdown {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nexus_stats_core::DataError::{Infinite, NotANumber};

    #[test]
    fn nothing_is_read_before_the_first_sample() {
        let dd = Drawdown::new();
        assert_eq!((dd.reading(), dd.count(), dd.is_primed()), (None, 0, false));
    }

    #[test]
    fn the_amount_and_the_fraction_are_measured_from_the_peak() {
        let mut dd = Drawdown::new();
        let first = dd.update(100.0);
        assert_eq!(
            (first.peak, first.drawdown, first.fraction),
            (100.0, 0.0, 0.0)
        );
        dd.update(125.0);
        let r = dd.update(100.0);
        assert_eq!((r.peak, r.drawdown, r.fraction), (125.0, 25.0, 0.2));
        let r = dd.update(110.0);
        assert_eq!((r.drawdown, r.fraction), (15.0, 0.12));
        assert_eq!((r.max_drawdown, r.max_fraction), (25.0, 0.2));
        assert_eq!(dd.reading(), Some(r));
    }

    /// The worst fraction is not the fraction of the worst amount: a small
    /// fall from a low peak can be the larger share.
    #[test]
    fn the_worst_fraction_and_the_worst_amount_can_come_from_different_falls() {
        let mut dd = Drawdown::new();
        for equity in [10.0, 5.0, 1000.0, 900.0] {
            dd.update(equity);
        }
        let r = dd.reading().unwrap();
        assert_eq!((r.max_drawdown, r.max_fraction), (100.0, 0.5));
    }

    /// Against the definition, on a random walk kept above zero.
    #[test]
    fn matches_the_definition_on_a_random_walk() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut dd = Drawdown::new();
        let (mut equity, mut peak) = (10_000.0f64, f64::MIN);
        let (mut worst, mut worst_fraction) = (0.0f64, 0.0f64);
        for _ in 0..50_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            equity += (state % 201) as f64 - 100.0;
            equity = equity.max(1.0);
            peak = peak.max(equity);
            worst = worst.max(peak - equity);
            worst_fraction = worst_fraction.max((peak - equity) / peak);
            let r = dd.update(equity);
            assert_eq!((r.peak, r.drawdown), (peak, peak - equity));
            assert_eq!((r.max_drawdown, r.max_fraction), (worst, worst_fraction));
        }
    }

    #[test]
    fn reset_forgets_everything() {
        let mut dd = Drawdown::new();
        dd.update(100.0);
        dd.update(50.0);
        dd.reset();
        assert_eq!((dd.reading(), dd.count()), (None, 0));
        let r = dd.update(10.0);
        assert_eq!((r.peak, r.max_drawdown, r.max_fraction), (10.0, 0.0, 0.0));
    }

    #[test]
    fn checked_update_refuses_nan_and_infinity_and_changes_nothing() {
        let mut dd = Drawdown::new();
        assert_eq!(dd.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!((dd.reading(), dd.count()), (None, 0));
        dd.checked_update(100.0).unwrap();
        dd.checked_update(80.0).unwrap();
        let before = (dd.reading(), dd.count());
        assert_eq!(dd.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(dd.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(dd.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!((dd.reading(), dd.count()), before);
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let (mut checked, mut plain) = (Drawdown::new(), Drawdown::new());
        for equity in [100.0, 90.0, 1e300, 5.0, 0.0, -3.0, 2.5] {
            assert_eq!(checked.checked_update(equity), Ok(plain.update(equity)));
        }
    }

    /// A peak of zero has no fraction. The division says so, and it is not
    /// kept as the worst.
    #[test]
    fn a_peak_of_zero_gives_an_undefined_fraction() {
        let mut dd = Drawdown::new();
        assert!(dd.update(0.0).fraction.is_nan());
        let r = dd.update(-5.0);
        assert_eq!(r.drawdown, 5.0);
        assert_eq!(r.fraction, f64::INFINITY);
        let mut dd = Drawdown::new();
        dd.update(0.0);
        assert_eq!(dd.reading().unwrap().max_fraction, 0.0);
    }
}
