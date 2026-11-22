/// Lower partial moments: downside risk, one sample at a time.
///
/// Measures deviations below a target threshold, raised to a
/// configurable integer order:
///
/// - Order 0: shortfall probability (fraction below target)
/// - Order 1: expected shortfall (mean distance below target)
/// - Order 2: semivariance (variance of downside deviations)
///
/// Fishburn (1977), Sortino & van der Meer (1991).
///
/// # Overflow
///
/// The shortfall is raised to the order and summed directly, as in R's
/// `PerformanceAnalytics::lpm` and Boost.Accumulators' `moment`, neither
/// of which rescales. A large shortfall at a high order can therefore
/// overflow an `f64`. For a stream of any length, keep shortfalls under
/// about `1e144` at order 2, `1e72` at order 4, and `1e18` at order 16.
///
/// [`checked_update`](Self::checked_update) refuses the sample that would
/// overflow the sum. It tests the result, which is where IEEE 754 defines
/// overflow and what `checked_add` does for integers.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::Lpm;
///
/// let mut lpm = Lpm::semivariance(0.0).unwrap();
/// for &v in &[-3.0, -1.0, 0.0, 2.0, 5.0] {
///     lpm.update(v);
/// }
/// let sv = lpm.lpm().unwrap();
/// assert!((sv - 2.0).abs() < 0.01);
/// ```
#[derive(Debug, Clone)]
pub struct Lpm {
    sum: f64,
    count: u64,
    target: f64,
    order: u32,
    min_samples: u64,
}

/// Builder for [`Lpm`].
#[derive(Debug, Clone)]
pub struct LpmBuilder {
    target: Option<f64>,
    order: Option<u32>,
    min_samples: u64,
}

impl Lpm {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> LpmBuilder {
        LpmBuilder {
            target: None,
            order: None,
            min_samples: 1,
        }
    }

    /// Convenience constructor for semivariance (order = 2).
    pub fn semivariance(target: f64) -> Result<Self, crate::ConfigError> {
        Self::builder().target(target).order(2).build()
    }

    /// Feeds a sample.
    ///
    /// Does not validate `sample`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::statistics::Lpm;
    ///
    /// let mut lpm = Lpm::semivariance(0.0).unwrap();
    /// lpm.update(-3.0);
    /// lpm.update(1.0);
    /// assert_eq!(lpm.lpm(), Some(4.5));
    /// ```
    #[inline]
    pub fn update(&mut self, sample: f64) {
        self.sum += self.term(sample);
        self.count += 1;
    }

    /// Checked update. Feeds `sample`, or returns an error and leaves the
    /// accumulator unchanged if `sample` is NaN or infinite, or if its shortfall
    /// raised to the order would overflow the running sum.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `sample`
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if `sample` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if the sum
    ///   would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::{DataError, statistics::Lpm};
    ///
    /// let mut lpm = Lpm::semivariance(0.0).unwrap();
    /// assert_eq!(lpm.checked_update(-3.0), Ok(()));
    /// assert_eq!(lpm.checked_update(-1e200), Err(DataError::OutOfRange));
    /// assert_eq!(lpm.lpm(), Some(9.0));
    /// ```
    #[inline]
    pub fn checked_update(&mut self, sample: f64) -> Result<(), crate::DataError> {
        // Any finite sample is allowed: it is the sum that can overflow.
        crate::math::check_input(sample, f64::MAX)?;
        if !(self.sum + self.term(sample)).is_finite() {
            return Err(crate::DataError::OutOfRange);
        }
        self.update(sample);
        Ok(())
    }

    /// Lower partial moment: average downside deviation^order.
    ///
    /// Returns `None` if not primed.
    #[must_use]
    pub fn lpm(&self) -> Option<f64> {
        if self.count < self.min_samples {
            return None;
        }

        Some(self.sum / self.count as f64)
    }

    /// The target threshold.
    #[must_use]
    pub fn target(&self) -> f64 {
        self.target
    }

    /// The moment order.
    #[must_use]
    pub fn order(&self) -> u32 {
        self.order
    }

    /// Total samples processed.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough samples have been observed.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets accumulated state. Target and order are preserved.
    pub fn reset(&mut self) {
        self.sum = 0.0;
        self.count = 0;
    }

    /// The sample's shortfall below the target, raised to the order.
    fn term(&self, sample: f64) -> f64 {
        // PERF: clamped, not branched: the side of the target is a coin flip.
        let shortfall = (self.target - sample).max(0.0);
        match self.order {
            0 => crate::math::indicator(shortfall > 0.0),
            1 => shortfall,
            2 => shortfall * shortfall,
            order => {
                let mut power = shortfall;
                for _ in 1..order {
                    power *= shortfall;
                }
                power
            }
        }
    }
}

impl LpmBuilder {
    /// Sets the target threshold (required).
    #[must_use]
    pub fn target(mut self, target: f64) -> Self {
        self.target = Some(target);
        self
    }

    /// Sets the moment order (required).
    #[must_use]
    pub fn order(mut self, order: u32) -> Self {
        self.order = Some(order);
        self
    }

    /// Sets the minimum samples before `lpm()` returns a value.
    #[must_use]
    pub fn min_samples(mut self, n: u64) -> Self {
        self.min_samples = n;
        self
    }

    /// Builds the LPM tracker.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if target is missing/non-finite or
    /// order is missing.
    pub fn build(self) -> Result<Lpm, crate::ConfigError> {
        let target = self.target.ok_or(crate::ConfigError::Missing("target"))?;
        if !target.is_finite() {
            return Err(crate::ConfigError::Invalid("target must be finite"));
        }
        let order = self.order.ok_or(crate::ConfigError::Missing("order"))?;
        if order > 16 {
            return Err(crate::ConfigError::Invalid(
                "order must be <= 16 (each update costs O(order) multiplies)",
            ));
        }
        if self.min_samples == 0 {
            return Err(crate::ConfigError::Invalid("min_samples must be >= 1"));
        }
        Ok(Lpm {
            sum: 0.0,
            count: 0,
            target,
            order,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semivariance_known_values() {
        // target=0, samples: -3, -1, 0, 2, 5
        // shortfalls: 3, 1, 0, 0, 0
        // squared shortfalls: 9, 1, 0, 0, 0
        // semivariance = 10 / 5 = 2.0
        let mut lpm = Lpm::semivariance(0.0).unwrap();
        for &v in &[-3.0, -1.0, 0.0, 2.0, 5.0] {
            lpm.update(v);
        }
        let sv = lpm.lpm().unwrap();
        assert!((sv - 2.0).abs() < 1e-10, "expected 2.0, got {sv}");
    }

    #[test]
    fn shortfall_probability() {
        let mut lpm = Lpm::builder().target(50.0).order(0).build().unwrap();
        for i in 0..100 {
            lpm.update(i as f64);
        }
        let prob = lpm.lpm().unwrap();
        assert!((prob - 0.5).abs() < 0.01, "expected ~0.5, got {prob}");
    }

    #[test]
    fn expected_shortfall() {
        let mut lpm = Lpm::builder().target(10.0).order(1).build().unwrap();
        for &v in &[5.0, 8.0, 12.0, 15.0] {
            lpm.update(v);
        }
        // shortfalls: 5, 2, 0, 0 → sum=7, mean=7/4=1.75
        let es = lpm.lpm().unwrap();
        assert!((es - 1.75).abs() < 1e-10, "expected 1.75, got {es}");
    }

    #[test]
    fn all_above_target() {
        let mut lpm = Lpm::semivariance(0.0).unwrap();
        for &v in &[1.0, 2.0, 3.0] {
            lpm.update(v);
        }
        let sv = lpm.lpm().unwrap();
        assert!((sv - 0.0).abs() < 1e-10, "expected 0.0, got {sv}");
    }

    #[test]
    fn all_below_target() {
        let mut lpm = Lpm::builder().target(100.0).order(2).build().unwrap();
        for &v in &[90.0, 80.0, 70.0] {
            lpm.update(v);
        }
        // shortfalls: 10, 20, 30; squared: 100, 400, 900; mean = 1400/3
        let sv = lpm.lpm().unwrap();
        assert!(
            (sv - 1400.0 / 3.0).abs() < 1e-10,
            "expected {}, got {sv}",
            1400.0 / 3.0
        );
    }

    #[test]
    fn semivariance_convenience() {
        let mut sv = Lpm::semivariance(0.0).unwrap();
        let mut manual = Lpm::builder().target(0.0).order(2).build().unwrap();
        for &v in &[-2.0, -1.0, 0.0, 1.0, 2.0] {
            sv.update(v);
            manual.update(v);
        }
        assert!((sv.lpm().unwrap() - manual.lpm().unwrap()).abs() < 1e-10);
        assert_eq!(sv.order(), 2);
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let mut lpm = Lpm::builder().target(0.0).order(16).build().unwrap();
        lpm.checked_update(-2.0).unwrap();
        let before = (lpm.count(), lpm.lpm());

        assert_eq!(lpm.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(lpm.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(lpm.checked_update(f64::NEG_INFINITY), Err(Infinite));
        // 1e20 to the 16th power is past the largest f64.
        assert_eq!(lpm.checked_update(-1e20), Err(OutOfRange));

        assert_eq!((lpm.count(), lpm.lpm()), before);
        assert_eq!(before, (1, Some(65_536.0)));
    }

    #[test]
    fn checked_update_refuses_the_sample_that_would_overflow_the_sum() {
        // Two squares of 1e154 are each finite; their sum is not.
        let mut lpm = Lpm::semivariance(0.0).unwrap();
        assert_eq!(lpm.checked_update(-1e154), Ok(()));
        assert_eq!(
            lpm.checked_update(-1e154),
            Err(crate::DataError::OutOfRange)
        );
        assert_eq!(lpm.count(), 1);
        assert!(lpm.lpm().unwrap().is_finite());
    }

    #[test]
    fn a_shortfall_that_overflows_is_refused_except_as_a_count() {
        // `1e308 - (-1e308)` is infinite, though both values are finite.
        let fed = |order: u32| {
            let mut lpm = Lpm::builder().target(1e308).order(order).build().unwrap();
            (lpm.checked_update(-1e308), lpm.count())
        };
        assert_eq!(fed(1), (Err(crate::DataError::OutOfRange), 0));
        // Order 0 only counts shortfalls, so the size does not matter.
        assert_eq!(fed(0), (Ok(()), 1));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        for order in [0, 1, 2, 5] {
            let mut checked = Lpm::builder().target(1.0).order(order).build().unwrap();
            let mut unchecked = checked.clone();
            for x in [2.0, -7.5, 0.5, 1.0, -3.25] {
                checked.checked_update(x).unwrap();
                unchecked.update(x);
            }
            assert_eq!(checked.count(), unchecked.count());
            assert_eq!(checked.lpm(), unchecked.lpm(), "order {order}");
        }
    }

    #[test]
    fn update_does_not_validate() {
        let mut lpm = Lpm::builder().target(0.0).order(16).build().unwrap();
        lpm.update(-1e20);
        assert_eq!(lpm.lpm(), Some(f64::INFINITY));
    }

    #[test]
    fn higher_orders_raise_the_shortfall_to_the_order() {
        // Shortfalls 2 and 0 at order 5: (32 + 0) / 2.
        let mut lpm = Lpm::builder().target(0.0).order(5).build().unwrap();
        lpm.update(-2.0);
        lpm.update(3.0);
        assert_eq!(lpm.lpm(), Some(16.0));
    }

    #[test]
    fn reset_clears() {
        let mut lpm = Lpm::semivariance(5.0).unwrap();
        lpm.update(2.0);
        lpm.update(3.0);
        assert_eq!(lpm.count(), 2);
        lpm.reset();
        assert_eq!(lpm.count(), 0);
        assert!(lpm.lpm().is_none());
        assert_eq!(lpm.target(), 5.0);
        assert_eq!(lpm.order(), 2);
    }
}
