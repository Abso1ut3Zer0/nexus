/// Lower Partial Moments — streaming downside risk.
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
    #[inline]
    #[must_use]
    pub fn builder() -> LpmBuilder {
        LpmBuilder {
            target: None,
            order: None,
            min_samples: 1,
        }
    }

    /// Convenience constructor for semivariance (order = 2).
    #[inline]
    pub fn semivariance(target: f64) -> Result<Self, crate::ConfigError> {
        Self::builder().target(target).order(2).build()
    }

    /// Feeds a sample.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in. A
    /// NaN makes the moment NaN from then on, until [`reset`](Self::reset);
    /// a large enough shortfall at a high order overflows it to infinity.
    /// (`+inf` is no shortfall and `-inf` an infinite one, as the definition
    /// has it.)
    /// Use [`checked_update`](Self::checked_update) to have such a sample
    /// refused instead.
    #[inline]
    pub fn update(&mut self, sample: f64) {
        self.commit(self.sum + self.term(sample));
    }

    /// [`update`](Self::update) with the sample validated first: refuses a
    /// NaN or an infinity, and a sample whose shortfall raised to the order
    /// would take the running sum to infinity. Orders run up to 16, too
    /// high for a single input limit to rule that out, so the result itself
    /// is checked. Fed only through this method the moment is always a
    /// finite number.
    ///
    /// # Errors
    ///
    /// `DataError::NotANumber`, `DataError::Infinite`, or
    /// `DataError::OutOfRange` if the sum would overflow. A refused sample
    /// changes nothing.
    #[inline]
    pub fn checked_update(&mut self, sample: f64) -> Result<(), crate::DataError> {
        check_finite!(sample);
        let sum = self.sum + self.term(sample);
        if !sum.is_finite() {
            return Err(crate::DataError::OutOfRange);
        }
        self.commit(sum);
        Ok(())
    }

    /// Records one more sample with the running sum it produced: shared by
    /// [`update`](Self::update), which takes whatever the sum came to, and
    /// [`checked_update`](Self::checked_update), which has first made sure
    /// it is finite. (`checked_update` cannot simply call `update`: it has
    /// to see the new sum before committing it.)
    #[inline]
    fn commit(&mut self, sum: f64) {
        self.sum = sum;
        self.count += 1;
    }

    /// The shortfall below the target, raised to the order.
    #[inline]
    fn term(&self, sample: f64) -> f64 {
        // Clamp instead of branching: for a return stream around the target,
        // `shortfall > 0` is a coin flip for the branch predictor. A zero
        // shortfall adds zero for every order.
        let shortfall = crate::math::floor_at_zero(self.target - sample);
        match self.order {
            0 => crate::math::indicator(shortfall > 0.0),
            1 => shortfall,
            2 => shortfall * shortfall,
            d => {
                let mut power = shortfall;
                for _ in 1..d {
                    power *= shortfall;
                }
                power
            }
        }
    }

    /// Lower partial moment: average downside deviation^order.
    ///
    /// Returns `None` if not primed.
    #[inline]
    #[must_use]
    pub fn lpm(&self) -> Option<f64> {
        if self.count < self.min_samples {
            None
        } else {
            Some(self.sum / self.count as f64)
        }
    }

    /// The target threshold.
    #[inline]
    #[must_use]
    pub fn target(&self) -> f64 {
        self.target
    }

    /// The moment order.
    #[inline]
    #[must_use]
    pub fn order(&self) -> u32 {
        self.order
    }

    /// Total samples processed.
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

    /// Resets accumulated state. Target and order are preserved.
    #[inline]
    pub fn reset(&mut self) {
        self.sum = 0.0;
        self.count = 0;
    }
}

impl LpmBuilder {
    /// Sets the target threshold (required).
    #[inline]
    #[must_use]
    pub fn target(mut self, target: f64) -> Self {
        self.target = Some(target);
        self
    }

    /// Sets the moment order (required).
    #[inline]
    #[must_use]
    pub fn order(mut self, order: u32) -> Self {
        self.order = Some(order);
        self
    }

    /// Sets the minimum samples before `lpm()` returns a value.
    #[inline]
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
    #[inline]
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
    fn rejects_nan_inf() {
        let mut lpm = Lpm::semivariance(0.0).unwrap();
        assert!(lpm.checked_update(f64::NAN).is_err());
        assert!(lpm.checked_update(f64::INFINITY).is_err());
        assert!(lpm.checked_update(f64::NEG_INFINITY).is_err());
        assert_eq!(lpm.count(), 0);
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
