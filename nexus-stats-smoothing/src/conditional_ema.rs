use nexus_stats_core::smoothing::Ema;

/// EMA that only updates when a condition holds.
///
/// Wraps an `Ema` and only feeds values when `active` is true.
/// Tracks both total observations and active observations for
/// computing the active fraction (what percentage of ticks the
/// condition was met).
///
/// The user decides the condition externally:
/// `ema.update(markout, vpin > 0.5)` — only smooth markout when
/// VPIN indicates informed flow.
///
/// # Examples
///
/// ```
/// use nexus_stats_smoothing::ConditionalEma;
///
/// let mut ema = ConditionalEma::builder()
///     .alpha(0.1)
///     .build()
///     .unwrap();
///
/// ema.update(10.0, true).unwrap();   // active: EMA updates
/// ema.update(20.0, false).unwrap();  // inactive: EMA holds
/// ema.update(15.0, true).unwrap();   // active: EMA updates
///
/// assert!((ema.active_fraction() - 2.0 / 3.0).abs() < 0.01);
/// ```
#[derive(Debug, Clone)]
pub struct ConditionalEma {
    ema: Ema,
    count: u64,
    active_count: u64,
}

/// Builder for [`ConditionalEma`].
#[derive(Debug, Clone)]
pub struct ConditionalEmaBuilder {
    alpha: Option<f64>,
    min_samples: u64,
}

impl ConditionalEma {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> ConditionalEmaBuilder {
        ConditionalEmaBuilder {
            alpha: None,
            min_samples: 1,
        }
    }

    /// Feed a value. Only updates the EMA when `active` is true.
    ///
    /// The total count always increments. The active count and EMA
    /// only update when `active` is true.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if the value is NaN or infinite.
    #[inline]
    pub fn update(&mut self, value: f64, active: bool) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(value);

        self.count += 1;
        if active {
            self.active_count += 1;
            self.ema.update(value);
        }

        Ok(())
    }

    /// Current smoothed value, or `None` if no active observations.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<f64> {
        self.ema.value()
    }

    /// Reads `0.0` before any sample: nothing has been active yet.
    /// Fraction of observations where the condition was active.
    #[inline]
    #[must_use]
    pub fn active_fraction(&self) -> f64 {
        if self.count == 0 {
            return 0.0;
        }
        self.active_count as f64 / self.count as f64
    }

    /// Total number of observations (active + inactive).
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Number of active observations.
    #[inline]
    #[must_use]
    pub fn active_count(&self) -> u64 {
        self.active_count
    }

    /// Whether the underlying EMA is primed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.ema.is_primed()
    }

    /// Reset all state.
    pub fn reset(&mut self) {
        self.ema.reset();
        self.count = 0;
        self.active_count = 0;
    }
}

impl ConditionalEmaBuilder {
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
        self.alpha = Some(nexus_stats_core::math::alpha_from_halflife(halflife));
        self
    }

    /// Minimum active samples before value is valid. Default: 1.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Build the conditional EMA.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if alpha is missing or invalid.
    #[inline]
    pub fn build(self) -> Result<ConditionalEma, nexus_stats_core::ConfigError> {
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;

        let ema = Ema::builder()
            .alpha(alpha)
            .min_samples(self.min_samples)
            .build()?;

        Ok(ConditionalEma {
            ema,
            count: 0,
            active_count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_active_updates_ema() {
        let mut ema = ConditionalEma::builder().alpha(0.5).build().unwrap();

        ema.update(100.0, true).unwrap();
        let v1 = ema.value().unwrap();
        assert!((v1 - 100.0).abs() < f64::EPSILON);

        // Inactive: value should not change
        ema.update(200.0, false).unwrap();
        let v2 = ema.value().unwrap();
        assert!((v2 - 100.0).abs() < f64::EPSILON);

        // Active: value should update
        ema.update(200.0, true).unwrap();
        let v3 = ema.value().unwrap();
        assert!(v3 > 100.0 && v3 < 200.0);
    }

    #[test]
    fn active_fraction_correct() {
        let mut ema = ConditionalEma::builder().alpha(0.5).build().unwrap();

        ema.update(1.0, true).unwrap();
        ema.update(2.0, false).unwrap();
        ema.update(3.0, true).unwrap();
        ema.update(4.0, false).unwrap();

        assert!((ema.active_fraction() - 0.5).abs() < f64::EPSILON);
        assert_eq!(ema.count(), 4);
        assert_eq!(ema.active_count(), 2);
    }

    #[test]
    fn no_active_not_primed() {
        let mut ema = ConditionalEma::builder().alpha(0.5).build().unwrap();
        ema.update(1.0, false).unwrap();
        ema.update(2.0, false).unwrap();
        assert!(!ema.is_primed());
        assert!(ema.value().is_none());
    }

    #[test]
    fn priming_on_active() {
        let mut ema = ConditionalEma::builder()
            .alpha(0.5)
            .min_samples(3)
            .build()
            .unwrap();

        ema.update(1.0, true).unwrap();
        ema.update(2.0, true).unwrap();
        assert!(!ema.is_primed());

        ema.update(3.0, true).unwrap();
        assert!(ema.is_primed());
    }

    #[test]
    fn reset_clears_state() {
        let mut ema = ConditionalEma::builder().alpha(0.5).build().unwrap();
        ema.update(100.0, true).unwrap();
        ema.reset();
        assert_eq!(ema.count(), 0);
        assert_eq!(ema.active_count(), 0);
        assert!(!ema.is_primed());
    }

    #[test]
    fn nan_rejected() {
        let mut ema = ConditionalEma::builder().alpha(0.5).build().unwrap();
        assert!(ema.update(f64::NAN, true).is_err());
    }

    #[test]
    fn inf_rejected() {
        let mut ema = ConditionalEma::builder().alpha(0.5).build().unwrap();
        assert!(ema.update(f64::INFINITY, true).is_err());
    }

    #[test]
    fn empty_active_fraction() {
        let ema = ConditionalEma::builder().alpha(0.5).build().unwrap();
        assert!(ema.active_fraction().abs() < f64::EPSILON);
    }
}
