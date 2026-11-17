use nexus_stats_core::math::MulAdd;

/// Critically damped spring — chase a target without overshoot.
///
/// Uses a Pade approximant for stable behavior with variable dt.
/// The output smoothly approaches the target with no ringing.
///
/// # Use Cases
/// - Camera smoothing in games
/// - Smooth parameter transitions
/// - Any "chase this value" without PID complexity
#[derive(Debug, Clone)]
pub struct Spring {
    smooth_time: f64,
    omega: f64,
    value: f64,
    velocity: f64,
    /// Samples processed; the first one seeds the position.
    count: u64,
}

impl Spring {
    /// Creates a new spring with the given smooth time.
    ///
    /// `smooth_time` controls how quickly the spring converges.
    /// Larger = slower, smoother. Smaller = faster, more reactive.
    #[inline]
    pub fn new(smooth_time: f64) -> Result<Self, nexus_stats_core::ConfigError> {
        #[allow(clippy::neg_cmp_op_on_partial_ord)]
        if !(smooth_time > 0.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "smooth_time must be positive",
            ));
        }
        Ok(Self {
            smooth_time,
            omega: 2.0 / smooth_time,
            value: 0.0,
            velocity: 0.0,
            count: 0,
        })
    }

    /// Updates toward the target. Returns the new value.
    ///
    /// `dt` is the time since the last update, in the same units as `smooth_time`.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if target or dt is NaN, or
    /// `DataError::Infinite` if either is infinite.
    #[inline]
    pub fn update(&mut self, target: f64, dt: f64) -> Result<f64, nexus_stats_core::DataError> {
        check_finite!(target);
        check_finite!(dt);
        self.count += 1;
        if self.count == 1 {
            self.value = target;
            return Ok(target);
        }

        // Critically damped spring using Pade approximant
        let x = self.omega * dt;
        // Pade(2,2) approximant to exp(-x): (1 - x/2 + x^2/12) / (1 + x/2 + x^2/12)
        // Simplified: use exact exp(-x) via (1 + x + x^2/2)^-1 approximation
        let exp_neg = 1.0 / x.fma(x.fma(0.5, 1.0), 1.0);

        let delta = self.value - target;
        let temp = self.omega.fma(delta, self.velocity) * dt;
        self.velocity = self.omega.fma(-temp, self.velocity) * exp_neg;
        self.value = (delta + temp).fma(exp_neg, target);

        Ok(self.value)
    }

    /// The configured smooth time.
    #[inline]
    #[must_use]
    pub fn smooth_time(&self) -> f64 {
        self.smooth_time
    }

    /// Current output value.
    #[inline]
    #[must_use]
    pub fn value(&self) -> f64 {
        self.value
    }

    /// Current velocity.
    #[inline]
    #[must_use]
    pub fn velocity(&self) -> f64 {
        self.velocity
    }

    /// Samples processed since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one sample has been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.value = 0.0;
        self.velocity = 0.0;
        self.count = 0;
    }

    /// Resets to a specific value with zero velocity.
    #[inline]
    pub fn reset_to(&mut self, value: f64) {
        self.value = value;
        self.velocity = 0.0;
        self.count = 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn converges_to_target() {
        let mut s = Spring::new(0.5).unwrap();
        let target = 100.0;

        for _ in 0..200 {
            s.update(target, 0.016).unwrap(); // ~60fps
        }

        assert!(
            (s.value() - target).abs() < 0.01,
            "should converge to {target}, got {}",
            s.value()
        );
    }

    #[test]
    fn no_overshoot() {
        let mut s = Spring::new(0.5).unwrap();
        let target = 100.0;
        s.update(0.0, 0.016).unwrap(); // initialize at 0

        let mut max_value = 0.0f64;
        for _ in 0..1000 {
            let v = s.update(target, 0.016).unwrap();
            if v > max_value {
                max_value = v;
            }
        }

        assert!(
            max_value <= target + 0.1,
            "should not overshoot, max was {max_value}"
        );
    }

    #[test]
    fn variable_dt_stable() {
        let mut s = Spring::new(1.0).unwrap();
        let target = 50.0;

        // Large dt steps shouldn't explode
        s.update(target, 0.5).unwrap();
        assert!(s.value().is_finite());
        s.update(target, 2.0).unwrap();
        assert!(s.value().is_finite());
        s.update(target, 10.0).unwrap();
        assert!(s.value().is_finite());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn reset_to() {
        let mut s = Spring::new(0.5).unwrap();
        s.update(100.0, 0.016).unwrap();

        s.reset_to(50.0);
        assert_eq!(s.value(), 50.0);
        assert_eq!(s.velocity(), 0.0);
    }

    #[test]
    fn rejects_zero_smooth_time() {
        assert!(matches!(
            Spring::new(0.0),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut s = Spring::new(0.5).unwrap();
        // NaN target
        assert!(matches!(
            s.update(f64::NAN, 0.016),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        // Infinite target
        assert!(matches!(
            s.update(f64::INFINITY, 0.016),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        // NaN dt
        assert!(matches!(
            s.update(100.0, f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        // Infinite dt
        assert!(matches!(
            s.update(100.0, f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
    }
}
