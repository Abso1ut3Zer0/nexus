/// Hawkes process intensity estimator.
///
/// Self-exciting point process: each event increases the intensity,
/// which then decays exponentially. Models bursty arrivals where
/// events cluster (trade arrivals, order bursts, alert cascades).
///
/// lambda(t) = mu + alpha * sum exp(-beta * (t - t_i))
///
/// Recursive form: O(1) per event.
///
/// # Parameters
///
/// - `mu` (mu) — baseline intensity (events per unit time)
/// - `alpha` (alpha) — excitation per event
/// - `beta` (beta) — decay rate (higher = faster decay)
///
/// Stability requires alpha < beta (branching ratio alpha/beta < 1).
///
/// # Examples
///
/// ```
/// use nexus_stats_core::monitoring::HawkesIntensity;
///
/// let mut h = HawkesIntensity::builder()
///     .mu(1.0)
///     .alpha(0.5)
///     .beta(1.0)
///     .build()
///     .unwrap();
///
/// h.update(0);
/// h.update(100);
/// assert!(h.intensity() > 1.0); // above baseline after event
/// ```
///
/// # Weighting clock
///
/// Caller's timestamps: the intensity decays by the elapsed ticks between
/// calls, so any call rate is correct.
#[derive(Debug, Clone)]
pub struct HawkesIntensity {
    mu: f64,
    alpha: f64,
    beta: f64,
    excitation: f64,
    last_time: u64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`HawkesIntensity`].
#[derive(Debug, Clone)]
pub struct HawkesIntensityBuilder {
    mu: Option<f64>,
    alpha: Option<f64>,
    beta: Option<f64>,
    min_samples: u64,
}

impl HawkesIntensity {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> HawkesIntensityBuilder {
        HawkesIntensityBuilder {
            mu: None,
            alpha: None,
            beta: None,
            min_samples: 2,
        }
    }

    /// Records an event at the given timestamp.
    ///
    /// Timestamps are u64 (matching `Clock::stamp()`). The delta
    /// between timestamps is computed with saturating subtraction.
    #[inline]
    pub fn update(&mut self, time: u64) {
        self.count += 1;

        if self.count == 1 {
            self.excitation = self.alpha;
            self.last_time = time;
            return;
        }

        let dt = time.saturating_sub(self.last_time);
        let decay = crate::math::exp(-(self.beta * dt as f64));
        self.excitation = crate::math::MulAdd::fma(decay, self.excitation, self.alpha);
        self.last_time = time;
    }

    /// Current intensity lambda at last event time: `mu + excitation`.
    #[inline]
    #[must_use]
    pub fn intensity(&self) -> f64 {
        if self.count == 0 {
            self.mu
        } else {
            self.mu + self.excitation
        }
    }

    /// Intensity at an arbitrary time (without recording an event).
    ///
    /// Decays excitation from last event time to `time`. Assumes
    /// monotonic timestamps; times before `last_time` are clamped
    /// to zero delta, returning the current intensity.
    #[inline]
    #[must_use]
    pub fn intensity_at(&self, time: u64) -> f64 {
        if self.count == 0 {
            return self.mu;
        }
        let dt = time.saturating_sub(self.last_time);
        let decay = crate::math::exp(-(self.beta * dt as f64));
        crate::math::MulAdd::fma(decay, self.excitation, self.mu)
    }

    /// Baseline intensity mu.
    #[inline]
    #[must_use]
    pub fn baseline(&self) -> f64 {
        self.mu
    }

    /// Branching ratio alpha/beta. Must be < 1 for stability.
    #[inline]
    #[must_use]
    pub fn branching_ratio(&self) -> f64 {
        self.alpha / self.beta
    }

    /// Number of events recorded.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough events have been observed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to empty state. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.excitation = 0.0;
        self.last_time = 0;
        self.count = 0;
    }
}

impl HawkesIntensityBuilder {
    /// Baseline intensity mu (required, > 0).
    #[inline]
    #[must_use]
    pub fn mu(mut self, mu: f64) -> Self {
        self.mu = Some(mu);
        self
    }

    /// Excitation per event alpha (required, >= 0).
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Decay rate beta (required, > 0, must be > alpha for stability).
    #[inline]
    #[must_use]
    pub fn beta(mut self, beta: f64) -> Self {
        self.beta = Some(beta);
        self
    }

    /// Minimum events before is_primed. Default: 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the Hawkes intensity estimator.
    ///
    /// # Errors
    ///
    /// - `mu` must be positive and finite.
    /// - `alpha` must be non-negative and finite.
    /// - `beta` must be positive and finite.
    /// - `alpha` must be < `beta` (branching ratio < 1).
    #[inline]
    pub fn build(self) -> Result<HawkesIntensity, crate::ConfigError> {
        let mu = self.mu.ok_or(crate::ConfigError::Missing("mu"))?;
        if mu <= 0.0 || !mu.is_finite() {
            return Err(crate::ConfigError::Invalid(
                "Hawkes mu must be positive and finite",
            ));
        }

        let alpha = self.alpha.ok_or(crate::ConfigError::Missing("alpha"))?;
        if !crate::math::nonnegative_finite(alpha) {
            return Err(crate::ConfigError::Invalid(
                "Hawkes alpha must be non-negative and finite",
            ));
        }

        let beta = self.beta.ok_or(crate::ConfigError::Missing("beta"))?;
        if beta <= 0.0 || !beta.is_finite() {
            return Err(crate::ConfigError::Invalid(
                "Hawkes beta must be positive and finite",
            ));
        }

        if alpha >= beta {
            return Err(crate::ConfigError::Invalid(
                "Hawkes alpha must be < beta (branching ratio < 1)",
            ));
        }

        Ok(HawkesIntensity {
            mu,
            alpha,
            beta,
            excitation: 0.0,
            last_time: 0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn baseline_without_events() {
        let h = HawkesIntensity::builder()
            .mu(5.0)
            .alpha(0.5)
            .beta(1.0)
            .build()
            .unwrap();

        assert!((h.intensity() - 5.0).abs() < 1e-10);
        assert!((h.intensity_at(1_000_000) - 5.0).abs() < 1e-10);
    }

    #[test]
    fn excitation_spike() {
        let mut h = HawkesIntensity::builder()
            .mu(1.0)
            .alpha(0.5)
            .beta(1.0)
            .build()
            .unwrap();

        h.update(0);
        let after_event = h.intensity();
        assert!(
            after_event > 1.0,
            "intensity should spike above baseline after event, got {after_event}"
        );
    }

    #[test]
    fn decay_over_time() {
        let mut h = HawkesIntensity::builder()
            .mu(1.0)
            .alpha(0.5)
            .beta(1.0)
            .build()
            .unwrap();

        h.update(0);
        let far_future = h.intensity_at(1_000_000);
        assert!(
            (far_future - 1.0).abs() < 0.01,
            "intensity should decay to baseline, got {far_future}"
        );
    }

    #[test]
    fn burst_intensifies() {
        let mut h = HawkesIntensity::builder()
            .mu(1.0)
            .alpha(0.5)
            .beta(1.0)
            .build()
            .unwrap();

        h.update(0);
        let after_one = h.intensity();

        h.update(1);
        let after_two = h.intensity();

        h.update(2);
        let after_three = h.intensity();

        assert!(
            after_three > after_two && after_two > after_one,
            "rapid events should increase intensity: {after_one} < {after_two} < {after_three}"
        );
    }

    #[test]
    fn branching_ratio_value() {
        let h = HawkesIntensity::builder()
            .mu(1.0)
            .alpha(0.3)
            .beta(1.0)
            .build()
            .unwrap();

        assert!((h.branching_ratio() - 0.3).abs() < 1e-10);
    }

    #[test]
    fn stability_validation() {
        let result = HawkesIntensity::builder()
            .mu(1.0)
            .alpha(1.0)
            .beta(1.0)
            .build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));

        let result = HawkesIntensity::builder()
            .mu(1.0)
            .alpha(2.0)
            .beta(1.0)
            .build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    #[test]
    fn reset_clears() {
        let mut h = HawkesIntensity::builder()
            .mu(1.0)
            .alpha(0.5)
            .beta(1.0)
            .build()
            .unwrap();

        h.update(0);
        h.update(10);
        h.reset();
        assert_eq!(h.count(), 0);
        assert!((h.intensity() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn same_timestamp_events() {
        let mut h = HawkesIntensity::builder()
            .mu(1.0)
            .alpha(0.5)
            .beta(1.0)
            .build()
            .unwrap();

        h.update(100);
        let after_one = h.intensity();

        h.update(100);
        let after_two = h.intensity();

        assert!(
            after_two > after_one,
            "same-time events should stack: {after_one} < {after_two}"
        );
    }
}
