use nexus_stats_core::math::{MulAdd, Warmup};

/// Critically damped spring: chases a target and settles without ringing.
///
/// Each update moves the value toward the target as a spring with exactly
/// enough damping not to oscillate. It keeps a velocity, so it eases in
/// and out where an average would jump off the mark, and it takes the time
/// since the last update, so it works at an uneven rate.
///
/// `smooth_time` is roughly the time to reach the target: larger is slower
/// and smoother. `dt` is in the same unit.
///
/// The method is from *Game Programming Gems 4*, chapter 1.10, in the form
/// used by Unity's `Mathf.SmoothDamp`: a rational approximation of the
/// decay, with the output held at the target if a step would cross it.
/// The crossing test is the one Unity's vector form uses: a spring that
/// is on the target with some velocity carries through it, either way.
///
/// One rule is added to the published form: a step long enough for the
/// decay to reach zero puts the spring at rest on the target, where the
/// formula alone would multiply an overflow by that zero.
///
/// # Examples
///
/// ```
/// use nexus_stats_smoothing::Spring;
///
/// let mut spring = Spring::new(0.5).unwrap();
/// spring.update(0.0, 0.1); // the first target is the starting value
/// let mut value = 0.0;
/// for _ in 0..100 {
///     value = spring.update(10.0, 0.1);
///     assert!(value <= 10.0); // from rest, never past the target
/// }
/// assert!((value - 10.0).abs() < 1e-6);
/// ```
#[derive(Debug, Clone)]
pub struct Spring {
    smooth_time: f64,
    omega: f64,
    motion: Motion,
    warmup: Warmup,
    /// What `reset` restores.
    seed: Option<f64>,
}

/// A [`Spring`] reading: where it is and how fast it is moving.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Motion {
    /// The current value.
    pub value: f64,
    /// The rate of change, in value per unit of `dt`.
    pub velocity: f64,
}

impl Motion {
    /// At rest at `value`.
    const fn at_rest(value: f64) -> Self {
        Self {
            value,
            velocity: 0.0,
        }
    }

    /// Whether both parts are finite.
    #[inline]
    fn is_finite(&self) -> bool {
        self.value.is_finite() && self.velocity.is_finite()
    }
}

impl Spring {
    /// Creates a spring with the given smooth time.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `smooth_time` is not finite and
    /// positive, or is so small that `2 / smooth_time` overflows.
    pub fn new(smooth_time: f64) -> Result<Self, nexus_stats_core::ConfigError> {
        let omega = 2.0 / smooth_time;
        if !(smooth_time.is_finite() && smooth_time > 0.0 && omega.is_finite()) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "smooth_time must be finite, positive, and large enough to divide into 2",
            ));
        }
        Ok(Self {
            smooth_time,
            omega,
            motion: Motion::at_rest(0.0),
            warmup: Warmup::new(1, false),
            seed: None,
        })
    }

    /// Moves toward `target` over `dt` and returns the new value.
    ///
    /// The first target is the starting value, unless the spring was
    /// seeded, in which case it moves from the seed.
    ///
    /// Does not validate; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, target: f64, dt: f64) -> f64 {
        let next = self.next(target, dt);
        self.take(next)
    }

    /// Checked update. Moves toward `target`, or returns an error and
    /// leaves the spring unchanged if `target` is NaN or infinite, if `dt`
    /// is NaN, infinite or negative, or if the step overflows.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `target` or `dt` is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if
    ///   `target` or `dt` is infinite.
    /// - [`DataError::Negative`](nexus_stats_core::DataError::Negative) if
    ///   `dt` is negative.
    /// - [`DataError::OutOfRange`](nexus_stats_core::DataError::OutOfRange)
    ///   if the value or the velocity after the step would not be finite.
    #[inline]
    pub fn checked_update(
        &mut self,
        target: f64,
        dt: f64,
    ) -> Result<f64, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_inputs!(target, dt)?;
        if dt < 0.0 {
            return Err(nexus_stats_core::DataError::Negative);
        }
        let next = self.next(target, dt);
        if !next.is_finite() {
            return Err(nexus_stats_core::DataError::OutOfRange);
        }
        Ok(self.take(next))
    }

    /// The value and velocity, or `None` before the first target of an
    /// unseeded spring.
    #[must_use]
    pub fn reading(&self) -> Option<Motion> {
        if !self.warmup.is_primed() {
            return None;
        }
        Some(self.motion)
    }

    /// The configured smooth time.
    #[must_use]
    pub fn smooth_time(&self) -> f64 {
        self.smooth_time
    }

    /// Updates since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.warmup.count()
    }

    /// Whether the spring has a value: it was seeded or has taken a target.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.warmup.is_primed()
    }

    /// Returns to the as-built state: at rest, at the seed if there is one.
    pub fn reset(&mut self) {
        self.motion = Motion::at_rest(self.seed.unwrap_or(0.0));
        self.warmup.reset();
    }

    /// Resets to rest at `value`, which becomes the seed: the next update
    /// moves from it, and later calls to [`reset`](Self::reset) return to
    /// it.
    ///
    /// # Errors
    ///
    /// `Invalid` if `value` is not finite. The spring is left unchanged.
    pub fn reset_with_seed(&mut self, value: f64) -> Result<(), nexus_stats_core::ConfigError> {
        if !value.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "seed must be finite",
            ));
        }
        self.seed = Some(value);
        self.motion = Motion::at_rest(value);
        self.warmup.reset_seeded();
        Ok(())
    }

    /// Where the spring is after moving toward `target` for `dt`. Changes
    /// nothing.
    #[inline]
    fn next(&self, target: f64, dt: f64) -> Motion {
        // The first target of an unseeded spring is where it starts.
        if self.warmup.count() == 0 && self.seed.is_none() {
            return Motion::at_rest(target);
        }
        let next = self.step(target, dt);
        if passed(self.motion.value, next.value, target) {
            return stopped_at(target, self.motion.velocity, dt);
        }
        next
    }

    /// Moves to `next`, counts the update and returns the new value.
    #[inline]
    fn take(&mut self, next: Motion) -> f64 {
        self.motion = next;
        self.warmup.tick();
        next.value
    }

    /// The published update: where the spring is after `dt`.
    #[inline]
    fn step(&self, target: f64, dt: f64) -> Motion {
        let Motion { value, velocity } = self.motion;
        let decay = decay(self.omega * dt);
        if decay == 0.0 {
            // Fully settled. The formula would multiply an overflow by zero.
            return Motion::at_rest(target);
        }
        let offset = value - target;
        let temp = self.omega.fma(offset, velocity) * dt;
        Motion {
            value: (offset + temp).fma(decay, target),
            velocity: self.omega.fma(-temp, velocity) * decay,
        }
    }
}

/// Stopped at the target. With no time elapsed nothing moved, so the
/// velocity is kept.
#[inline]
fn stopped_at(target: f64, start_velocity: f64, dt: f64) -> Motion {
    Motion {
        value: target,
        velocity: if dt == 0.0 { start_velocity } else { 0.0 },
    }
}

/// The published approximation of `exp(-x)`, for `x = omega * dt`:
/// `1 / (1 + x + 0.48 x^2 + 0.235 x^3)`.
#[inline]
fn decay(x: f64) -> f64 {
    1.0 / x.fma(x.fma(x.fma(0.235, 0.48), 1.0), 1.0)
}

/// Whether a step from `start` to `value` crossed `target`: began on one
/// side and ended on the other. A step that begins on the target does not.
#[inline]
fn passed(start: f64, value: f64, target: f64) -> bool {
    (start < target && value > target) || (start > target && value < target)
}

#[cfg(test)]
#[allow(clippy::unreadable_literal)]
mod tests {
    use super::*;
    use nexus_stats_core::DataError::{Infinite, Negative, NotANumber};

    /// (target, value, velocity) after each update, from a direct port of
    /// the published formula.
    type Steps = &'static [(f64, f64, f64)];

    const EVEN: Steps = &[
        (10.0, 0.6156156156156136, 10.725010725010726),
        (10.0, 1.912244566684718, 14.378231881449388),
        (10.0, 3.3739312402828334, 14.456877293928361),
        (10.0, 4.750905905317461, 12.920847002295478),
        (10.0, 5.9401497262937, 10.826267396550135),
        (10.0, 6.915779410973156, 8.708387545487561),
    ];
    const MOVING_TARGET: Steps = &[
        (5.0, 1.0004875097101857, 0.06298444866598132),
        (5.0, 1.001966720197382, 0.12397002417992614),
        (-3.0, 1.0034310166944183, 0.05703540635743629),
        (-3.0, 1.00384117472671, -0.0078061906227980486),
        (4.0, 1.0040834217037151, 0.039618448013301354),
    ];
    const LONG_STEP: Steps = &[
        (10.0, 9.625850340136054, 2.2675736961451247),
        (10.0, 9.997570456754131, 0.015425671402347832),
        (10.0, 9.999987801127208, 7.870240511383517e-05),
    ];

    #[test]
    fn matches_the_published_formula() {
        for (smooth_time, dt, start, steps) in [
            (0.5, 0.1, 0.0, EVEN),
            (2.0, 0.016, 1.0, MOVING_TARGET),
            (0.3, 1.5, 0.0, LONG_STEP),
        ] {
            let mut spring = Spring::new(smooth_time).unwrap();
            assert_eq!(spring.update(start, dt), start);
            for (i, &(target, value, velocity)) in steps.iter().enumerate() {
                let got = spring.update(target, dt);
                assert!((got - value).abs() <= 1e-13 * value.abs().max(1.0), "{i}");
                let got = spring.reading().map(|m| m.velocity).unwrap();
                assert!(
                    (got - velocity).abs() <= 1e-12 * velocity.abs().max(1.0),
                    "velocity at {i}: {got} vs {velocity}"
                );
            }
        }
    }

    #[test]
    fn it_reaches_the_target_and_never_passes_it() {
        for (smooth_time, dt) in [(0.5, 0.01), (0.5, 0.4), (0.1, 5.0), (3.0, 0.016)] {
            for (start, target) in [(0.0, 10.0), (10.0, -4.0)] {
                let mut spring = Spring::new(smooth_time).unwrap();
                spring.update(start, dt);
                let mut value = start;
                for _ in 0..20_000 {
                    value = spring.update(target, dt);
                    let between = (value - start) * (value - target) <= 0.0;
                    assert!(between, "{value} outside {start}..{target}");
                }
                assert!((value - target).abs() < 1e-6, "ended at {value}");
            }
        }
    }

    /// A step that overflows without having settled: the unchecked form
    /// follows the arithmetic, the checked form refuses and changes nothing.
    #[test]
    fn a_step_that_overflows_is_refused_by_checked_update() {
        use nexus_stats_core::DataError::OutOfRange;

        // (smooth_time, start, target, dt)
        for (smooth_time, start, target, dt) in [
            (0.5, 1e308, -1e308, 0.1),
            (1e-300, 0.0, 1e10, 0.0),
            (1e-300, -5e7, 0.0, 1e-300),
        ] {
            let mut spring = Spring::new(smooth_time).unwrap();
            spring.update(start, 0.1);
            let before = (spring.reading(), spring.count());
            assert_eq!(spring.checked_update(target, dt), Err(OutOfRange));
            assert_eq!((spring.reading(), spring.count()), before);
            spring.update(target, dt);
            let after = spring.reading().unwrap();
            assert!(!(after.value.is_finite() && after.velocity.is_finite()));
        }
    }

    #[test]
    fn update_follows_the_arithmetic_on_a_nan() {
        let mut spring = Spring::new(0.5).unwrap();
        spring.update(0.0, 0.1);
        assert!(spring.update(10.0, f64::NAN).is_nan());
        spring.reset();
        spring.update(0.0, 0.1);
        assert!(spring.update(f64::NAN, 0.1).is_nan());
    }

    /// Finite settings at which the decay is exactly zero.
    #[test]
    fn a_step_too_long_to_resolve_lands_at_rest_on_the_target() {
        for (smooth_time, dt) in [
            (1e-300, 0.1),
            (1e-160, 0.1),
            (0.5, 1e308),
            (0.5, f64::MAX),
            (1e-200, 1e200),
        ] {
            let mut spring = Spring::new(smooth_time).unwrap();
            spring.update(0.0, dt);
            for target in [10.0, -3.0, -3.0, 1e100] {
                let value = spring.checked_update(target, dt).unwrap();
                assert_eq!(value, target, "smooth_time {smooth_time:e} dt {dt:e}");
                assert_eq!(spring.reading(), Some(Motion::at_rest(target)));
            }
        }
    }

    /// On the target with velocity, the spring carries through, the same
    /// way in both directions, then eases back.
    #[test]
    fn a_spring_on_the_target_with_velocity_carries_through_either_way() {
        for direction in [1.0, -1.0] {
            let mut spring = Spring::new(0.5).unwrap();
            spring.update(0.0, 0.1);
            let on = spring.update(10.0 * direction, 0.1);
            let velocity = spring.reading().unwrap().velocity;
            assert!(velocity * direction > 0.0);
            // Retarget to where it is: it keeps moving the way it was going.
            let after = spring.update(on, 0.1);
            assert!(
                (after - on) * direction > 0.0,
                "{direction}: {on} -> {after}"
            );
            // Mirror images of each other.
            if direction < 0.0 {
                let mut mirror = Spring::new(0.5).unwrap();
                mirror.update(0.0, 0.1);
                let m_on = mirror.update(10.0, 0.1);
                assert_eq!(mirror.update(m_on, 0.1), -after);
            }
            // It then eases back toward the target.
            let mut value = after;
            for _ in 0..200 {
                value = spring.update(on, 0.1);
            }
            assert!((value - on).abs() < 1e-9, "{direction}: ended at {value}");
        }
    }

    #[test]
    fn no_time_elapsed_moves_nothing() {
        let mut spring = Spring::new(0.5).unwrap();
        spring.update(0.0, 0.1);
        let value = spring.update(10.0, 0.1);
        let velocity = spring.reading().map(|m| m.velocity);
        // Up to the rounding of `target + (value - target)`.
        assert!((spring.update(10.0, 0.0) - value).abs() < 1e-14);
        assert_eq!(spring.reading().map(|m| m.velocity), velocity);
    }

    #[test]
    fn a_seed_is_the_starting_value() {
        let mut spring = Spring::new(0.5).unwrap();
        assert_eq!(
            (
                spring.reading().map(|m| m.value),
                spring.reading().map(|m| m.velocity)
            ),
            (None, None)
        );
        spring.reset_with_seed(100.0).unwrap();
        assert_eq!(
            (
                spring.reading().map(|m| m.value),
                spring.reading().map(|m| m.velocity)
            ),
            (Some(100.0), Some(0.0))
        );
        // The first update moves from the seed; it is not the starting value.
        let value = spring.update(0.0, 0.1);
        assert!(value < 100.0 && value > 0.0);
        spring.reset();
        assert_eq!(
            (spring.reading().map(|m| m.value), spring.count()),
            (Some(100.0), 0)
        );
        assert!(spring.reset_with_seed(f64::NAN).is_err());
        assert_eq!(spring.reading().map(|m| m.value), Some(100.0));
    }

    #[test]
    fn reset_without_a_seed_starts_over() {
        let mut spring = Spring::new(0.5).unwrap();
        spring.update(0.0, 0.1);
        spring.update(10.0, 0.1);
        spring.reset();
        assert_eq!(
            (spring.reading().map(|m| m.value), spring.is_primed()),
            (None, false)
        );
        assert_eq!(spring.update(7.0, 0.1), 7.0);
        assert_eq!(spring.reading().map(|m| m.velocity), Some(0.0));
    }

    #[test]
    fn smooth_time_must_be_finite_and_positive() {
        for bad in [0.0, -1.0, f64::NAN, f64::INFINITY] {
            assert!(Spring::new(bad).is_err(), "{bad}");
        }
        // So small that 2 / smooth_time overflows.
        assert!(Spring::new(1e-308).is_err());
        assert!(Spring::new(5e-324).is_err());
        assert!(Spring::new(f64::MIN_POSITIVE).is_ok());
        assert_eq!(Spring::new(0.25).unwrap().smooth_time(), 0.25);
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        let mut spring = Spring::new(0.5).unwrap();
        assert_eq!(spring.checked_update(f64::NAN, 0.1), Err(NotANumber));
        assert_eq!(spring.count(), 0);
        spring.checked_update(0.0, 0.1).unwrap();
        spring.checked_update(10.0, 0.1).unwrap();
        let before = (
            spring.reading().map(|m| m.value),
            spring.reading().map(|m| m.velocity),
            spring.count(),
        );
        assert_eq!(spring.checked_update(f64::INFINITY, 0.1), Err(Infinite));
        assert_eq!(spring.checked_update(1.0, f64::NAN), Err(NotANumber));
        assert_eq!(spring.checked_update(1.0, f64::INFINITY), Err(Infinite));
        assert_eq!(spring.checked_update(1.0, -0.1), Err(Negative));
        assert_eq!(
            (
                spring.reading().map(|m| m.value),
                spring.reading().map(|m| m.velocity),
                spring.count()
            ),
            before
        );
        assert!(spring.checked_update(1.0, 0.0).is_ok());
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let (mut checked, mut plain) = (Spring::new(0.7).unwrap(), Spring::new(0.7).unwrap());
        for (target, dt) in [
            (1.0, 0.1),
            (5.0, 0.1),
            (5.0, 0.0),
            (-3.0, 2.5),
            (1e12, 0.01),
        ] {
            assert_eq!(
                checked.checked_update(target, dt),
                Ok(plain.update(target, dt))
            );
        }
    }
}
