use core::marker::PhantomData;
use core::time::Duration;

use nexus_stats_core::Timestamp;
use nexus_stats_core::math::MulAdd;
use nexus_stats_core::parts::LastTime;

/// Intensity of a self-exciting (Hawkes) point process with an
/// exponential kernel.
///
/// Each event raises the intensity by `alpha`, and the raise then decays
/// at rate `beta`. It models arrivals that cluster: trades, order bursts,
/// alert cascades.
///
/// ```text
/// lambda(t) = mu + alpha * sum over earlier events of exp(-beta * (t - t_i))
/// ```
///
/// The sum is kept in one number, so an event costs one exponential. Time
/// is in seconds: `mu` is events per second and `beta` is per second. The
/// process is stable when `alpha < beta`, which `build` requires. See
/// [Hawkes process](https://en.wikipedia.org/wiki/Hawkes_process).
///
/// # Weighting clock
///
/// The caller's timestamps. The intensity decays by the time elapsed
/// between events, so any event rate is correct.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::estimation::HawkesIntensity;
///
/// let mut hawkes = HawkesIntensity::builder()
///     .mu(1.0)
///     .alpha(0.5)
///     .beta(2.0)
///     .build()
///     .unwrap();
///
/// // Times as nanoseconds. An `Instant` works the same way.
/// hawkes.update(0_i128);
/// assert_eq!(hawkes.intensity(), 1.5); // baseline plus one event
/// // Half a second on, the raise has decayed by exp(-1).
/// let later = hawkes.intensity_at(500_000_000);
/// assert!((later - (1.0 + 0.5 * (-1.0_f64).exp())).abs() < 1e-12);
/// ```
#[derive(Debug, Clone)]
pub struct HawkesIntensity<T: Timestamp> {
    mu: f64,
    alpha: f64,
    beta: f64,
    /// `alpha * sum of exp(-beta * (last - t_i))`, as of the last event.
    excitation: f64,
    last: LastTime<T>,
    count: u64,
}

/// Builder for [`HawkesIntensity`].
#[derive(Debug, Clone)]
pub struct HawkesIntensityBuilder<T: Timestamp> {
    mu: Option<f64>,
    alpha: Option<f64>,
    beta: Option<f64>,
    clock: PhantomData<T>,
}

impl<T: Timestamp> HawkesIntensity<T> {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> HawkesIntensityBuilder<T> {
        HawkesIntensityBuilder {
            mu: None,
            alpha: None,
            beta: None,
            clock: PhantomData,
        }
    }

    /// Records an event at `time`.
    ///
    /// An event timestamped before the last one taken is ignored. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, time: T) {
        if self.last.would_go_back(time) {
            return;
        }
        // What earlier events still contribute. Nothing before the first.
        let carried = self
            .last
            .elapsed_to(time)
            .map_or(0.0, |elapsed| self.decay_over(elapsed) * self.excitation);
        self.take(time, carried);
    }

    /// Checked update. Records an event at `time`, or returns an error and
    /// leaves the state unchanged if `time` is before the last event.
    ///
    /// # Errors
    ///
    /// [`DataError::NonMonotonicTime`](nexus_stats_core::DataError::NonMonotonicTime)
    /// if `time` is before the last event taken.
    #[inline]
    pub fn checked_update(&mut self, time: T) -> Result<(), nexus_stats_core::DataError> {
        self.last.check(time)?;
        self.update(time);
        Ok(())
    }

    /// The intensity just after the last event, in events per second. The
    /// baseline `mu` before any event.
    #[must_use]
    pub fn intensity(&self) -> f64 {
        self.mu + self.excitation
    }

    /// The intensity at `time`, in events per second, with no new event.
    /// A `time` before the last event reads as the last event's time.
    #[must_use]
    pub fn intensity_at(&self, time: T) -> f64 {
        let Some(elapsed) = self.last.elapsed_to(time) else {
            return self.mu;
        };
        self.decay_over(elapsed).fma(self.excitation, self.mu)
    }

    /// The baseline intensity `mu`.
    #[must_use]
    pub fn baseline(&self) -> f64 {
        self.mu
    }

    /// `alpha / beta`: the expected number of events one event sets off.
    #[must_use]
    pub fn branching_ratio(&self) -> f64 {
        self.alpha / self.beta
    }

    /// Events recorded since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one event has been recorded.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Forgets every event. The parameters are kept.
    pub fn reset(&mut self) {
        self.excitation = 0.0;
        self.last.reset();
        self.count = 0;
    }

    /// Records an event at `time`, on top of what earlier events still
    /// contribute.
    #[inline]
    fn take(&mut self, time: T, carried: f64) {
        self.excitation = carried + self.alpha;
        self.last.set(time);
        self.count += 1;
    }

    /// What is left of a raise after `elapsed`: `exp(-beta * elapsed)`.
    #[inline]
    fn decay_over(&self, elapsed: Duration) -> f64 {
        nexus_stats_core::math::exp(-(self.beta * elapsed.as_secs_f64()))
    }
}

impl<T: Timestamp> HawkesIntensityBuilder<T> {
    /// Baseline intensity, in events per second. Positive.
    #[must_use]
    pub fn mu(mut self, mu: f64) -> Self {
        self.mu = Some(mu);
        self
    }

    /// How much one event raises the intensity. Not negative, and below
    /// `beta`.
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Decay rate of a raise, per second. Positive.
    #[must_use]
    pub fn beta(mut self, beta: f64) -> Self {
        self.beta = Some(beta);
        self
    }

    /// Builds the estimator.
    ///
    /// # Errors
    ///
    /// - `Missing` if `mu`, `alpha` or `beta` was not set.
    /// - `Invalid` if `mu` or `beta` is not positive and finite, if `alpha`
    ///   is negative or not finite, or if `alpha >= beta`.
    pub fn build(self) -> Result<HawkesIntensity<T>, nexus_stats_core::ConfigError> {
        use nexus_stats_core::ConfigError::{Invalid, Missing};
        use nexus_stats_core::math::{nonnegative_finite, positive_finite};

        let mu = self.mu.ok_or(Missing("mu"))?;
        let alpha = self.alpha.ok_or(Missing("alpha"))?;
        let beta = self.beta.ok_or(Missing("beta"))?;
        if !positive_finite(mu) {
            return Err(Invalid("Hawkes mu must be positive and finite"));
        }
        if !nonnegative_finite(alpha) {
            return Err(Invalid("Hawkes alpha must be non-negative and finite"));
        }
        if !positive_finite(beta) {
            return Err(Invalid("Hawkes beta must be positive and finite"));
        }
        if alpha >= beta {
            return Err(Invalid("Hawkes alpha must be < beta (branching ratio < 1)"));
        }
        Ok(HawkesIntensity {
            mu,
            alpha,
            beta,
            excitation: 0.0,
            last: LastTime::new(),
            count: 0,
        })
    }
}

#[cfg(test)]
#[allow(clippy::suboptimal_flops)]
mod tests {
    extern crate std;
    use super::*;
    use nexus_stats_core::DataError::NonMonotonicTime;
    use std::time::Instant;
    use std::vec::Vec;

    const SECOND: i128 = 1_000_000_000;

    fn hawkes<T: Timestamp>(mu: f64, alpha: f64, beta: f64) -> HawkesIntensity<T> {
        HawkesIntensity::builder()
            .mu(mu)
            .alpha(alpha)
            .beta(beta)
            .build()
            .unwrap()
    }

    /// The definition, summed over every earlier event.
    fn by_definition(mu: f64, alpha: f64, beta: f64, events: &[i128], at: i128) -> f64 {
        let raises: f64 = events
            .iter()
            .filter(|&&t| t <= at)
            .map(|&t| (-beta * ((at - t) as f64 / 1e9)).exp())
            .sum();
        mu + alpha * raises
    }

    #[test]
    fn matches_the_definition_summed_over_every_event() {
        let (mu, alpha, beta) = (0.8, 0.6, 1.7);
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut h = hawkes(mu, alpha, beta);
        let (mut t, mut events) = (0i128, Vec::new());
        for _ in 0..400 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            // Gaps from zero to two seconds, so events cluster and thin out.
            t += i128::from(state % 2_000_000_001);
            h.update(t);
            events.push(t);
            let want = by_definition(mu, alpha, beta, &events, t);
            assert!((h.intensity() - want).abs() <= 1e-12 * want, "at {t}");
            let later = t + 300_000_000;
            let want = by_definition(mu, alpha, beta, &events, later);
            assert!((h.intensity_at(later) - want).abs() <= 1e-12 * want);
        }
    }

    #[test]
    fn the_baseline_is_the_intensity_before_any_event() {
        let h = hawkes::<i128>(2.0, 0.5, 1.0);
        assert_eq!((h.intensity(), h.intensity_at(5 * SECOND)), (2.0, 2.0));
        assert_eq!((h.baseline(), h.count(), h.is_primed()), (2.0, 0, false));
        assert_eq!(h.branching_ratio(), 0.5);
    }

    #[test]
    fn an_event_raises_the_intensity_by_alpha_and_it_decays_back() {
        let mut h = hawkes(1.0, 0.5, 2.0);
        h.update(0_i128);
        assert_eq!(h.intensity(), 1.5);
        let after = h.intensity_at(SECOND / 2);
        assert!((after - (1.0 + 0.5 * (-1.0_f64).exp())).abs() < 1e-15);
        // Long after, only the baseline is left.
        assert!((h.intensity_at(100 * SECOND) - 1.0).abs() < 1e-12);
        // Reading ahead changes nothing.
        assert_eq!(h.intensity(), 1.5);
    }

    #[test]
    fn events_at_the_same_time_each_add_alpha() {
        let mut h = hawkes(1.0, 0.5, 2.0);
        for _ in 0..3 {
            h.update(7 * SECOND);
        }
        assert_eq!((h.intensity(), h.count()), (2.5, 3));
    }

    #[test]
    fn an_instant_and_nanoseconds_give_the_same_intensity() {
        let start = Instant::now();
        let (mut on_instant, mut on_nanos) = (hawkes(1.0, 0.4, 3.0), hawkes(1.0, 0.4, 3.0));
        for millis in [0u64, 120, 121, 900, 2_500, 2_501] {
            on_instant.update(start + Duration::from_millis(millis));
            on_nanos.update(i128::from(millis) * 1_000_000);
            assert_eq!(on_instant.intensity(), on_nanos.intensity());
        }
        let at = start + Duration::from_millis(3_000);
        assert_eq!(
            on_instant.intensity_at(at),
            on_nanos.intensity_at(3 * SECOND)
        );
    }

    #[test]
    fn an_event_before_the_last_one_is_ignored() {
        let mut h = hawkes(1.0, 0.5, 2.0);
        h.update(10 * SECOND);
        h.update(11 * SECOND);
        let before = (h.intensity(), h.count());
        h.update(10 * SECOND);
        h.update(i128::MIN);
        assert_eq!((h.intensity(), h.count()), before);
        // The clock did not move back: the next event is measured from 11.
        h.update(11 * SECOND);
        assert_eq!(h.intensity(), before.0 + 0.5);
        // Reading before the last event reads as the last event.
        assert_eq!(h.intensity_at(0), h.intensity());
    }

    #[test]
    fn checked_update_reports_time_going_back_and_changes_nothing() {
        let mut h = hawkes(1.0, 0.5, 2.0);
        // Nothing is late before the first event.
        assert_eq!(h.checked_update(-5 * SECOND), Ok(()));
        assert_eq!(h.checked_update(3 * SECOND), Ok(()));
        let before = (h.intensity(), h.count());
        assert_eq!(h.checked_update(3 * SECOND - 1), Err(NonMonotonicTime));
        assert_eq!((h.intensity(), h.count()), before);
        // The same time is not going back.
        assert_eq!(h.checked_update(3 * SECOND), Ok(()));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let (mut checked, mut plain) = (hawkes(0.5, 0.3, 0.9), hawkes(0.5, 0.3, 0.9));
        for t in [
            0,
            1,
            SECOND,
            SECOND,
            4 * SECOND,
            4 * SECOND + 7,
            90 * SECOND,
        ] {
            checked.checked_update(t).unwrap();
            plain.update(t);
            assert_eq!(checked.intensity(), plain.intensity());
        }
    }

    #[test]
    fn a_burst_builds_up_and_stays_below_the_stable_limit() {
        let (mu, alpha, beta) = (1.0, 0.9, 1.0);
        let mut h = hawkes(mu, alpha, beta);
        let mut previous = mu;
        // One event a millisecond: each adds to what the others left.
        for i in 0..1_000 {
            h.update(i128::from(i) * 1_000_000);
            assert!(h.intensity() > previous);
            previous = h.intensity();
        }
        assert!(h.intensity() < mu + alpha * 1_000.0);
    }

    #[test]
    fn reset_forgets_the_events_and_the_clock() {
        let mut h = hawkes(1.0, 0.5, 2.0);
        h.update(50 * SECOND);
        h.reset();
        assert_eq!((h.intensity(), h.count(), h.is_primed()), (1.0, 0, false));
        // An earlier time is fine after a reset.
        assert_eq!(h.checked_update(SECOND), Ok(()));
        assert_eq!(h.intensity(), 1.5);
    }

    #[test]
    fn the_builder_checks_its_parameters() {
        let build = |mu, alpha, beta| {
            HawkesIntensity::<i128>::builder()
                .mu(mu)
                .alpha(alpha)
                .beta(beta)
                .build()
        };
        assert!(build(1.0, 0.5, 1.0).is_ok());
        assert!(build(1.0, 0.0, 1.0).is_ok());
        for (mu, alpha, beta) in [
            (0.0, 0.5, 1.0),
            (-1.0, 0.5, 1.0),
            (f64::NAN, 0.5, 1.0),
            (1.0, -0.1, 1.0),
            (1.0, f64::INFINITY, 1.0),
            (1.0, 0.5, 0.0),
            (1.0, 0.5, f64::NAN),
            (1.0, 1.0, 1.0),
            (1.0, 1.5, 1.0),
        ] {
            assert!(build(mu, alpha, beta).is_err(), "{mu} {alpha} {beta}");
        }
        assert!(
            HawkesIntensity::<i128>::builder()
                .alpha(0.5)
                .beta(1.0)
                .build()
                .is_err()
        );
    }
}
