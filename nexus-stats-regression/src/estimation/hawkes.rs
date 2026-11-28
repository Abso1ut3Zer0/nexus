use core::marker::PhantomData;

use nexus_stats_core::math::{MulAdd, sqrt, step_mean};
use nexus_stats_core::parts::LastTime;
use nexus_stats_core::{Span, Tick};

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
/// The sum is kept in one number, so an event costs one exponential. The
/// process is stable when `alpha < beta`, which `build` requires. See
/// [Hawkes process](https://en.wikipedia.org/wiki/Hawkes_process).
///
/// This is the model: you give it its parameters. To fit them from
/// events, use a [`HawkesEstimator`].
///
/// # Weighting clock
///
/// The caller's clock, any [`Tick`]. The intensity decays by the span
/// between events, so any event rate is correct. The rates are per unit
/// of that clock. On physical time (any
/// [`Timestamp`](nexus_stats_core::Timestamp)) the unit is the second, so `mu` is events per second and `beta` is per
/// second. On another clock, traded volume as an `f64` say, they are per
/// unit of volume.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::estimation::HawkesModel;
///
/// let mut hawkes = HawkesModel::builder()
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
pub struct HawkesModel<T: Tick> {
    mu: f64,
    alpha: f64,
    beta: f64,
    /// `alpha * sum of exp(-beta * (last - t_i))`, as of the last event.
    excitation: f64,
    last: LastTime<T>,
    count: u64,
}

/// Builder for [`HawkesModel`].
#[derive(Debug, Clone)]
pub struct HawkesModelBuilder<T: Tick> {
    mu: Option<f64>,
    alpha: Option<f64>,
    beta: Option<f64>,
    clock: PhantomData<T>,
}

impl<T: Tick> HawkesModel<T> {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> HawkesModelBuilder<T> {
        HawkesModelBuilder {
            mu: None,
            alpha: None,
            beta: None,
            clock: PhantomData,
        }
    }

    /// Records an event at `time`.
    ///
    /// An event at a tick that is not at or after the last one taken is
    /// ignored. See
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
    /// leaves the state unchanged if `time` is not at or after the last
    /// event.
    ///
    /// # Errors
    ///
    /// [`DataError::NonMonotonicTime`](nexus_stats_core::DataError::NonMonotonicTime)
    /// if `time` is not at or after the last event taken.
    #[inline]
    pub fn checked_update(&mut self, time: T) -> Result<(), nexus_stats_core::DataError> {
        self.last.check(time)?;
        self.update(time);
        Ok(())
    }

    /// The intensity just after the last event, in events per unit of the
    /// clock. The baseline `mu` before any event.
    #[must_use]
    pub fn intensity(&self) -> f64 {
        self.mu + self.excitation
    }

    /// The intensity at `time`, with no new event.
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
    fn decay_over(&self, elapsed: T::Span) -> f64 {
        nexus_stats_core::math::exp(-(self.beta * elapsed.as_f64()))
    }
}

impl<T: Tick> HawkesModelBuilder<T> {
    /// Baseline intensity, in events per unit of the clock. Positive.
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

    /// Decay rate of a raise, per unit of the clock. Positive.
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
    pub fn build(self) -> Result<HawkesModel<T>, nexus_stats_core::ConfigError> {
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
        Ok(HawkesModel {
            mu,
            alpha,
            beta,
            excitation: 0.0,
            last: LastTime::new(),
            count: 0,
        })
    }
}

/// The parameters of a Hawkes process, fitted from events.
///
/// Feed it each event's time. It counts events in windows of a length you
/// choose and reads the clustering from how much those counts scatter:
/// Hardiman and Bouchaud's estimator (2014). With `m` the mean count in a
/// window and `v` its variance:
///
/// ```text
/// rate            = m / window
/// branching ratio = 1 - sqrt(m / v)
/// baseline        = rate (1 - branching ratio)
/// ```
///
/// Independent events give a variance equal to the mean, and a branching
/// ratio of zero. Clustering fills some windows and empties others, which
/// raises the variance. Everything is a closed form over running sums.
///
/// This type does the fitting and nothing else. [`summary`](Self::summary)
/// has everything about the fit, and [`model`](Self::model) gives the
/// fitted [`HawkesModel`].
///
/// # The window is yours to choose
///
/// It is a setting of the fit, not something the fit finds. It must be
/// long next to a cluster, which lasts about `1 / (beta - alpha)`. A
/// shorter window cuts clusters apart and the branching ratio reads low.
/// This is the estimate, by the window's length in cluster times:
///
/// | True ratio | 1 | 3 | 10 | 30 | 100 |
/// |---|---|---|---|---|---|
/// | 0.2 | 0.09 | 0.15 | 0.185 | 0.195 | 0.199 |
/// | 0.5 | 0.31 | 0.43 | 0.48 | 0.494 | 0.498 |
/// | 0.8 | 0.68 | 0.76 | 0.79 | 0.797 | 0.799 |
///
/// A longer window has less bias and, from the same data, fewer windows
/// to take a variance from. At a true ratio of one half the estimate
/// scatters by about 0.075 with 30 windows, 0.04 with 100, 0.013 with
/// 1,000 and 0.004 with 10,000. To check a window, run a second
/// estimator on one several times longer: where the two agree, both are
/// long enough.
///
/// The table follows from the covariance of the process (Laub, Taimre
/// and Pollett, 2015, Theorem 2) and matches simulation to three digits.
///
/// # The decay is yours to choose too
///
/// The method gives the branching ratio, which is `alpha / beta`, and not
/// the two apart: a window's mean and variance are two numbers, and the
/// model has three parameters. So the decay `beta` is a setting, as it is
/// in the `tick` library's exponential learner, and
/// [`model`](Self::model) uses it. It does not change the fit. To fit all
/// three at once, use maximum likelihood offline.
///
/// It assumes a steady baseline. One that drifts looks like clustering
/// and raises the ratio. Remove a known daily pattern before feeding it.
///
/// # Examples
///
/// ```
/// use core::time::Duration;
/// use nexus_stats_regression::estimation::HawkesEstimator;
///
/// // Events on nanosecond time, counted in ten-second windows.
/// let mut fit = HawkesEstimator::<i64>::builder()
///     .window(Duration::from_secs(10))
///     .decay(2.0) // per second
///     .build()
///     .unwrap();
/// for second in [1, 2, 3, 12, 35, 36, 41] {
///     fit.update(second * 1_000_000_000);
/// }
/// // Four windows have closed since the first event at 1 s. They held
/// // 3, 1, 0 and 2 events. The event at 41 s is in a window still open.
/// let summary = fit.summary();
/// assert_eq!((summary.windows(), summary.events()), (4, 6));
/// assert!((summary.rate().unwrap() - 6.0 / 40.0).abs() < 1e-15);
/// ```
#[derive(Debug, Clone)]
pub struct HawkesEstimator<T: Tick> {
    /// The window's length, in units of the clock.
    window: f64,
    /// The decay `beta` the fitted model takes.
    decay: f64,
    /// The first event, where the first window starts.
    origin: Option<T>,
    last: LastTime<T>,
    open: OpenWindow,
    closed: WindowCounts,
}

/// Builder for [`HawkesEstimator`].
#[derive(Debug, Clone)]
pub struct HawkesEstimatorBuilder<T: Tick> {
    window: Option<T::Span>,
    decay: Option<f64>,
}

impl<T: Tick> HawkesEstimator<T> {
    /// Creates a builder. The window and the decay must be set.
    #[inline]
    #[must_use]
    pub fn builder() -> HawkesEstimatorBuilder<T> {
        HawkesEstimatorBuilder {
            window: None,
            decay: None,
        }
    }

    /// Records an event at `time`.
    ///
    /// The first event starts the first window. An event at a tick that
    /// is not at or after the last one taken is ignored. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, time: T) {
        if self.last.would_go_back(time) {
            return;
        }
        self.last.set(time);
        // The first event is its own origin, in window 0.
        let origin = *self.origin.get_or_insert(time);
        let index = self.window_of(time.since(origin));
        if index > self.open.index {
            self.close_through(index);
        }
        self.open.events += 1;
    }

    /// Checked update. Records an event at `time`, or returns an error and
    /// leaves the state unchanged if `time` is not at or after the last
    /// event.
    ///
    /// # Errors
    ///
    /// [`DataError::NonMonotonicTime`](nexus_stats_core::DataError::NonMonotonicTime)
    /// if `time` is not at or after the last event taken.
    #[inline]
    pub fn checked_update(&mut self, time: T) -> Result<(), nexus_stats_core::DataError> {
        self.last.check(time)?;
        self.update(time);
        Ok(())
    }

    /// The fit so far, from the windows that have closed. Changes nothing.
    #[inline]
    #[must_use]
    pub fn summary(&self) -> HawkesSummary {
        HawkesSummary {
            window: self.window,
            closed: self.closed,
        }
    }

    /// The fitted model: the baseline from the fit, the decay `beta` the
    /// estimator was built with, and `alpha` as the branching ratio times
    /// that decay.
    ///
    /// `None` until the fit has a branching ratio from 0 up to 1. A ratio
    /// below zero is data a Hawkes process does not describe.
    #[must_use]
    pub fn model(&self) -> Option<HawkesModel<T>> {
        let summary = self.summary();
        let ratio = summary.branching_ratio()?;
        HawkesModel::builder()
            .mu(summary.baseline()?)
            .alpha(ratio * self.decay)
            .beta(self.decay)
            .build()
            .ok()
    }

    /// Forgets every event. The window and the decay are kept.
    pub fn reset(&mut self) {
        self.origin = None;
        self.last.reset();
        self.open = OpenWindow::default();
        self.closed = WindowCounts::default();
    }

    /// Closes the open window and every empty one before window `index`,
    /// which becomes the open one.
    #[inline]
    fn close_through(&mut self, index: u64) {
        self.closed.record(self.open.events);
        self.closed.record_empty(index - self.open.index - 1);
        self.open = OpenWindow { index, events: 0 };
    }

    /// Which window a time `since_origin` after the first event is in,
    /// counted from 0. A window holds its start and not its end.
    #[inline]
    fn window_of(&self, since_origin: T::Span) -> u64 {
        (since_origin.as_f64() / self.window) as u64
    }
}

impl<T: Tick> HawkesEstimatorBuilder<T> {
    /// The length of a counting window, a span of the clock. Required,
    /// and fixed: counts from windows of one length cannot be joined with
    /// another's. Choose it long next to a cluster, which lasts about
    /// `1 / (beta - alpha)`.
    #[must_use]
    pub fn window(mut self, window: T::Span) -> Self {
        self.window = Some(window);
        self
    }

    /// The decay `beta` of the fitted model, per unit of the clock: how
    /// fast the raise from one event fades. Required. It is the model's,
    /// and plays no part in the fit.
    #[must_use]
    pub fn decay(mut self, beta: f64) -> Self {
        self.decay = Some(beta);
        self
    }

    /// Builds the estimator.
    ///
    /// # Errors
    ///
    /// - `Missing` if the window or the decay was not set.
    /// - `Invalid` if either is not positive and finite.
    pub fn build(self) -> Result<HawkesEstimator<T>, nexus_stats_core::ConfigError> {
        use nexus_stats_core::ConfigError::{Invalid, Missing};
        use nexus_stats_core::math::positive_finite;

        let window = self.window.ok_or(Missing("window"))?.as_f64();
        let decay = self.decay.ok_or(Missing("decay"))?;
        if !positive_finite(window) {
            return Err(Invalid("Hawkes window must be positive and finite"));
        }
        if !positive_finite(decay) {
            return Err(Invalid("Hawkes decay must be positive and finite"));
        }
        Ok(HawkesEstimator {
            window,
            decay,
            origin: None,
            last: LastTime::new(),
            open: OpenWindow::default(),
            closed: WindowCounts::default(),
        })
    }
}

/// The window still filling.
#[derive(Debug, Clone, Copy, Default)]
struct OpenWindow {
    /// Which window it is, counted from the first.
    index: u64,
    /// Events in it so far.
    events: u64,
}

/// The running mean and scatter of the counts of the closed windows, by
/// Welford's algorithm.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
struct WindowCounts {
    windows: u64,
    events: u64,
    mean: f64,
    /// The sum of squared distances from the mean.
    squares: f64,
}

impl WindowCounts {
    #[inline]
    fn record(&mut self, count: u64) {
        self.windows += 1;
        self.events += count;
        let step = step_mean(&mut self.mean, count as f64, 1.0 / self.windows as f64);
        self.squares = step.before.fma(step.after, self.squares);
    }

    /// Records `empty` windows with no events, in one step.
    #[inline]
    fn record_empty(&mut self, empty: u64) {
        if empty == 0 {
            return;
        }
        let (had, empty_windows) = (self.windows as f64, empty as f64);
        let kept = had / (had + empty_windows);
        // Zeros pull the mean down by `kept`, and each sits the old mean
        // away from it.
        self.squares = (self.mean * self.mean).fma(empty_windows * kept, self.squares);
        self.mean *= kept;
        self.windows += empty;
    }

    #[inline]
    fn variance(self) -> f64 {
        self.squares / (self.windows - 1) as f64
    }
}

/// How good a [`HawkesEstimator`]'s fit is, from its
/// [`summary`](HawkesEstimator::summary).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HawkesSummary {
    window: f64,
    closed: WindowCounts,
}

impl HawkesSummary {
    /// Windows that have closed. The fit is read from these. The open one
    /// is left out until an event arrives past its end.
    #[inline]
    #[must_use]
    pub fn windows(&self) -> u64 {
        self.closed.windows
    }

    /// Events in the closed windows.
    #[inline]
    #[must_use]
    pub fn events(&self) -> u64 {
        self.closed.events
    }

    /// The mean rate, in events per unit of the clock: the baseline and
    /// what it sets off together. `None` until a window has closed.
    ///
    /// It is above the [`baseline`](Self::baseline) by the factor
    /// `1 / (1 - branching ratio)`: at a ratio of one half, half the
    /// events were set off by others and the rate is twice the baseline.
    #[inline]
    #[must_use]
    pub fn rate(&self) -> Option<f64> {
        if self.closed.windows == 0 {
            return None;
        }
        Some(self.closed.mean / self.window)
    }

    /// The variance of the count in a window over its mean. `None` until
    /// two windows have closed with an event between them.
    ///
    /// | Value | Reads as |
    /// |---|---|
    /// | about 1 | independent events, a Poisson process |
    /// | above 1 | clustering. A Hawkes process in a long window gives `1 / (1 - branching ratio)^2`, so 4 is a ratio of one half |
    /// | below 1 | more even than chance, which a Hawkes process cannot give |
    /// | 0 | every window held the same count |
    #[inline]
    #[must_use]
    pub fn dispersion(&self) -> Option<f64> {
        if self.closed.windows < 2 || self.closed.events == 0 {
            return None;
        }
        Some(self.closed.variance() / self.closed.mean)
    }

    /// The expected number of events one event sets off, `alpha / beta`:
    /// `1 - sqrt(mean / variance)` of the counts. `None` where
    /// [`dispersion`](Self::dispersion) is, and while every window has
    /// held the same count.
    ///
    /// | Value | Reads as |
    /// |---|---|
    /// | 0 | no event sets off another: a Poisson process |
    /// | 0.5 | each event sets off half an event on average, and half of all events were set off by others |
    /// | near 1 | nearly self-sustaining: almost every event was set off by another |
    /// | below 0 | the counts scatter less than independent events would. A Hawkes process cannot do that, so the data is not one, and [`HawkesEstimator::model`] gives none |
    ///
    /// It is reported as the formula gives it, with no clamp, as in the
    /// paper. It reads low when the window is short. See the table on
    /// [`HawkesEstimator`].
    #[inline]
    #[must_use]
    pub fn branching_ratio(&self) -> Option<f64> {
        let dispersion = self.dispersion()?;
        let scatters = dispersion > 0.0;
        if !scatters {
            return None;
        }
        Some(1.0 - sqrt(1.0 / dispersion))
    }

    /// The baseline intensity `mu`: the rate of the events nothing set
    /// off, `rate (1 - branching ratio)`. `None` where
    /// [`branching_ratio`](Self::branching_ratio) is.
    #[inline]
    #[must_use]
    pub fn baseline(&self) -> Option<f64> {
        Some(self.rate()? * (1.0 - self.branching_ratio()?))
    }
}

#[cfg(test)]
#[allow(clippy::suboptimal_flops)]
mod tests {
    extern crate std;
    use super::*;
    use nexus_stats_core::DataError::NonMonotonicTime;
    use std::time::{Duration, Instant};
    use std::vec::Vec;

    const SECOND: i128 = 1_000_000_000;

    fn hawkes<T: Tick>(mu: f64, alpha: f64, beta: f64) -> HawkesModel<T> {
        HawkesModel::builder()
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

    /// Events at a fixed spacing: the raises form a geometric series.
    #[test]
    fn a_steady_burst_builds_up_to_the_geometric_sum() {
        let (mu, alpha, beta) = (1.0, 0.9, 1.0);
        let mut h = hawkes(mu, alpha, beta);
        let mut previous = mu;
        // One event a millisecond, so each raise decays by exp(-0.001).
        for i in 0..1_000 {
            h.update(i128::from(i) * 1_000_000);
            assert!(h.intensity() > previous);
            previous = h.intensity();
        }
        let kept = (-beta * 0.001_f64).exp();
        let want = mu + alpha * (1.0 - kept.powi(1_000)) / (1.0 - kept);
        assert!((h.intensity() - want).abs() < 1e-9 * want);
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
            HawkesModel::<i128>::builder()
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
            HawkesModel::<i128>::builder()
                .alpha(0.5)
                .beta(1.0)
                .build()
                .is_err()
        );
    }

    /// The clock is the caller's. On traded volume the rates are per unit
    /// of volume, and the numbers match a clock in seconds fed the same
    /// values.
    #[test]
    fn a_volume_clock_gives_the_same_intensity_as_seconds() {
        let mut on_volume = hawkes::<f64>(1.0, 0.5, 2.0);
        let mut on_seconds = hawkes::<i128>(1.0, 0.5, 2.0);
        for millis in [0_i128, 250, 300, 1_750, 1_750, 4_000] {
            on_volume.update(millis as f64 / 1_000.0);
            on_seconds.update(millis * SECOND / 1_000);
            let (a, b) = (on_volume.intensity(), on_seconds.intensity());
            assert!((a - b).abs() < 1e-12 * b, "{a} vs {b}");
        }
        let (a, b) = (
            on_volume.intensity_at(4.5),
            on_seconds.intensity_at(4_500 * SECOND / 1_000),
        );
        assert!((a - b).abs() < 1e-12 * b);
    }

    /// On a counter, one unit is one count: `beta` is per count.
    #[test]
    fn a_counter_clock_decays_per_count() {
        let mut on_u64 = hawkes::<u64>(1.0, 0.5, 2.0);
        let mut on_u32 = hawkes::<u32>(1.0, 0.5, 2.0);
        on_u64.update(10);
        on_u32.update(10);
        let want = 1.0 + 0.5 * (-2.0_f64 * 3.0).exp();
        assert!((on_u64.intensity_at(13) - want).abs() < 1e-15);
        assert!((on_u32.intensity_at(13) - want).abs() < 1e-15);
        // A count that goes back is ignored.
        on_u64.update(9);
        assert_eq!((on_u64.count(), on_u64.intensity()), (1, 1.5));
        assert_eq!(on_u64.checked_update(9), Err(NonMonotonicTime));
    }

    /// A NaN tick would poison every later span. `update` ignores it and
    /// the guarded form reports it, the first event included.
    #[test]
    fn a_nan_tick_is_ignored_and_reported() {
        let mut hawkes = hawkes::<f64>(1.0, 0.5, 2.0);
        hawkes.update(f64::NAN);
        assert_eq!((hawkes.count(), hawkes.intensity()), (0, 1.0));
        assert_eq!(hawkes.checked_update(f64::NAN), Err(NonMonotonicTime));
        hawkes.update(1.0);
        hawkes.update(f64::NAN);
        assert_eq!((hawkes.count(), hawkes.intensity()), (1, 1.5));
        assert_eq!(hawkes.intensity_at(f64::NAN), 1.5);
        hawkes.update(2.0);
        assert!(hawkes.intensity().is_finite());
        assert_eq!(hawkes.count(), 2);
    }

    fn fitter<T: Tick>(window: T::Span) -> HawkesEstimator<T> {
        HawkesEstimator::builder()
            .window(window)
            .decay(2.0)
            .build()
            .unwrap()
    }

    /// A small deterministic generator for the simulations.
    struct Uniform(u64);

    impl Uniform {
        /// In `(0, 1]`.
        fn next(&mut self) -> f64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            ((self.0 >> 11) + 1) as f64 / (1u64 << 53) as f64
        }

        fn exponential(&mut self, rate: f64) -> f64 {
            -self.next().ln() / rate
        }
    }

    /// Event times of a Hawkes process up to `until`, by Ogata's thinning.
    fn simulate(mu: f64, alpha: f64, beta: f64, until: f64, seed: u64) -> std::vec::Vec<f64> {
        let mut uniform = Uniform(seed);
        let (mut time, mut excitation, mut events) = (0.0, 0.0, std::vec::Vec::new());
        loop {
            let bound = mu + excitation;
            let wait = uniform.exponential(bound);
            time += wait;
            if time > until {
                return events;
            }
            excitation *= (-beta * wait).exp();
            if uniform.next() * bound <= mu + excitation {
                events.push(time);
                excitation += alpha;
            }
        }
    }

    /// Windows of 10 from the first event at 0: the counts are 3, 1, 0, 2,
    /// and the event at 41 is in a window still open.
    #[test]
    fn events_are_counted_in_windows_from_the_first() {
        let mut fit = fitter::<f64>(10.0);
        assert_eq!(fit.summary().windows(), 0);
        assert_eq!(fit.summary().rate(), None);
        for time in [0.0, 1.0, 2.0, 12.0, 35.0, 36.0, 41.0] {
            fit.update(time);
        }
        let summary = fit.summary();
        assert_eq!((summary.windows(), summary.events()), (4, 6));
        assert_eq!(summary.rate(), Some(1.5 / 10.0));
        // The counts 3, 1, 0, 2 have a mean of 1.5 and a variance of 5/3.
        let dispersion = summary.dispersion().unwrap();
        assert!((dispersion - (5.0 / 3.0) / 1.5).abs() < 1e-15);
        let ratio = summary.branching_ratio().unwrap();
        assert!((ratio - (1.0 - (1.5_f64 / (5.0 / 3.0)).sqrt())).abs() < 1e-15);
        assert!((summary.baseline().unwrap() - 0.15 * (1.0 - ratio)).abs() < 1e-15);
    }

    /// An event exactly on a boundary opens the next window.
    #[test]
    fn a_window_holds_its_start_and_not_its_end() {
        let mut fit = fitter::<f64>(10.0);
        for time in [5.0, 14.999, 15.0, 25.0] {
            fit.update(time);
        }
        // [5, 15) holds two, [15, 25) holds one, and 25 opens the third.
        assert_eq!((fit.summary().windows(), fit.summary().events()), (2, 3));
    }

    /// A long quiet stretch closes its empty windows in one step, and
    /// counts them the same as one at a time would.
    #[test]
    fn empty_windows_count_as_zeros() {
        let mut together = WindowCounts::default();
        let mut one_by_one = WindowCounts::default();
        for count in [4, 1, 7] {
            together.record(count);
            one_by_one.record(count);
        }
        together.record_empty(1_000);
        for _ in 0..1_000 {
            one_by_one.record(0);
        }
        assert_eq!(together.windows, one_by_one.windows);
        assert!((together.mean / one_by_one.mean - 1.0).abs() < 1e-12);
        assert!((together.variance() / one_by_one.variance() - 1.0).abs() < 1e-12);

        let mut fit = fitter::<f64>(1.0);
        fit.update(0.0);
        fit.update(1e9 + 0.5);
        assert_eq!(fit.summary().windows(), 1_000_000_000);
        assert_eq!(fit.summary().events(), 1);
    }

    /// Independent events have no clustering to find.
    #[test]
    fn a_poisson_stream_has_a_branching_ratio_near_zero() {
        let mut fit = fitter::<f64>(20.0);
        for time in simulate(1.0, 0.0, 1.0, 400_000.0, 0x9E37_79B9_7F4A_7C15) {
            fit.update(time);
        }
        let summary = fit.summary();
        assert!((summary.rate().unwrap() - 1.0).abs() < 0.01);
        assert!(summary.branching_ratio().unwrap().abs() < 0.02);
    }

    /// The fit recovers the parameters of a simulated process, to the bias
    /// the docs state for the window. Here `beta - alpha` is 1, so the
    /// window is its own length in cluster times.
    #[test]
    fn the_fit_recovers_a_simulated_process_to_the_documented_bias() {
        // (true ratio, window, documented estimate)
        for (ratio, window, documented) in
            [(0.5, 30.0, 0.494), (0.5, 3.0, 0.427), (0.8, 30.0, 0.797)]
        {
            let beta = 1.0 / (1.0 - ratio);
            let (alpha, mu) = (ratio * beta, 1.0 - ratio);
            let mut fit = fitter::<f64>(window);
            for time in simulate(mu, alpha, beta, 600_000.0, 0xD1B5_4A32_D192_ED03) {
                fit.update(time);
            }
            let summary = fit.summary();
            let got = summary.branching_ratio().unwrap();
            assert!(
                (got - documented).abs() < 0.02,
                "{ratio} at {window}: {got}"
            );
            // The mean rate is mu / (1 - ratio), which is 1 here.
            assert!((summary.rate().unwrap() - 1.0).abs() < 0.03);
            assert!((summary.baseline().unwrap() - (1.0 - got)).abs() < 0.03);
        }
    }

    #[test]
    fn the_model_is_the_fit_with_the_decay_given() {
        let mut fit = fitter::<f64>(30.0);
        assert!(fit.model().is_none());
        for time in simulate(0.5, 1.0, 2.0, 200_000.0, 0x2545_F491_4F6C_DD1D) {
            fit.update(time);
        }
        let summary = fit.summary();
        let ratio = summary.branching_ratio().unwrap();
        let model = fit.model().unwrap();
        assert_eq!(model.baseline(), summary.baseline().unwrap());
        // alpha is the ratio times the decay of 2, so the model's own
        // ratio is the fit's.
        assert!((model.branching_ratio() - ratio).abs() < 1e-15);
        // Just after an event the intensity is mu + alpha.
        let mut primed = model.clone();
        primed.update(0.0);
        assert!((primed.intensity() - (model.baseline() + ratio * 2.0)).abs() < 1e-12);
    }

    /// Counts that scatter less than independent events would give a ratio
    /// below zero, and no model.
    #[test]
    fn evenly_spaced_events_have_no_hawkes_model() {
        let mut fit = fitter::<f64>(10.0);
        for step in 0..1_000 {
            fit.update(f64::from(step) * 3.7);
        }
        assert!(fit.summary().branching_ratio().unwrap() < 0.0);
        assert!(fit.model().is_none());
        // Every window the same: no scatter at all, so no ratio.
        let mut level = fitter::<f64>(10.0);
        for step in 0..100 {
            level.update(f64::from(step) * 5.0);
        }
        assert_eq!(level.summary().dispersion(), Some(0.0));
        assert_eq!(level.summary().branching_ratio(), None);
    }

    #[test]
    fn on_physical_time_the_window_is_a_duration() {
        use core::time::Duration;

        let mut fit = fitter::<i64>(Duration::from_secs(10));
        for second in [1_i64, 2, 3, 12, 35, 36, 41] {
            fit.update(second * 1_000_000_000);
        }
        // Windows from the first event at 1 s: [1, 11), [11, 21), [21, 31)
        // and [31, 41) hold 3, 1, 0 and 2. The event at 41 s opens the next.
        let summary = fit.summary();
        assert_eq!((summary.windows(), summary.events()), (4, 6));
        assert!((summary.rate().unwrap() - 6.0 / 40.0).abs() < 1e-15);
    }

    #[test]
    fn an_event_before_the_last_is_ignored_and_the_checked_form_says_so() {
        let mut fit = fitter::<f64>(10.0);
        fit.update(50.0);
        fit.update(40.0);
        fit.update(f64::NAN);
        assert_eq!(
            fit.checked_update(49.0),
            Err(nexus_stats_core::DataError::NonMonotonicTime)
        );
        fit.update(61.0);
        assert_eq!((fit.summary().windows(), fit.summary().events()), (1, 1));
        assert_eq!(fit.checked_update(61.0), Ok(()));
    }

    #[test]
    fn reset_forgets_the_events_and_keeps_the_window() {
        let mut fit = fitter::<f64>(10.0);
        for time in [0.0, 5.0, 30.0] {
            fit.update(time);
        }
        fit.reset();
        assert_eq!(fit.summary().windows(), 0);
        fit.update(1_000.0);
        fit.update(1_011.0);
        assert_eq!((fit.summary().windows(), fit.summary().events()), (1, 1));
    }

    #[test]
    fn the_builder_needs_a_usable_window_and_decay() {
        let build = |window: Option<f64>, decay: Option<f64>| {
            let mut builder = HawkesEstimator::<f64>::builder();
            if let Some(window) = window {
                builder = builder.window(window);
            }
            if let Some(decay) = decay {
                builder = builder.decay(decay);
            }
            builder.build()
        };
        assert!(build(Some(10.0), Some(2.0)).is_ok());
        assert!(build(None, Some(2.0)).is_err());
        assert!(build(Some(10.0), None).is_err());
        for bad in [0.0, -1.0, f64::NAN, f64::INFINITY] {
            assert!(build(Some(bad), Some(2.0)).is_err(), "window {bad}");
            assert!(build(Some(10.0), Some(bad)).is_err(), "decay {bad}");
        }
    }
}
