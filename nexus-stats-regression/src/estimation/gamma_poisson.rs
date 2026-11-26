use core::marker::PhantomData;

#[cfg(any(feature = "std", feature = "libm"))]
use nexus_stats_core::Confidence;
use nexus_stats_core::{DataError, Span, Tick};

/// The rate of a Poisson process, learned from counts, with its
/// uncertainty.
///
/// Feed it how many events were seen over how much exposure. It keeps a
/// Gamma posterior over the rate, starting from a `Gamma(alpha, beta)`
/// prior: after `k` events over an exposure of `t` the posterior is
/// `Gamma(alpha + k, beta + t)`. The update is two additions. See
/// [conjugate prior](https://en.wikipedia.org/wiki/Conjugate_prior).
///
/// This type fits the rate. [`HawkesIntensity`](super::HawkesIntensity) is
/// the model for events that cluster, and it is told its parameters.
///
/// # The interval is an estimate
///
/// [`credible_interval`](Self::credible_interval) is Wilson and Hilferty's
/// closed form, not the exact Gamma quantile. This type is built for a
/// stream, where the events run to thousands and beyond. That is where
/// the closed form is at its best. At 95% it is within one part in a
/// million of exact from a thousand events, in about 20 cycles (under ten nanoseconds),
/// with no search that could fail to converge. The exact quantile needs
/// an iterative search whose hard cases are large counts and extreme
/// tails, which are the cases a stream produces (SciPy's issue 26471,
/// open in 2026, is one about large counts).
///
/// With only a few events the estimate is rough (see the table on the
/// method). For exact intervals on a small sample, compute them offline:
/// `scipy.stats.gamma.interval(confidence, alpha + k, scale=1 / (beta + t))`
/// with your prior's `alpha` and `beta`, and `k` and `t` from
/// [`count`](Self::count) and [`exposure`](Self::exposure). To start this
/// type from a rate `r` fitted offline, trusted as much as `n` events,
/// build it with `alpha = n` and `beta = n / r`.
///
/// # Weighting clock
///
/// The caller's, any [`Tick`]. The exposure is a span of that clock, and
/// the rate is in events per unit of it. On physical time (any
/// [`Timestamp`](nexus_stats_core::Timestamp)) the exposure is a
/// `Duration` and the rate is events per second. On another clock, traded
/// volume as an `f64` say, it is events per unit of volume. With two
/// times in hand the exposure is `now.since(earlier)`.
///
/// # Examples
///
/// ```
/// use core::time::Duration;
/// use nexus_stats_regression::Confidence;
/// use nexus_stats_regression::estimation::GammaPoisson;
///
/// // Checked when this is compiled.
/// const NINETY_FIVE: Confidence = Confidence::new(0.95);
///
/// // Events per second, on nanosecond time.
/// let mut arrivals = GammaPoisson::<i64>::builder().build().unwrap();
/// arrivals.update(100, Duration::from_secs(10));
/// // The prior (1, 1) counts as one event over one second.
/// assert_eq!(arrivals.rate(), 101.0 / 11.0);
/// let interval = arrivals.credible_interval(NINETY_FIVE);
/// assert!(interval.lower < arrivals.rate() && arrivals.rate() < interval.upper);
/// ```
#[derive(Debug, Clone)]
pub struct GammaPoisson<T: Tick> {
    prior: Gamma,
    /// Events seen, apart from the prior.
    events: u64,
    /// Exposure seen, apart from the prior, in units of the clock.
    exposure: f64,
    clock: PhantomData<T>,
}

/// Builder for [`GammaPoisson`].
#[derive(Debug, Clone)]
pub struct GammaPoissonBuilder<T: Tick> {
    alpha: f64,
    beta: f64,
    clock: PhantomData<T>,
}

/// The range a quantity lies in with a stated probability.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct CredibleInterval {
    /// The lower end.
    pub lower: f64,
    /// The upper end.
    pub upper: f64,
}

impl CredibleInterval {
    /// `upper - lower`.
    #[inline]
    #[must_use]
    pub fn width(&self) -> f64 {
        self.upper - self.lower
    }
}

impl<T: Tick> GammaPoisson<T> {
    /// Creates a builder. The prior defaults to `Gamma(1, 1)`, which
    /// counts as one event over one unit of exposure.
    #[inline]
    #[must_use]
    pub fn builder() -> GammaPoissonBuilder<T> {
        GammaPoissonBuilder {
            alpha: 1.0,
            beta: 1.0,
            clock: PhantomData,
        }
    }

    /// Records `count` events over `exposure`.
    ///
    /// The count is a `u64` and adds as `+` does, so past `u64::MAX` it
    /// panics in a debug build and wraps in a release one. An exposure that is not
    /// a number, or is below zero, corrupts the estimate from here on. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, count: u64, exposure: T::Span) {
        self.events += count;
        self.exposure += exposure.as_f64();
    }

    /// Checked update. Records `count` events over `exposure`, or returns
    /// an error and leaves the estimate unchanged. Only an `f64` span, or
    /// a span type of your own, can be refused. A `Duration` or a counter
    /// is never NaN, infinite or negative.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`] if the exposure is NaN.
    /// - [`DataError::Infinite`] if it is infinite.
    /// - [`DataError::Negative`] if it is below zero.
    #[inline]
    pub fn checked_update(&mut self, count: u64, exposure: T::Span) -> Result<(), DataError> {
        check_exposure(exposure.as_f64())?;
        self.update(count, exposure);
        Ok(())
    }

    /// The posterior mean of the rate, in events per unit of the clock.
    #[inline]
    #[must_use]
    pub fn rate(&self) -> f64 {
        self.posterior().mean()
    }

    /// The posterior variance of the rate.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> f64 {
        self.posterior().variance()
    }

    /// An estimate of the equal-tailed interval that holds the rate with
    /// the given confidence: the posterior's quantiles at
    /// [`confidence.tail()`](Confidence::tail) from each end, by Wilson and
    /// Hilferty's closed form (1931). About 20 cycles, under ten nanoseconds.
    ///
    /// The level was checked when the [`Confidence`] was made, so nothing
    /// is checked here and this cannot fail.
    ///
    /// With `shape = alpha + events` and `rate = beta + exposure`:
    ///
    /// ```text
    /// tail  = (1 - confidence) / 2
    /// z     = the standard normal quantile at 1 - tail
    /// v     = 1 / (9 shape)
    /// lower = shape (1 - v - z sqrt(v))^3 / rate
    /// upper = shape (1 - v + z sqrt(v))^3 / rate
    /// ```
    ///
    /// The cube root of the rate, scaled, is close to a normal with mean
    /// `1 - v` and variance `v`, and the two ends are that normal's
    /// quantiles cubed.
    ///
    /// Every answer is a little off the exact one, by an amount that
    /// shrinks as the events grow and grows with the confidence asked for.
    /// This is how far an end of the interval is from the exact end, as a
    /// fraction of its value (the farther of the two ends). The shape is
    /// the prior's `alpha` plus the events seen. It is a distance, not a
    /// rate of failure. The same inputs always give the same answer.
    ///
    /// | Shape | 90% | 95% | 99% | 99.9% |
    /// |---|---|---|---|---|
    /// | 3 | 0.9% | 2.5% | 9.4% | 28% |
    /// | 5 | 0.22% | 0.75% | 2.9% | 8.5% |
    /// | 11 | 0.027% | 0.14% | 0.56% | 1.6% |
    /// | 31 | 0.0044% | 0.018% | 0.083% | 0.23% |
    /// | 101 | 6.4e-6 | 2.3e-5 | 0.011% | 0.031% |
    /// | 1,001 | 1.7e-7 | 5.5e-7 | 3.0e-6 | 8.2e-6 |
    /// | 10,001 | 4.7e-9 | 1.6e-8 | 8.9e-8 | 2.4e-7 |
    /// | 100,001 | 1.5e-10 | 4.9e-10 | 2.8e-9 | 7.6e-9 |
    /// | 1,000,001 | 6.3e-12 | 1.7e-11 | 9.0e-11 | 2.4e-10 |
    ///
    /// The distance depends on the shape and the confidence only, not on
    /// the rate. It falls steadily as the shape grows. With the default
    /// prior and 100 events over 10 seconds, the exact 95% interval is
    /// (7.47874, 11.05698) and this gives (7.47857, 11.05709).
    ///
    /// Below a shape of 3 the interval is poor. The lower end is zero
    /// where the closed form goes negative, which at 95% is a shape below
    /// about 0.63, and below about 0.02 both ends are zero. These are
    /// measurements against a 40-digit reference, not proven bounds.
    ///
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn credible_interval(&self, confidence: Confidence) -> CredibleInterval {
        self.posterior().interval(confidence)
    }

    /// Events recorded since construction or `reset`, apart from the
    /// prior.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.events
    }

    /// Exposure recorded since construction or `reset`, apart from the
    /// prior, in units of the clock.
    #[inline]
    #[must_use]
    pub fn exposure(&self) -> f64 {
        self.exposure
    }

    /// Forgets every observation. The prior is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.events = 0;
        self.exposure = 0.0;
    }

    /// The prior with everything seen added to it.
    #[inline]
    fn posterior(&self) -> Gamma {
        Gamma {
            shape: self.prior.shape + self.events as f64,
            rate: self.prior.rate + self.exposure,
        }
    }
}

impl<T: Tick> GammaPoissonBuilder<T> {
    /// The prior's shape: events it counts as. Positive. Default 1.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = alpha;
        self
    }

    /// The prior's rate: exposure it counts as, in units of the clock.
    /// Positive. Default 1.
    #[inline]
    #[must_use]
    pub fn beta(mut self, beta: f64) -> Self {
        self.beta = beta;
        self
    }

    /// Builds the estimator.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `alpha` or `beta` is not positive and
    /// finite.
    #[inline]
    pub fn build(self) -> Result<GammaPoisson<T>, nexus_stats_core::ConfigError> {
        use nexus_stats_core::ConfigError::Invalid;
        use nexus_stats_core::math::positive_finite;

        if !positive_finite(self.alpha) {
            return Err(Invalid("GammaPoisson alpha must be positive and finite"));
        }
        if !positive_finite(self.beta) {
            return Err(Invalid("GammaPoisson beta must be positive and finite"));
        }
        Ok(GammaPoisson {
            prior: Gamma {
                shape: self.alpha,
                rate: self.beta,
            },
            events: 0,
            exposure: 0.0,
            clock: PhantomData,
        })
    }
}

/// A gamma distribution, by shape and rate.
#[derive(Debug, Clone, Copy)]
struct Gamma {
    shape: f64,
    rate: f64,
}

impl Gamma {
    #[inline]
    fn mean(self) -> f64 {
        self.shape / self.rate
    }

    #[inline]
    fn variance(self) -> f64 {
        self.shape / (self.rate * self.rate)
    }

    /// Wilson and Hilferty's estimate of the equal-tailed interval at
    /// `confidence`.
    #[cfg(any(feature = "std", feature = "libm"))]
    fn interval(self, confidence: Confidence) -> CredibleInterval {
        let (lower, upper) = nexus_stats_core::math::probability::gamma_interval_approx(
            self.shape,
            confidence.tail(),
        );
        CredibleInterval {
            lower: lower / self.rate,
            upper: upper / self.rate,
        }
    }
}

/// `Ok` if `exposure` is a number, finite, and not below zero.
#[inline]
fn check_exposure(exposure: f64) -> Result<(), DataError> {
    // PERF: cold, so naming the reason stays off the accepted path.
    #[cold]
    fn refusal(exposure: f64) -> DataError {
        if exposure.is_nan() {
            DataError::NotANumber
        } else if exposure.is_infinite() {
            DataError::Infinite
        } else {
            DataError::Negative
        }
    }

    if exposure.is_finite() && exposure >= 0.0 {
        return Ok(());
    }
    Err(refusal(exposure))
}

#[cfg(test)]
#[allow(clippy::unreadable_literal, clippy::excessive_precision)]
mod tests {
    extern crate std;
    use super::*;
    use core::time::Duration;

    fn estimator<T: Tick>(alpha: f64, beta: f64) -> GammaPoisson<T> {
        GammaPoisson::builder()
            .alpha(alpha)
            .beta(beta)
            .build()
            .unwrap()
    }

    /// `Gamma(alpha + k, beta + t)`: the mean is `(alpha + k) / (beta + t)`
    /// and the variance `(alpha + k) / (beta + t)^2`.
    #[test]
    fn the_posterior_is_the_prior_plus_what_was_seen() {
        let mut gp = estimator::<f64>(1.0, 1.0);
        assert_eq!((gp.rate(), gp.variance()), (1.0, 1.0));
        gp.update(100, 10.0);
        assert_eq!(gp.rate(), 101.0 / 11.0);
        assert_eq!(gp.variance(), 101.0 / 121.0);
        gp.update(20, 2.0);
        gp.update(0, 3.0);
        assert_eq!((gp.count(), gp.exposure()), (120, 15.0));
        assert_eq!(gp.rate(), 121.0 / 16.0);
    }

    #[test]
    fn the_prior_is_the_estimate_before_any_data() {
        let gp = estimator::<f64>(2.5, 10.0);
        assert_eq!((gp.rate(), gp.count(), gp.exposure()), (0.25, 0, 0.0));
    }

    /// On physical time the exposure is a `Duration` and the rate is per
    /// second, whatever unit the times are in.
    #[test]
    fn on_physical_time_the_rate_is_per_second() {
        use nexus_stats_core::{Micros, Tick as _};

        let mut on_nanos = estimator::<i64>(1.0, 1.0);
        on_nanos.update(50, Duration::from_millis(2_500));
        assert_eq!(on_nanos.rate(), 51.0 / 3.5);

        // The exposure from two times.
        let mut on_micros = estimator::<Micros>(1.0, 1.0);
        on_micros.update(50, Micros(4_000_000).since(Micros(1_500_000)));
        assert_eq!(on_micros.rate(), on_nanos.rate());

        let mut on_instant = estimator::<std::time::Instant>(1.0, 1.0);
        on_instant.update(50, Duration::from_millis(2_500));
        assert_eq!(on_instant.rate(), on_nanos.rate());
    }

    /// On another clock the rate is per unit of that clock.
    #[test]
    fn on_a_counter_or_a_volume_clock_the_rate_is_per_unit() {
        let mut per_trade = estimator::<u64>(1.0, 1.0);
        per_trade.update(30, 999);
        assert_eq!(per_trade.rate(), 31.0 / 1_000.0);

        let mut per_lot = estimator::<f64>(1.0, 1.0);
        per_lot.update(30, 999.0);
        assert_eq!(per_lot.rate(), per_trade.rate());
    }

    /// The count is kept as an integer, so it is exact with any prior.
    #[test]
    fn the_count_is_exact_with_a_fractional_prior() {
        let mut gp = estimator::<f64>(0.1, 0.3);
        gp.update(3, 0.2);
        gp.update((1 << 53) + 1, 1.0);
        assert_eq!(gp.count(), (1 << 53) + 4);
        assert_eq!(gp.exposure(), 1.2);
    }

    #[test]
    fn more_data_narrows_the_estimate() {
        let mut gp = estimator::<f64>(1.0, 1.0);
        gp.update(10, 1.0);
        let (early, early_width) = (
            gp.variance(),
            gp.credible_interval(Confidence::new(0.95)).width(),
        );
        gp.update(1_000, 100.0);
        assert!(gp.variance() < early);
        let interval = gp.credible_interval(Confidence::new(0.95));
        assert!(interval.width() < early_width);
        assert!(interval.lower < gp.rate() && gp.rate() < interval.upper);
    }

    // Exact intervals from mpmath 1.4.1 at 40 digits, the Gamma posterior's
    // quantiles divided by its rate, for
    // `(alpha, beta, k, t, confidence, lower, upper)`. SciPy 1.18.1's
    // `gamma.interval(confidence, alpha + k, scale=1/(beta + t))` agrees.
    const INTERVALS: [(f64, f64, u64, f64, f64, f64, f64); 7] = [
        (
            1.0,
            1.0,
            4,
            2.0,
            0.95,
            0.5411621300394737,
            3.4138628918012324,
        ),
        (
            1.0,
            1.0,
            10,
            0.5,
            0.95,
            3.6607735781578925,
            12.260237361345185,
        ),
        (
            1.0,
            1.0,
            100,
            10.0,
            0.95,
            7.478741708458086,
            11.056981253856945,
        ),
        (
            2.5,
            3.0,
            40,
            12.25,
            0.9,
            2.1229310108432786,
            3.52530298264654,
        ),
        (
            1.0,
            1.0,
            1000,
            60.0,
            0.99,
            15.10464473271867,
            17.776604394498182,
        ),
        (
            0.5,
            0.001,
            5000,
            1.5,
            0.95,
            3239.7416783669537,
            3424.411738449448,
        ),
        (
            1.0,
            1.0,
            1000000,
            3.0,
            0.95,
            249510.495590078,
            250490.47798635805,
        ),
    ];

    fn relative_error(got: f64, want: f64) -> f64 {
        (got - want).abs() / want
    }

    /// The distance from exact the docs state, with a tenth of room, for
    /// the documented shape at or below `shape` and the documented
    /// confidence whose tail is at or below `tail`.
    fn documented_distance(shape: f64, tail: f64) -> f64 {
        let by_confidence = match shape {
            s if s >= 1_000_001.0 => [6.96e-12, 1.86e-11, 9.88e-11, 2.59e-10],
            s if s >= 100_001.0 => [1.65e-10, 5.44e-10, 3.05e-9, 8.36e-9],
            s if s >= 10_001.0 => [5.22e-9, 1.76e-8, 9.80e-8, 2.69e-7],
            s if s >= 1_001.0 => [1.82e-7, 6.08e-7, 3.28e-6, 9.03e-6],
            s if s >= 101.0 => [7.08e-6, 2.51e-5, 1.23e-4, 3.41e-4],
            s if s >= 31.0 => [4.87e-5, 2.01e-4, 9.09e-4, 2.54e-3],
            s if s >= 11.0 => [2.95e-4, 1.50e-3, 6.17e-3, 1.77e-2],
            s if s >= 5.0 => [2.45e-3, 8.22e-3, 3.17e-2, 9.40e-2],
            _ => [9.94e-3, 2.79e-2, 1.04e-1, 3.10e-1],
        };
        // 90%, 95%, 99%, 99.9%.
        let column = match tail {
            t if t >= 0.05 => 0,
            t if t >= 0.025 => 1,
            t if t >= 0.005 => 2,
            _ => 3,
        };
        by_confidence[column]
    }

    /// The estimate against the exact interval, within the distance the
    /// docs state for the shape and the confidence.
    #[test]
    fn the_interval_is_as_close_to_exact_as_documented() {
        for (alpha, beta, count, exposure, confidence, lower, upper) in INTERVALS {
            let mut gp = estimator::<f64>(alpha, beta);
            gp.update(count, exposure);
            let got = gp.credible_interval(Confidence::new(confidence));
            let limit = documented_distance(alpha + count as f64, (1.0 - confidence) / 2.0);
            assert!(
                relative_error(got.lower, lower) < limit
                    && relative_error(got.upper, upper) < limit,
                "({alpha}, {beta}) + ({count}, {exposure}) at {confidence}: {got:?}, limit {limit}"
            );
        }
    }

    /// With almost no data the lower end is rough, and it is zero where
    /// the closed form goes negative. It is never below zero or NaN.
    #[test]
    fn a_few_events_give_a_rough_but_ordered_interval() {
        // The prior alone, shape 1: the exact 95% interval is
        // (0.0253, 3.689).
        let gp = estimator::<f64>(1.0, 1.0);
        let got = gp.credible_interval(Confidence::new(0.95));
        assert!(got.lower > 0.0 && got.lower < 0.0253 && relative_error(got.upper, 3.689) < 0.01);
        // A very small shape: both ends are zero at 95%, where the exact
        // interval at a shape of 0.01 is (0, 0.0471).
        for alpha in [1e-300, 1e-9, 0.01] {
            let got = estimator::<f64>(alpha, 1.0).credible_interval(Confidence::new(0.95));
            assert_eq!((got.lower, got.upper), (0.0, 0.0), "{alpha}");
        }
        // A little larger: the upper end is back, the lower still zero.
        let got = estimator::<f64>(0.5, 1.0).credible_interval(Confidence::new(0.95));
        assert!(
            got.lower == 0.0 && got.upper > 1.0 && got.upper.is_finite(),
            "{got:?}"
        );
    }

    /// A confidence one rounding step from either end. Each end comes from
    /// its own tail, so the interval stays ordered and finite.
    #[test]
    fn the_ends_stay_in_order_at_every_confidence() {
        for (alpha, count) in [(1.0, 0), (0.5, 3), (2.0, 400), (1.0, 6_334)] {
            let mut gp = estimator::<f64>(alpha, 1.0);
            gp.update(count, 0.0);
            for confidence in [
                f64::from_bits(1),
                1e-300,
                1e-14,
                0.5,
                0.999_999,
                1.0 - f64::EPSILON / 2.0,
            ] {
                let got = gp.credible_interval(Confidence::new(confidence));
                assert!(
                    got.lower <= got.upper && got.lower >= 0.0 && got.upper.is_finite(),
                    "{alpha}+{count} at {confidence}: {got:?}"
                );
            }
        }
    }

    #[test]
    fn the_interval_widens_with_confidence() {
        let mut gp = estimator::<f64>(1.0, 1.0);
        gp.update(12, 4.0);
        let mut last = gp.credible_interval(Confidence::new(0.01));
        for confidence in [0.1, 0.5, 0.9, 0.99, 0.9999] {
            let next = gp.credible_interval(Confidence::new(confidence));
            assert!(
                next.lower < last.lower && next.upper > last.upper,
                "{confidence}"
            );
            last = next;
        }
    }

    #[test]
    fn checked_update_refuses_an_exposure_that_would_corrupt_the_estimate() {
        use nexus_stats_core::DataError::{Infinite, Negative, NotANumber};

        let mut gp = estimator::<f64>(1.0, 1.0);
        gp.update(4, 2.0);
        let before = (gp.rate(), gp.count(), gp.exposure());
        assert_eq!(gp.checked_update(1, f64::NAN), Err(NotANumber));
        assert_eq!(gp.checked_update(1, f64::INFINITY), Err(Infinite));
        assert_eq!(gp.checked_update(1, f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(gp.checked_update(1, -0.5), Err(Negative));
        assert_eq!((gp.rate(), gp.count(), gp.exposure()), before);
        // No exposure with events is fine, and so is exposure with none.
        assert_eq!(gp.checked_update(2, 0.0), Ok(()));
        assert_eq!(gp.checked_update(0, 3.0), Ok(()));
        assert_eq!((gp.count(), gp.exposure()), (6, 5.0));
    }

    #[test]
    fn checked_update_agrees_with_update() {
        let (mut plain, mut checked) = (estimator::<f64>(1.0, 1.0), estimator::<f64>(1.0, 1.0));
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        for _ in 0..2_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let (count, exposure) = (state % 40, (state >> 20) as f64 % 5.0);
            plain.update(count, exposure);
            assert_eq!(checked.checked_update(count, exposure), Ok(()));
        }
        assert_eq!(
            (plain.rate(), plain.variance()),
            (checked.rate(), checked.variance())
        );
    }

    #[test]
    fn reset_forgets_the_data_and_keeps_the_prior() {
        let mut gp = estimator::<f64>(2.0, 3.0);
        gp.update(50, 5.0);
        gp.reset();
        assert_eq!((gp.count(), gp.exposure(), gp.rate()), (0, 0.0, 2.0 / 3.0));
    }

    #[test]
    fn the_builder_checks_the_prior() {
        let build = |alpha: f64, beta: f64| {
            GammaPoisson::<f64>::builder()
                .alpha(alpha)
                .beta(beta)
                .build()
        };
        for (alpha, beta) in [
            (0.0, 1.0),
            (-1.0, 1.0),
            (1.0, 0.0),
            (1.0, -1.0),
            (f64::NAN, 1.0),
            (1.0, f64::NAN),
            (f64::INFINITY, 1.0),
            (1.0, f64::INFINITY),
        ] {
            assert!(build(alpha, beta).is_err(), "({alpha}, {beta})");
        }
        assert!(build(0.001, 1e9).is_ok());
        // The default prior is (1, 1).
        assert_eq!(GammaPoisson::<f64>::builder().build().unwrap().rate(), 1.0);
    }
}
