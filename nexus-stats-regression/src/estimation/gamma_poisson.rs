use core::marker::PhantomData;

use nexus_stats_core::{DataError, Span, Tick};

/// The rate of a Poisson process, learned from counts, with its
/// uncertainty.
///
/// Feed it how many events were seen over how much exposure. It keeps a
/// Gamma posterior over the rate, starting from a `Gamma(alpha, beta)`
/// prior: after `k` events over an exposure of `t` the posterior is
/// `Gamma(alpha + k, beta + t)`. The update is exact and costs two
/// additions. See
/// [conjugate prior](https://en.wikipedia.org/wiki/Conjugate_prior).
///
/// This type fits the rate. [`HawkesIntensity`](super::HawkesIntensity) is
/// the model for events that cluster, and it is told its parameters.
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
/// use nexus_stats_regression::estimation::GammaPoisson;
///
/// // Events per second, on nanosecond time.
/// let mut arrivals = GammaPoisson::<i64>::builder().build().unwrap();
/// arrivals.update(100, Duration::from_secs(10));
/// // The prior (1, 1) counts as one event over one second.
/// assert_eq!(arrivals.rate(), 101.0 / 11.0);
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
    /// The count is a `u64` and adds as `+` does. An exposure that is not
    /// a number, or is below zero, corrupts the estimate from here on. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, count: u64, exposure: T::Span) {
        self.events += count;
        self.exposure += exposure.as_f64();
    }

    /// Checked update. Records `count` events over `exposure`, or returns
    /// an error and leaves the estimate unchanged.
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

    /// The equal-tailed interval that holds the rate with probability
    /// `confidence`: the posterior's quantiles at `(1 - confidence) / 2`
    /// from each end.
    ///
    /// This is `scipy.stats.gamma.interval`, to ten digits while the
    /// posterior's shape (the prior's `alpha` plus the events seen) is at
    /// most 10,000 and to one part in a million above that. It runs a
    /// short iteration and costs from a few hundred nanoseconds to a few
    /// microseconds, more as the events grow.
    /// [`approx_credible_interval`](Self::approx_credible_interval) is the
    /// fast form.
    ///
    /// # Panics
    ///
    /// If `confidence` is not strictly between 0 and 1.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn credible_interval(&self, confidence: f64) -> CredibleInterval {
        self.posterior().interval(
            confidence,
            nexus_stats_core::math::probability::gamma_quantile,
        )
    }

    /// The same interval by Wilson and Hilferty's closed form (1931), in
    /// about ten nanoseconds.
    ///
    /// Against [`credible_interval`](Self::credible_interval) at 95% it is
    /// within 3% once the shape reaches 5, within 0.6% from 11 and within
    /// 0.02% from 100. Below a shape of 5 the lower end is poor, and it is
    /// zero where the closed form goes negative. Use it to compute an
    /// interval per event, and the exact one to report.
    ///
    /// # Panics
    ///
    /// If `confidence` is not strictly between 0 and 1.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn approx_credible_interval(&self, confidence: f64) -> CredibleInterval {
        self.posterior().interval(
            confidence,
            nexus_stats_core::math::probability::gamma_quantile_approx,
        )
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

    /// The equal-tailed interval at `confidence`, given the quantile of a
    /// `Gamma(shape, 1)`.
    #[cfg(any(feature = "std", feature = "libm"))]
    fn interval(self, confidence: f64, unit_quantile: fn(f64, f64) -> f64) -> CredibleInterval {
        assert!(
            confidence > 0.0 && confidence < 1.0,
            "confidence must be strictly between 0 and 1"
        );
        let tail = (1.0 - confidence) / 2.0;
        CredibleInterval {
            lower: unit_quantile(self.shape, tail) / self.rate,
            upper: unit_quantile(self.shape, 1.0 - tail) / self.rate,
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
        let (early, early_width) = (gp.variance(), gp.credible_interval(0.95).width());
        gp.update(1_000, 100.0);
        assert!(gp.variance() < early);
        let interval = gp.credible_interval(0.95);
        assert!(interval.width() < early_width);
        assert!(interval.lower < gp.rate() && gp.rate() < interval.upper);
    }

    // Reference values from SciPy 1.18.1:
    // `scipy.stats.gamma.interval(confidence, alpha + k, scale=1/(beta + t))`
    // for `(alpha, beta, k, t, confidence, lower, upper)`.
    const INTERVALS: [(f64, f64, u64, f64, f64, f64, f64); 8] = [
        (
            1.0,
            1.0,
            0,
            0.0,
            0.95,
            0.025317807984289897,
            3.6888794541139354,
        ),
        (
            1.0,
            1.0,
            1,
            2.0,
            0.95,
            0.08073642618132168,
            1.8572144636462993,
        ),
        (1.0, 1.0, 3, 0.5, 0.9, 0.9108789311665537, 5.16910435195515),
        (
            1.0,
            1.0,
            100,
            10.0,
            0.95,
            7.478741708458085,
            11.056981253856945,
        ),
        (
            0.5,
            0.001,
            7,
            1.5,
            0.99,
            1.5326167793895207,
            10.92648922244898,
        ),
        (
            2.5,
            3.0,
            40,
            12.25,
            0.5,
            2.4878926936015375,
            3.0620966956212525,
        ),
        (
            1.0,
            1.0,
            5000,
            60.0,
            0.999,
            78.22249447358747,
            85.85212040513247,
        ),
        (
            1.0,
            1.0,
            20000,
            3.0,
            0.95,
            4931.190167786081,
            5069.783406981602,
        ),
    ];

    fn relative_error(got: f64, want: f64) -> f64 {
        (got - want).abs() / want
    }

    #[test]
    fn the_credible_interval_matches_scipy() {
        for (alpha, beta, count, exposure, confidence, lower, upper) in INTERVALS {
            let mut gp = estimator::<f64>(alpha, beta);
            gp.update(count, exposure);
            let got = gp.credible_interval(confidence);
            // Ten digits up to a shape of 10,000, six above.
            let limit = if alpha + count as f64 <= 10_000.0 {
                1e-10
            } else {
                1e-6
            };
            assert!(
                relative_error(got.lower, lower) < limit
                    && relative_error(got.upper, upper) < limit,
                "({alpha}, {beta}) + ({count}, {exposure}) at {confidence}: {got:?}"
            );
        }
    }

    /// The interval is defined from the prior alone, before any data.
    #[test]
    fn the_prior_alone_has_an_interval() {
        let gp = estimator::<f64>(1.0, 1.0);
        let interval = gp.credible_interval(0.95);
        assert!(relative_error(interval.lower, 0.025317807984289897) < 1e-10);
        assert!(relative_error(interval.upper, 3.6888794541139354) < 1e-10);
    }

    /// The accuracy the fast form's documentation states, at 95%.
    #[test]
    fn the_fast_interval_is_as_accurate_as_documented() {
        for (count, limit) in [(4, 0.03), (10, 0.006), (99, 2e-4), (5_000, 2e-6)] {
            let mut gp = estimator::<f64>(1.0, 1.0);
            gp.update(count, 7.0);
            let (exact, fast) = (
                gp.credible_interval(0.95),
                gp.approx_credible_interval(0.95),
            );
            assert!(
                relative_error(fast.lower, exact.lower) < limit
                    && relative_error(fast.upper, exact.upper) < limit,
                "{count} events: {fast:?} vs {exact:?}"
            );
        }
        // Poor with almost no data, and never below zero.
        let gp = estimator::<f64>(0.05, 1.0);
        let fast = gp.approx_credible_interval(0.999);
        assert_eq!(fast.lower, 0.0);
        assert!(fast.upper > 0.0);
    }

    #[test]
    fn the_interval_widens_with_confidence() {
        let mut gp = estimator::<f64>(1.0, 1.0);
        gp.update(12, 4.0);
        let mut last = gp.credible_interval(0.01);
        for confidence in [0.1, 0.5, 0.9, 0.99, 0.9999] {
            let next = gp.credible_interval(confidence);
            assert!(
                next.lower < last.lower && next.upper > last.upper,
                "{confidence}"
            );
            last = next;
        }
    }

    #[test]
    #[should_panic(expected = "confidence must be strictly between 0 and 1")]
    fn a_confidence_of_one_is_refused() {
        let _ = estimator::<f64>(1.0, 1.0).credible_interval(1.0);
    }

    #[test]
    #[should_panic(expected = "confidence must be strictly between 0 and 1")]
    fn a_confidence_that_is_not_a_number_is_refused() {
        let _ = estimator::<f64>(1.0, 1.0).approx_credible_interval(f64::NAN);
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
