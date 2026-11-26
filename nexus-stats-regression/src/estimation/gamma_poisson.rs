use core::marker::PhantomData;

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
/// million of exact from a thousand events, in about ten nanoseconds,
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
    /// probability `confidence`: the posterior's quantiles at
    /// `(1 - confidence) / 2` from each end, by Wilson and Hilferty's
    /// closed form (1931). About ten nanoseconds.
    ///
    /// Every answer is a little off the exact one, by an amount that
    /// shrinks as the posterior's shape grows (the prior's `alpha` plus
    /// the events seen). This is how far the lower end is from the exact
    /// lower end, as a fraction of its value. It is a distance, not a rate
    /// of failure. The same inputs always give the same answer.
    ///
    /// | Shape | At 95% | At 99.9% |
    /// |---|---|---|
    /// | 3 | 2.5% | 28% |
    /// | 5 | 0.75% | 8.6% |
    /// | 11 | 0.14% | 1.6% |
    /// | 31 | 0.02% | 0.23% |
    /// | 101 | 0.0023% | 0.031% |
    /// | 1,001 | 6 in 10 million | 8 in a million |
    /// | 10,001 | 2 in 100 million | 2.5 in 10 million |
    /// | 1,000,001 | 2 in 100 billion | 2.4 in 10 billion |
    ///
    /// At these shapes the upper end is at least as close. With the
    /// default prior and 100 events over 10 seconds, the exact 95%
    /// interval is (7.47874, 11.05698) and this gives (7.47857, 11.05709).
    ///
    /// Below a shape of 3 the interval is poor. The lower end is zero
    /// where the closed form goes negative, which at 95% is a shape below
    /// about 0.63, and below about 0.02 both ends are zero. These are
    /// measurements against a 40-digit reference, not proven bounds.
    ///
    /// # Panics
    ///
    /// If `confidence` is not strictly between 0 and 1.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn credible_interval(&self, confidence: f64) -> CredibleInterval {
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
    /// `confidence`. Each end takes its own tail, so `1 - tail` is never
    /// formed.
    #[cfg(any(feature = "std", feature = "libm"))]
    fn interval(self, confidence: f64) -> CredibleInterval {
        use nexus_stats_core::math::probability::{
            gamma_quantile_approx, gamma_quantile_upper_approx,
        };
        assert!(
            confidence > 0.0 && confidence < 1.0,
            "confidence must be strictly between 0 and 1"
        );
        let tail = (1.0 - confidence) / 2.0;
        CredibleInterval {
            lower: gamma_quantile_approx(self.shape, tail) / self.rate,
            upper: gamma_quantile_upper_approx(self.shape, tail) / self.rate,
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

    /// The largest distance from exact the docs state for the lower end,
    /// by the posterior's shape, with about a tenth of room. `tail` picks
    /// the column: 95% for a tail of 0.025 or more, 99.9% below that.
    fn documented_error(shape: f64, tail: f64) -> f64 {
        let (at_95, at_999) = match shape {
            s if s >= 1_000_001.0 => (1.9e-11, 2.6e-10),
            s if s >= 100_001.0 => (5.2e-10, 8.0e-9),
            s if s >= 10_001.0 => (1.7e-8, 2.6e-7),
            s if s >= 1_001.0 => (5.8e-7, 8.6e-6),
            s if s >= 101.0 => (2.4e-5, 3.2e-4),
            s if s >= 31.0 => (1.9e-4, 2.4e-3),
            s if s >= 11.0 => (1.4e-3, 1.65e-2),
            s if s >= 5.0 => (7.6e-3, 8.8e-2),
            _ => (2.6e-2, 2.9e-1),
        };
        if tail >= 0.025 { at_95 } else { at_999 }
    }

    /// The estimate against the exact interval, within the distance the
    /// docs state for the shape. A confidence above 95% is held to the
    /// 99.9% column.
    #[test]
    fn the_interval_is_as_close_to_exact_as_documented() {
        for (alpha, beta, count, exposure, confidence, lower, upper) in INTERVALS {
            let mut gp = estimator::<f64>(alpha, beta);
            gp.update(count, exposure);
            let got = gp.credible_interval(confidence);
            let tail = if confidence > 0.95 { 0.0005 } else { 0.025 };
            let limit = documented_error(alpha + count as f64, tail);
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
        let got = gp.credible_interval(0.95);
        assert!(got.lower > 0.0 && got.lower < 0.0253 && relative_error(got.upper, 3.689) < 0.01);
        // A very small shape: both ends are zero at 95%, where the exact
        // interval at a shape of 0.01 is (0, 0.0471).
        for alpha in [1e-300, 1e-9, 0.01] {
            let got = estimator::<f64>(alpha, 1.0).credible_interval(0.95);
            assert_eq!((got.lower, got.upper), (0.0, 0.0), "{alpha}");
        }
        // A little larger: the upper end is back, the lower still zero.
        let got = estimator::<f64>(0.5, 1.0).credible_interval(0.95);
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
                let got = gp.credible_interval(confidence);
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
        let _ = estimator::<f64>(1.0, 1.0).credible_interval(f64::NAN);
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
