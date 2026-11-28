use core::marker::PhantomData;

#[cfg(any(feature = "std", feature = "libm"))]
use nexus_stats_core::Confidence;
use nexus_stats_core::math::{MulAdd, step_mean};
use nexus_stats_core::{DataError, Span, Tick};

#[cfg(any(feature = "std", feature = "libm"))]
use super::{ConfidenceInterval, CredibleInterval, PredictionInterval};

/// The rate of a Poisson process, learned from counts, with its
/// uncertainty.
///
/// Feed it how many events were seen over how much exposure. It keeps a
/// Gamma posterior over the rate, starting from a `Gamma(alpha, beta)`
/// prior: after `k` events over an exposure of `t` the posterior is
/// `Gamma(alpha + k, beta + t)`. The update is two additions. See
/// [conjugate prior](https://en.wikipedia.org/wiki/Conjugate_prior).
///
/// This type does the fitting and nothing else. [`summary`](Self::summary)
/// has everything about the fit: the rate, how far off it may be, and how
/// well a Poisson process describes the data. And [`model`](Self::model) gives the fitted
/// [`PoissonModel`], which says what to expect next. A rate known already
/// needs no fitting: build a [`PoissonModel`] from it.
/// [`HawkesModel`](super::HawkesModel) is the model for events
/// that cluster.
///
/// # The interval is an estimate
///
/// [`credible_interval`](PoissonSummary::credible_interval) is Wilson and Hilferty's
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
/// with your prior's `alpha` and `beta`, and `k` and `t` from the
/// [`summary`](Self::summary)'s `events` and `exposure`. To start this
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
/// use nexus_stats_regression::estimation::PoissonEstimator;
///
/// // Checked when this is compiled.
/// const NINETY_FIVE: Confidence = Confidence::new(0.95);
///
/// // Events per second, on nanosecond time.
/// let mut arrivals = PoissonEstimator::<i64>::builder().build().unwrap();
/// arrivals.update(100, Duration::from_secs(10));
/// // The prior (1, 1) counts as one event over one second.
/// let summary = arrivals.summary();
/// assert_eq!(summary.rate(), 101.0 / 11.0);
/// let interval = summary.credible_interval(NINETY_FIVE).unwrap();
/// assert!(interval.contains(summary.rate()));
///
/// // What to expect over the next five seconds.
/// let expected = arrivals.model().expected(Duration::from_secs(5));
/// assert!((expected - 505.0 / 11.0).abs() < 1e-12);
/// ```
#[derive(Debug, Clone)]
pub struct PoissonEstimator<T: Tick> {
    prior: Gamma,
    /// Events seen, apart from the prior.
    events: u64,
    /// Exposure seen, apart from the prior, in units of the clock.
    exposure: f64,
    scatter: Scatter,
    clock: PhantomData<T>,
}

/// Builder for [`PoissonEstimator`].
#[derive(Debug, Clone)]
pub struct PoissonEstimatorBuilder<T: Tick> {
    alpha: f64,
    beta: f64,
    clock: PhantomData<T>,
}

impl<T: Tick> PoissonEstimator<T> {
    /// Creates a builder. The prior defaults to `Gamma(1, 1)`, which
    /// counts as one event over one unit of exposure.
    #[inline]
    #[must_use]
    pub fn builder() -> PoissonEstimatorBuilder<T> {
        PoissonEstimatorBuilder {
            alpha: 1.0,
            beta: 1.0,
            clock: PhantomData,
        }
    }

    /// Records `count` events over `exposure`.
    ///
    /// The count is a `u64` and adds as `+` does, so past `u64::MAX` it
    /// panics in a debug build and wraps in a release one. An exposure
    /// that is not a number, or is below zero, corrupts the estimate from
    /// here on.
    ///
    /// An exposure of zero leaves the rate sound and spoils the test of
    /// the fit: the [`summary`](Self::summary)'s chi-square, dispersion
    /// and p-value are NaN from then until `reset`. A Poisson process has
    /// no two events at one instant, so events over no exposure have no
    /// place in it. SciPy's `chisquare` gives infinity or NaN for the
    /// same data. See [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, count: u64, exposure: T::Span) {
        let exposure = exposure.as_f64();
        self.events += count;
        self.exposure += exposure;
        self.scatter.record(count, exposure);
    }

    /// Checked update. Records `count` events over `exposure`, or returns
    /// an error and leaves the estimate unchanged.
    ///
    /// It refuses an exposure that is not a usable span (NaN, infinite,
    /// negative, zero, or outside the range a float can divide by and
    /// square) and a count that would overflow the total. A `Duration` or
    /// a counter is never NaN, infinite or negative, so on those clocks
    /// only an exposure of zero is refused.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`] if the exposure is NaN.
    /// - [`DataError::Infinite`] if it is infinite.
    /// - [`DataError::Negative`] if it is below zero.
    /// - [`DataError::OutOfRange`] if it is zero, or too small to divide
    ///   by (below `f64::MIN_POSITIVE / f64::EPSILON`, about `1e-292`,
    ///   the form of LAPACK's safe minimum). statsmodels' `confint_poisson`
    ///   refuses an exposure that is not positive in the same way.
    /// - [`DataError::OutOfRange`] if the exposure, or `count` over it, is
    ///   above `1e80`. The test of the fit multiplies an exposure by the
    ///   square of a rate, and beyond this the product no longer fits.
    /// - [`DataError::OutOfRange`] if `count` would take the events past
    ///   `u64::MAX`.
    #[inline]
    pub fn checked_update(&mut self, count: u64, exposure: T::Span) -> Result<(), DataError> {
        check_observation(count, exposure.as_f64())?;
        if self.events.checked_add(count).is_none() {
            return Err(DataError::OutOfRange);
        }
        self.update(count, exposure);
        Ok(())
    }

    /// The fitted model, at the posterior mean of the rate. Ask it what
    /// to expect over a future exposure.
    ///
    /// It carries the rate only. What uncertainty is left in the rate is
    /// in the [`summary`](Self::summary).
    #[inline]
    #[must_use]
    pub fn model(&self) -> PoissonModel<T> {
        PoissonModel {
            rate: self.posterior().mean(),
            clock: PhantomData,
        }
    }

    /// How good the fit is: the rate, how far off it may be, and whether
    /// the data looks like a Poisson process at all. Changes nothing.
    #[inline]
    #[must_use]
    pub fn summary(&self) -> PoissonSummary {
        PoissonSummary {
            posterior: self.posterior(),
            events: self.events,
            exposure: self.exposure,
            scatter: self.scatter,
        }
    }

    /// Forgets every observation. The prior is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.events = 0;
        self.exposure = 0.0;
        self.scatter = Scatter::default();
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

impl<T: Tick> PoissonEstimatorBuilder<T> {
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
    pub fn build(self) -> Result<PoissonEstimator<T>, nexus_stats_core::ConfigError> {
        use nexus_stats_core::ConfigError::Invalid;
        use nexus_stats_core::math::positive_finite;

        if !positive_finite(self.alpha) {
            return Err(Invalid(
                "PoissonEstimator alpha must be positive and finite",
            ));
        }
        if !positive_finite(self.beta) {
            return Err(Invalid("PoissonEstimator beta must be positive and finite"));
        }
        Ok(PoissonEstimator {
            prior: Gamma {
                shape: self.alpha,
                rate: self.beta,
            },
            events: 0,
            exposure: 0.0,
            scatter: Scatter::default(),
            clock: PhantomData,
        })
    }
}

/// A gamma distribution, by shape and rate.
#[derive(Debug, Clone, Copy, PartialEq)]
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
    /// `confidence`, where there is enough evidence for one.
    #[cfg(any(feature = "std", feature = "libm"))]
    fn interval(self, confidence: Confidence) -> Option<CredibleInterval> {
        if self.shape < 0.5 {
            return None;
        }
        let (lower, upper) =
            crate::probability::gamma_interval_approx(self.shape, confidence.tail());
        Some(CredibleInterval::new(lower / self.rate, upper / self.rate))
    }
}

/// What the chi-square of the fit needs, kept as the data arrives: the
/// running mean of each observation's rate, weighted by its exposure, and
/// the weighted sum of squared distances from it. This is West's weighted
/// form of Welford's algorithm, which never subtracts two large totals.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
struct Scatter {
    observations: u64,
    exposure: f64,
    /// The mean of `count / exposure`, weighted by exposure: the rate from
    /// the data alone.
    rate: f64,
    /// The sum of `exposure (rate_i - rate)^2`.
    squares: f64,
}

impl Scatter {
    #[inline]
    fn record(&mut self, count: u64, exposure: f64) {
        self.observations += 1;
        self.exposure += exposure;
        let step = step_mean(
            &mut self.rate,
            count as f64 / exposure,
            exposure / self.exposure,
        );
        self.squares = (exposure * step.before).fma(step.after, self.squares);
    }

    /// The sum of `(count - expected)^2 / expected` over the observations,
    /// with `expected` from `rate`, the data's own: events over exposure.
    ///
    /// The running mean is that rate too, but it can round to zero when
    /// one exposure dwarfs the rest, so the totals give the divisor.
    #[inline]
    fn chi_square(self, rate: f64) -> f64 {
        self.squares / rate
    }
}

/// How good a [`PoissonEstimator`]'s fit is, from its
/// [`summary`](PoissonEstimator::summary).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PoissonSummary {
    posterior: Gamma,
    events: u64,
    exposure: f64,
    scatter: Scatter,
}

impl PoissonSummary {
    /// The estimate: the posterior mean of the rate, in events per unit
    /// of the clock.
    #[inline]
    #[must_use]
    pub fn rate(&self) -> f64 {
        self.posterior.mean()
    }

    /// The posterior variance of the rate.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> f64 {
        self.posterior.variance()
    }

    /// An estimate of the equal-tailed interval that holds the rate with
    /// the given confidence: the posterior's quantiles at
    /// [`confidence.tail()`](Confidence::tail) from each end, by Wilson and
    /// Hilferty's closed form (1931). About 20 cycles, under ten nanoseconds.
    ///
    /// The level was checked when the [`Confidence`] was made, so nothing
    /// about it is checked here.
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
    /// The table is the whole story for a stream: the distance is a few
    /// percent with a handful of events and falls to parts in a million by
    /// a thousand.
    ///
    /// The worst case is the start, with few or no events. Below a shape
    /// of 3 the interval is rough. The lower end is zero where the closed
    /// form goes negative, which at 95% is a shape below about 0.63. At a
    /// shape of one half, which is a Jeffreys prior before any event, the
    /// upper end is 2% from exact, and that is as far off as it gets where
    /// an interval is given at all. These are measurements against a
    /// 40-digit reference, not proven bounds.
    ///
    /// `None` while the shape is below one half: less than half an event
    /// of evidence, prior included, where the closed form falls apart.
    /// The default prior always has an interval, and so does the Jeffreys
    /// prior, an `alpha` of one half.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn credible_interval(&self, confidence: Confidence) -> Option<CredibleInterval> {
        self.posterior.interval(confidence)
    }

    /// An estimate of the classical interval for the rate, from the data
    /// alone with no prior: Garwood's interval, by the closed form
    /// [`credible_interval`](Self::credible_interval) uses. `None` before
    /// any exposure.
    ///
    /// With `k` events over an exposure of `t`, the lower end is the
    /// quantile of a `Gamma(k)` and the upper end that of a `Gamma(k + 1)`,
    /// each over `t`. With no events the lower end is zero. The distance
    /// from exact is the table on `credible_interval`, read at a shape of
    /// `k` for the lower end and `k + 1` for the upper. For the exact value, offline: `scipy.stats.gamma.ppf(tail, k) / t`
    /// and `scipy.stats.gamma.isf(tail, k + 1) / t`.
    ///
    /// It differs from the credible interval by the prior. With the
    /// default prior and many events the two are nearly the same. With a
    /// strong prior this one says what the data alone supports.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn confidence_interval(&self, confidence: Confidence) -> Option<ConfidenceInterval> {
        // Only "nothing seen yet" is `None`. A corrupt total reads as NaN.
        if self.exposure == 0.0 {
            return None;
        }
        let events = self.events as f64;
        // With no events the lower end is known outright.
        let (lower, upper) = crate::probability::gamma_interval_between(
            events.max(1.0),
            events + 1.0,
            confidence.tail(),
        );
        let lower = if self.events == 0 { 0.0 } else { lower };
        Some(ConfidenceInterval::new(
            lower / self.exposure,
            upper / self.exposure,
        ))
    }

    /// How far off the rate may be: the square root of the variance. Over
    /// the rate it is `1 / sqrt(alpha + events)`, so a hundred events pin
    /// the rate to about 10% and ten thousand to about 1%.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn standard_error(&self) -> f64 {
        nexus_stats_core::math::sqrt(self.variance())
    }

    /// Events recorded, apart from the prior.
    #[inline]
    #[must_use]
    pub fn events(&self) -> u64 {
        self.events
    }

    /// Exposure recorded, apart from the prior, in units of the clock.
    #[inline]
    #[must_use]
    pub fn exposure(&self) -> f64 {
        self.exposure
    }

    /// Calls to `update`. Each is one observation of the process.
    #[inline]
    #[must_use]
    pub fn observations(&self) -> u64 {
        self.scatter.observations
    }

    /// The chi-square statistic of the fit: how far the counts are from
    /// what the rate expects of each observation, squared and scaled.
    /// `None` until there are two observations and one event. Report it
    /// with [`degrees_of_freedom`](Self::degrees_of_freedom).
    #[inline]
    #[must_use]
    pub fn chi_square(&self) -> Option<f64> {
        self.degrees_of_freedom()?;
        Some(self.scatter.chi_square(self.events as f64 / self.exposure))
    }

    /// The degrees of freedom of [`chi_square`](Self::chi_square): one
    /// less than the observations. `None` until there are two observations
    /// and one event.
    #[inline]
    #[must_use]
    pub fn degrees_of_freedom(&self) -> Option<u64> {
        if self.scatter.observations < 2 || self.events == 0 {
            return None;
        }
        Some(self.scatter.observations - 1)
    }

    /// How much the counts scatter, over how much a Poisson process
    /// would: the chi-square of the fit over its degrees of freedom.
    /// `None` until there are two observations and one event.
    ///
    /// ```text
    /// expected_i = exposure_i events / exposure
    /// chi_square = sum of (count_i - expected_i)^2 / expected_i
    /// dispersion = chi_square / (observations - 1)
    /// ```
    ///
    /// About 1 for a Poisson process. Well above 1 means the events come
    /// in clusters, which a single rate does not describe. Well below 1
    /// means they come more evenly than chance.
    ///
    /// It reads the scatter between observations, so it needs
    /// observations that each expect several events. Five is the usual
    /// rule. Fed one event at a time it says nothing.
    ///
    /// It also needs their exposures within about fifteen orders of
    /// magnitude of each other. Past that, the shorter ones fall below
    /// what a float can hold beside the longer and no longer count. The
    /// rate is not affected.
    #[inline]
    #[must_use]
    pub fn dispersion(&self) -> Option<f64> {
        let degrees = self.degrees_of_freedom()?;
        Some(self.chi_square()? / degrees as f64)
    }

    /// An estimate of the probability that a Poisson process would scatter
    /// at least this much. Small means the data is not Poisson. `None`
    /// where [`dispersion`](Self::dispersion) is.
    ///
    /// The hypothesis under test is that the data is Poisson. So a small
    /// value counts against the model, the other way round from the
    /// p-value of a regression coefficient, where the hypothesis is "no
    /// effect" and a small value is the result hoped for.
    ///
    /// Reading it: below 0.05 is the usual line for "not Poisson", and a
    /// value near 1 means the counts are more even than chance. With very
    /// many observations it turns small for a departure too slight to
    /// matter, so read the [`dispersion`](Self::dispersion) beside it: 1.02
    /// is a trivial departure and 3 is a serious one.
    ///
    /// It is the upper tail of a chi-square at the fit's statistic, with
    /// `observations - 1` degrees of freedom, by Wilson and Hilferty's
    /// closed form. From five observations it is within 2% of exact down
    /// to 0.05 and within 12% at 0.001. Below about one in a million it
    /// says only "very small". For the exact value, offline:
    /// `scipy.stats.chisquare(counts, exposures * counts.sum() / exposures.sum())`.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn p_value(&self) -> Option<f64> {
        let degrees = self.degrees_of_freedom()?;
        Some(crate::probability::chi_square_upper_tail_approx(
            self.chi_square()?,
            degrees as f64,
        ))
    }
}

/// A Poisson process with a known rate: what to expect from it.
///
/// Events arrive independently at a steady rate. Give it the rate, known
/// already or fitted by a [`PoissonEstimator`], and it says how many
/// events to expect over an exposure.
///
/// The clock is the caller's, any [`Tick`], and the rate is in events per
/// unit of it: per second on physical time.
///
/// # Examples
///
/// ```
/// use core::time::Duration;
/// use nexus_stats_regression::estimation::PoissonModel;
///
/// // 9.2 events per second, on nanosecond time.
/// let arrivals = PoissonModel::<i64>::new(9.2).unwrap();
/// assert_eq!(arrivals.expected(Duration::from_secs(10)), 92.0);
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PoissonModel<T: Tick> {
    rate: f64,
    clock: PhantomData<T>,
}

impl<T: Tick> PoissonModel<T> {
    /// A model with the given rate, in events per unit of the clock.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `rate` is below zero or not finite. A
    /// rate of zero is a process with no events, as in SciPy's `poisson`.
    #[inline]
    pub fn new(rate: f64) -> Result<Self, nexus_stats_core::ConfigError> {
        if !nexus_stats_core::math::nonnegative_finite(rate) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "PoissonModel rate must be finite and not below zero",
            ));
        }
        Ok(Self {
            rate,
            clock: PhantomData,
        })
    }

    /// The rate, in events per unit of the clock.
    #[inline]
    #[must_use]
    pub fn rate(&self) -> f64 {
        self.rate
    }

    /// The count expected over `exposure`: the rate times the exposure.
    /// It is also the variance of that count.
    #[inline]
    #[must_use]
    pub fn expected(&self, exposure: T::Span) -> f64 {
        self.rate * exposure.as_f64()
    }

    /// An estimate of the equal-tailed interval that holds the count over
    /// `exposure` with the given confidence, by Wilson and Hilferty's
    /// closed form at the expected count `m`:
    ///
    /// ```text
    /// v     = 1 / (9 m)
    /// lower = m (1 - v - z sqrt(v))^3
    /// upper = m (1 - v + z sqrt(v))^3
    /// ```
    ///
    /// A count is a whole number and the ends here are not. For expected
    /// counts from 10 to 3,000,000 an end is within one count of the
    /// exact end at 95% and within two and a half at 99.9% (SciPy's
    /// `poisson.ppf` and `poisson.isf`). Below an expected count of 10
    /// it is rough. Both ends are zero where nothing is expected, and NaN
    /// where the expected count is NaN or below zero.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn interval(&self, exposure: T::Span, confidence: Confidence) -> PredictionInterval {
        let (lower, upper) = crate::probability::count_interval_approx(
            self.expected(exposure),
            1.0,
            confidence.tail(),
        );
        PredictionInterval::new(lower, upper)
    }
}

/// The largest exposure, and the largest rate of one observation, that
/// `checked_update` takes: `1e80`.
///
/// The test of the fit sums an exposure times the square of a rate. With
/// each factor within this, a term stays within core's `POWER_LIMIT`, the
/// most a sum of `2^64` such terms can hold.
const LIMIT_FOR_SCATTER: f64 = 1e80;
const _: () = assert!(
    LIMIT_FOR_SCATTER * LIMIT_FOR_SCATTER * LIMIT_FOR_SCATTER
        <= nexus_stats_core::math::POWER_LIMIT
);

/// `Ok` if `exposure`, and the rate of `count` events over it, are within
/// what the estimate and the test of the fit can hold.
#[inline]
fn check_observation(count: u64, exposure: f64) -> Result<(), DataError> {
    use nexus_stats_core::math::check_input;

    check_exposure(exposure)?;
    check_input(exposure, LIMIT_FOR_SCATTER)?;
    check_input(count as f64 / exposure, LIMIT_FOR_SCATTER)
}

/// `Ok` if `exposure` is a number, finite, and large enough to divide by.
#[inline]
fn check_exposure(exposure: f64) -> Result<(), DataError> {
    // PERF: cold, so naming the reason stays off the accepted path.
    #[cold]
    fn refusal(exposure: f64) -> DataError {
        if exposure.is_nan() {
            DataError::NotANumber
        } else if exposure.is_infinite() {
            DataError::Infinite
        } else if exposure < 0.0 {
            DataError::Negative
        } else {
            DataError::OutOfRange
        }
    }

    if exposure.is_finite() && exposure >= nexus_stats_core::math::SMALLEST_DIVISOR {
        return Ok(());
    }
    Err(refusal(exposure))
}

// The tests read intervals and p-values, which need a square root.
#[cfg(all(test, any(feature = "std", feature = "libm")))]
#[allow(clippy::unreadable_literal, clippy::excessive_precision)]
mod tests {
    extern crate std;
    use super::*;
    use core::time::Duration;

    fn estimator<T: Tick>(alpha: f64, beta: f64) -> PoissonEstimator<T> {
        PoissonEstimator::builder()
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
        assert_eq!((gp.summary().rate(), gp.summary().variance()), (1.0, 1.0));
        gp.update(100, 10.0);
        assert_eq!(gp.summary().rate(), 101.0 / 11.0);
        assert_eq!(gp.summary().variance(), 101.0 / 121.0);
        gp.update(20, 2.0);
        gp.update(0, 3.0);
        assert_eq!(
            (gp.summary().events(), gp.summary().exposure()),
            (120, 15.0)
        );
        assert_eq!(gp.summary().rate(), 121.0 / 16.0);
    }

    #[test]
    fn the_prior_is_the_estimate_before_any_data() {
        let gp = estimator::<f64>(2.5, 10.0);
        assert_eq!(
            (
                gp.summary().rate(),
                gp.summary().events(),
                gp.summary().exposure()
            ),
            (0.25, 0, 0.0)
        );
    }

    /// On physical time the exposure is a `Duration` and the rate is per
    /// second, whatever unit the times are in.
    #[test]
    fn on_physical_time_the_rate_is_per_second() {
        use nexus_stats_core::{Micros, Tick as _};

        let mut on_nanos = estimator::<i64>(1.0, 1.0);
        on_nanos.update(50, Duration::from_millis(2_500));
        assert_eq!(on_nanos.summary().rate(), 51.0 / 3.5);

        // The exposure from two times.
        let mut on_micros = estimator::<Micros>(1.0, 1.0);
        on_micros.update(50, Micros(4_000_000).since(Micros(1_500_000)));
        assert_eq!(on_micros.summary().rate(), on_nanos.summary().rate());

        let mut on_instant = estimator::<std::time::Instant>(1.0, 1.0);
        on_instant.update(50, Duration::from_millis(2_500));
        assert_eq!(on_instant.summary().rate(), on_nanos.summary().rate());
    }

    /// On another clock the rate is per unit of that clock.
    #[test]
    fn on_a_counter_or_a_volume_clock_the_rate_is_per_unit() {
        let mut per_trade = estimator::<u64>(1.0, 1.0);
        per_trade.update(30, 999);
        assert_eq!(per_trade.summary().rate(), 31.0 / 1_000.0);

        let mut per_lot = estimator::<f64>(1.0, 1.0);
        per_lot.update(30, 999.0);
        assert_eq!(per_lot.summary().rate(), per_trade.summary().rate());
    }

    /// The count is kept as an integer, so it is exact with any prior.
    #[test]
    fn the_count_is_exact_with_a_fractional_prior() {
        let mut gp = estimator::<f64>(0.1, 0.3);
        gp.update(3, 0.2);
        gp.update((1 << 53) + 1, 1.0);
        assert_eq!(gp.summary().events(), (1 << 53) + 4);
        assert_eq!(gp.summary().exposure(), 1.2);
    }

    #[test]
    fn more_data_narrows_the_estimate() {
        let mut gp = estimator::<f64>(1.0, 1.0);
        gp.update(10, 1.0);
        let (early, early_width) = (
            gp.summary().variance(),
            gp.summary()
                .credible_interval(Confidence::new(0.95))
                .unwrap()
                .width(),
        );
        gp.update(1_000, 100.0);
        assert!(gp.summary().variance() < early);
        let interval = gp
            .summary()
            .credible_interval(Confidence::new(0.95))
            .unwrap();
        assert!(interval.width() < early_width);
        assert!(interval.lower() < gp.summary().rate() && gp.summary().rate() < interval.upper());
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
            let got = gp
                .summary()
                .credible_interval(Confidence::new(confidence))
                .unwrap();
            let limit = documented_distance(alpha + count as f64, (1.0 - confidence) / 2.0);
            assert!(
                relative_error(got.lower(), lower) < limit
                    && relative_error(got.upper(), upper) < limit,
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
        let got = gp
            .summary()
            .credible_interval(Confidence::new(0.95))
            .unwrap();
        assert!(
            got.lower() > 0.0 && got.lower() < 0.0253 && relative_error(got.upper(), 3.689) < 0.01
        );
        // Less than half an event of evidence: no interval.
        for alpha in [1e-300, 1e-9, 0.01, 0.49] {
            let summary = estimator::<f64>(alpha, 1.0).summary();
            assert_eq!(
                summary.credible_interval(Confidence::new(0.95)),
                None,
                "{alpha}"
            );
        }
        // The Jeffreys prior with no events is the worst case that still
        // has an interval: the lower end zero, and the upper within 2% of
        // the exact one, SciPy 1.18.1's `gamma.isf(0.025, 0.5)`.
        let got = estimator::<f64>(0.5, 1.0)
            .summary()
            .credible_interval(Confidence::new(0.95))
            .unwrap();
        assert!(
            got.lower() == 0.0 && relative_error(got.upper(), 2.511943093657445) < 0.02,
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
                let got = gp
                    .summary()
                    .credible_interval(Confidence::new(confidence))
                    .unwrap();
                assert!(
                    got.lower() <= got.upper() && got.lower() >= 0.0 && got.upper().is_finite(),
                    "{alpha}+{count} at {confidence}: {got:?}"
                );
            }
        }
    }

    #[test]
    fn the_interval_widens_with_confidence() {
        let mut gp = estimator::<f64>(1.0, 1.0);
        gp.update(12, 4.0);
        let mut last = gp
            .summary()
            .credible_interval(Confidence::new(0.01))
            .unwrap();
        for confidence in [0.1, 0.5, 0.9, 0.99, 0.9999] {
            let next = gp
                .summary()
                .credible_interval(Confidence::new(confidence))
                .unwrap();
            assert!(
                next.lower() < last.lower() && next.upper() > last.upper(),
                "{confidence}"
            );
            last = next;
        }
    }

    #[test]
    fn checked_update_refuses_an_exposure_that_would_corrupt_the_estimate() {
        use DataError::{Infinite, Negative, NotANumber, OutOfRange};

        let mut gp = estimator::<f64>(1.0, 1.0);
        gp.update(4, 2.0);
        gp.update(9, 3.0);
        let before = gp.summary();
        for (count, exposure, refusal) in [
            (1, f64::NAN, NotANumber),
            (1, f64::INFINITY, Infinite),
            (1, f64::NEG_INFINITY, Infinite),
            (1, -0.5, Negative),
            // No exposure, with events or without.
            (2, 0.0, OutOfRange),
            (0, 0.0, OutOfRange),
            (0, -0.0, OutOfRange),
            // Too small to divide by.
            (10, 1e-310, OutOfRange),
            (10, f64::MIN_POSITIVE, OutOfRange),
            // Too large for the test of the fit: the exposure, then the rate.
            (1, 1e81, OutOfRange),
            (1_000_000_000, 1e-72, OutOfRange),
        ] {
            assert_eq!(
                gp.checked_update(count, exposure),
                Err(refusal),
                "({count}, {exposure})"
            );
            assert_eq!(gp.summary(), before, "({count}, {exposure})");
        }
        // Exposure with no events is an observation like any other.
        assert_eq!(gp.checked_update(0, 3.0), Ok(()));
        assert_eq!((gp.summary().events(), gp.summary().exposure()), (13, 8.0));
        assert_eq!(gp.summary().observations(), 3);
    }

    /// At the edges of what `checked_update` takes, the readings are
    /// still numbers.
    #[test]
    fn checked_update_takes_the_edges_of_its_range() {
        let confidence = Confidence::new(0.95);
        let mut gp = estimator::<f64>(1.0, 1.0);
        for (count, exposure) in [
            (5, 1.0),
            (1, 1e-79),
            (u64::MAX / 4, 1e-61),
            (0, 1e80),
            (0, 1e80),
            (7, 2.0),
        ] {
            assert_eq!(
                gp.checked_update(count, exposure),
                Ok(()),
                "({count}, {exposure})"
            );
            let summary = gp.summary();
            let credible = summary.credible_interval(confidence).unwrap();
            let classical = summary.confidence_interval(confidence).unwrap();
            for reading in [
                summary.rate(),
                summary.variance(),
                summary.standard_error(),
                summary.chi_square().unwrap_or(0.0),
                summary.dispersion().unwrap_or(0.0),
                summary.p_value().unwrap_or(0.0),
                credible.lower(),
                credible.upper(),
                classical.lower(),
                classical.upper(),
            ] {
                assert!(reading.is_finite(), "({count}, {exposure}): {reading}");
            }
        }
    }

    /// A count that would take the events past `u64::MAX` is refused, and
    /// nothing changes.
    #[test]
    fn checked_update_refuses_a_count_that_would_overflow() {
        let mut gp = estimator::<f64>(1.0, 1.0);
        assert_eq!(gp.checked_update(u64::MAX - 5, 1.0), Ok(()));
        let before = gp.summary();
        assert_eq!(gp.checked_update(6, 1.0), Err(DataError::OutOfRange));
        assert_eq!(gp.summary(), before);
        assert_eq!(gp.checked_update(5, 1.0), Ok(()));
        assert_eq!(gp.summary().events(), u64::MAX);
    }

    /// A rate so small that almost nothing is expected has an interval of
    /// zero, not NaN.
    #[test]
    fn next_to_nothing_expected_is_nothing_expected() {
        let model = PoissonModel::<u64>::new(1e-310).unwrap();
        let interval = model.interval(1, Confidence::new(0.95));
        assert_eq!((interval.lower(), interval.upper()), (0.0, 0.0));
    }

    #[test]
    fn checked_update_agrees_with_update() {
        let (mut plain, mut checked) = (estimator::<f64>(1.0, 1.0), estimator::<f64>(1.0, 1.0));
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        for _ in 0..2_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let (count, exposure) = (state % 40, 0.5 + (state >> 20) as f64 % 5.0);
            plain.update(count, exposure);
            assert_eq!(checked.checked_update(count, exposure), Ok(()));
        }
        // Every reading, the test of the fit included.
        assert_eq!(plain.summary(), checked.summary());
        assert!(plain.summary().dispersion().unwrap().is_finite());
    }

    #[test]
    fn reset_forgets_the_data_and_keeps_the_prior() {
        let mut gp = estimator::<f64>(2.0, 3.0);
        gp.update(50, 5.0);
        gp.reset();
        assert_eq!(
            (
                gp.summary().events(),
                gp.summary().exposure(),
                gp.summary().rate()
            ),
            (0, 0.0, 2.0 / 3.0)
        );
    }

    #[test]
    fn the_builder_checks_the_prior() {
        let build = |alpha: f64, beta: f64| {
            PoissonEstimator::<f64>::builder()
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
        assert_eq!(
            PoissonEstimator::<f64>::builder()
                .build()
                .unwrap()
                .summary()
                .rate(),
            1.0
        );
    }

    // Counts over exposures, with the chi-square of the fit and its
    // p-value from SciPy 1.18.1's `chisquare(counts, rate * exposures)`.
    const STEADY: [(u64, f64); 12] = [
        (9, 0.82),
        (15, 1.75),
        (14, 2.0),
        (4, 0.57),
        (5, 0.87),
        (18, 2.82),
        (6, 0.68),
        (5, 0.82),
        (29, 2.87),
        (14, 2.05),
        (6, 1.42),
        (14, 1.78),
    ];
    const STEADY_CHI_SQUARE: f64 = 7.615899508724086;
    const STEADY_P_VALUE: f64 = 0.7472416100930674;
    const CLUSTERED: [(u64, f64); 12] = [
        (43, 2.35),
        (5, 0.99),
        (0, 0.65),
        (48, 2.0),
        (64, 2.74),
        (4, 0.57),
        (4, 2.51),
        (18, 0.98),
        (9, 0.73),
        (5, 0.54),
        (6, 1.23),
        (21, 2.32),
    ];
    const CLUSTERED_CHI_SQUARE: f64 = 98.87174431187796;

    fn fitted(data: &[(u64, f64)]) -> PoissonEstimator<f64> {
        let mut gp = estimator::<f64>(1.0, 1.0);
        for &(count, exposure) in data {
            gp.update(count, exposure);
        }
        gp
    }

    #[test]
    fn the_summary_carries_the_fit() {
        let summary = fitted(&STEADY).summary();
        assert_eq!(summary.events(), 139);
        assert_eq!(summary.observations(), 12);
        assert!(relative_error(summary.exposure(), 18.45) < 1e-14);
        assert!(relative_error(summary.rate(), 140.0 / 19.45) < 1e-14);
        // Gamma(140, 19.45): the standard error over the rate is
        // 1 / sqrt(140).
        assert!(
            relative_error(
                summary.standard_error() / summary.rate(),
                140f64.sqrt().recip()
            ) < 1e-14
        );
        assert_eq!(summary.standard_error(), summary.variance().sqrt());
    }

    #[test]
    fn the_dispersion_is_the_chi_square_over_its_degrees_of_freedom() {
        let steady = fitted(&STEADY).summary().dispersion().unwrap();
        assert!(relative_error(steady, STEADY_CHI_SQUARE / 11.0) < 1e-12);
        let clustered = fitted(&CLUSTERED).summary().dispersion().unwrap();
        assert!(relative_error(clustered, CLUSTERED_CHI_SQUARE / 11.0) < 1e-12);
        assert!(steady < 1.0 && clustered > 8.0);
    }

    #[test]
    fn the_p_value_tells_a_steady_process_from_a_clustered_one() {
        let steady = fitted(&STEADY).summary().p_value().unwrap();
        assert!(relative_error(steady, STEADY_P_VALUE) < 0.02, "{steady}");
        // Exact is 3e-16, far below what the estimate resolves.
        let clustered = fitted(&CLUSTERED).summary().p_value().unwrap();
        assert!((0.0..1e-6).contains(&clustered), "{clustered}");
    }

    #[test]
    fn the_fit_has_no_quality_reading_before_two_observations() {
        let mut gp = estimator::<f64>(1.0, 1.0);
        assert_eq!(gp.summary().dispersion(), None);
        gp.update(5, 1.0);
        assert_eq!(gp.summary().dispersion(), None);
        assert_eq!(gp.summary().p_value(), None);
        gp.update(7, 1.0);
        assert!(gp.summary().dispersion().is_some());
        // Observations with no events at all have no rate to test.
        let mut empty = estimator::<f64>(1.0, 1.0);
        empty.update(0, 1.0);
        empty.update(0, 1.0);
        assert_eq!(empty.summary().dispersion(), None);
    }

    /// Events at one instant are not a Poisson process. The rate takes
    /// them and the test of the fit is NaN until `reset`.
    #[test]
    fn an_update_of_no_length_spoils_the_test_of_the_fit() {
        for count in [0, 10] {
            let mut gp = fitted(&STEADY);
            gp.update(count, 0.0);
            let summary = gp.summary();
            assert_eq!(summary.events(), 139 + count);
            assert!(summary.rate().is_finite());
            assert!(summary.credible_interval(Confidence::new(0.95)).is_some());
            assert!(summary.chi_square().unwrap().is_nan(), "{count}");
            assert!(summary.dispersion().unwrap().is_nan(), "{count}");
            assert!(summary.p_value().unwrap().is_nan(), "{count}");
            gp.reset();
            gp.update(5, 1.0);
            gp.update(7, 1.0);
            assert!(gp.summary().dispersion().unwrap().is_finite());
        }
    }

    /// A corrupt exposure shows as NaN in every reading, never as a
    /// number.
    #[test]
    fn a_corrupt_exposure_reads_as_nan() {
        let mut gp = fitted(&STEADY);
        gp.update(3, f64::NAN);
        let confidence = Confidence::new(0.95);
        let summary = gp.summary();
        assert!(summary.rate().is_nan() && summary.variance().is_nan());
        assert!(summary.standard_error().is_nan() && summary.exposure().is_nan());
        assert!(summary.chi_square().unwrap().is_nan());
        assert!(summary.dispersion().unwrap().is_nan());
        assert!(summary.p_value().unwrap().is_nan());
        assert!(summary.credible_interval(confidence).unwrap().is_nan());
        assert!(summary.confidence_interval(confidence).unwrap().is_nan());
        assert!(gp.model().rate().is_nan());
        let model = PoissonModel::<f64>::new(4.0).unwrap();
        let interval = model.interval(f64::NAN, Confidence::new(0.95));
        assert!(interval.is_nan());
        let interval = model.interval(-5.0, Confidence::new(0.95));
        assert!(interval.is_nan());
    }

    #[test]
    fn reset_forgets_the_scatter() {
        let mut gp = fitted(&CLUSTERED);
        gp.reset();
        assert_eq!(gp.summary().observations(), 0);
        assert_eq!(gp.summary().dispersion(), None);
    }

    #[test]
    fn the_model_is_the_fitted_rate() {
        let gp = fitted(&STEADY);
        let model = gp.model();
        assert_eq!(model.rate(), gp.summary().rate());
        assert_eq!(model.expected(10.0), gp.summary().rate() * 10.0);
    }

    /// On physical time the exposure is a `Duration` and the rate is per
    /// second.
    #[test]
    fn the_model_is_on_the_callers_clock() {
        let model = PoissonModel::<i64>::new(9.5).unwrap();
        assert_eq!(model.expected(Duration::from_secs(4)), 38.0);
        assert_eq!(PoissonModel::<u64>::new(0.5).unwrap().expected(30), 15.0);
    }

    /// `(rate, exposure, confidence, lower, upper)`: exact ends from SciPy
    /// 1.18.1's `poisson.ppf` and `poisson.isf` at the expected count.
    const COUNT_INTERVALS: [(f64, f64, f64, f64, f64); 5] = [
        (9.2, 10.0, 0.95, 74.0, 111.0),
        (0.5, 40.0, 0.95, 12.0, 29.0),
        (120.0, 100.0, 0.999, 11641.0, 12362.0),
        (3.0, 100000.0, 0.95, 298927.0, 301074.0),
        (2.5, 400.0, 0.9, 948.0, 1052.0),
    ];

    #[test]
    fn the_count_interval_is_within_the_documented_counts_of_exact() {
        for (rate, exposure, confidence, lower, upper) in COUNT_INTERVALS {
            let model = PoissonModel::<f64>::new(rate).unwrap();
            let got = model.interval(exposure, Confidence::new(confidence));
            let limit = if confidence > 0.95 { 2.5 } else { 1.0 };
            assert!(
                (got.lower() - lower).abs() < limit && (got.upper() - upper).abs() < limit,
                "{rate} over {exposure} at {confidence}: {got:?} vs ({lower}, {upper})"
            );
        }
    }

    #[test]
    fn nothing_is_expected_over_no_exposure() {
        let model = PoissonModel::<f64>::new(4.0).unwrap();
        assert_eq!(model.expected(0.0), 0.0);
        let interval = model.interval(0.0, Confidence::new(0.95));
        assert_eq!((interval.lower(), interval.upper()), (0.0, 0.0));
    }

    #[test]
    fn the_model_checks_its_rate() {
        for bad in [-1.0, f64::NAN, f64::INFINITY] {
            assert!(PoissonModel::<f64>::new(bad).is_err(), "rate {bad}");
        }
        // A rate of zero is a process with no events.
        let silent = PoissonModel::<f64>::new(0.0).unwrap();
        assert_eq!(silent.expected(100.0), 0.0);
        let interval = silent.interval(100.0, Confidence::new(0.95));
        assert_eq!((interval.lower(), interval.upper()), (0.0, 0.0));
    }

    /// `(k, t, confidence, lower, upper)`: Garwood's exact interval from
    /// SciPy 1.18.1, `gamma.ppf(tail, k) / t` and `gamma.isf(tail, k + 1) / t`.
    const CONFIDENCE_INTERVALS: [(u64, f64, f64, f64, f64); 5] = [
        (37, 4.0, 0.95, 6.512853641776508, 12.749906535482706),
        (5, 2.5, 0.9, 0.788059827223812, 4.205213963496615),
        (1000, 100.0, 0.999, 8.992086831191871, 11.083940211570052),
        (0, 3.0, 0.95, 0.0, 1.2296264847046452),
        (123456, 1000.0, 0.99, 122.55282710520844, 124.36393315474935),
    ];

    /// The prior plays no part in it.
    #[test]
    fn the_confidence_interval_is_from_the_data_alone() {
        for (count, exposure, confidence, lower, upper) in CONFIDENCE_INTERVALS {
            let mut gp = estimator::<f64>(50.0, 0.001);
            gp.update(count, exposure);
            let got = gp
                .summary()
                .confidence_interval(Confidence::new(confidence))
                .unwrap();
            let limit = documented_distance(count as f64, (1.0 - confidence) / 2.0);
            assert!(
                (got.lower() - lower).abs() <= limit * lower
                    && relative_error(got.upper(), upper) < limit,
                "{count} over {exposure} at {confidence}: {got:?} vs ({lower}, {upper})"
            );
        }
        assert_eq!(
            estimator::<f64>(1.0, 1.0)
                .summary()
                .confidence_interval(Confidence::new(0.95)),
            None
        );
    }

    #[test]
    fn the_chi_square_comes_with_its_degrees_of_freedom() {
        let summary = fitted(&STEADY).summary();
        assert!(relative_error(summary.chi_square().unwrap(), STEADY_CHI_SQUARE) < 1e-12);
        assert_eq!(summary.degrees_of_freedom(), Some(11));
        let empty = estimator::<f64>(1.0, 1.0).summary();
        assert_eq!(
            (empty.chi_square(), empty.degrees_of_freedom()),
            (None, None)
        );
    }
}
