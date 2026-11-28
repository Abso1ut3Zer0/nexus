#[cfg(any(feature = "std", feature = "libm"))]
use nexus_stats_core::Confidence;
use nexus_stats_core::Probability;
use nexus_stats_core::math::MulAdd;

#[cfg(any(feature = "std", feature = "libm"))]
use super::{ConfidenceInterval, CredibleInterval, PredictionInterval};

/// The probability of success, learned from outcomes, with its
/// uncertainty.
///
/// Feed it successes and failures. It keeps a Beta posterior over the
/// probability, starting from a `Beta(alpha, beta)` prior: after `s`
/// successes and `f` failures the posterior is `Beta(alpha + s, beta + f)`.
/// The update is a few additions. With little data the estimate stays near
/// the prior, and with much it follows the observed rate. See
/// [conjugate prior](https://en.wikipedia.org/wiki/Conjugate_prior).
///
/// Use it for a fill rate, an error rate, a hit rate: any yes-or-no
/// outcome where the uncertainty matters as much as the estimate.
///
/// This type does the fitting and nothing else. [`summary`](Self::summary)
/// has everything about the fit: the probability, how far off it may be,
/// what went into it, and whether the outcomes look independent. And [`model`](Self::model) gives the fitted
/// [`BernoulliModel`]. A probability known already needs no fitting:
/// build a [`BernoulliModel`] from it.
///
/// # The interval is an estimate
///
/// [`credible_interval`](BernoulliSummary::credible_interval) is Abramowitz and
/// Stegun's closed form (26.5.22), not the exact Beta quantile. This type
/// is built for a stream, where the outcomes run to thousands and beyond,
/// and the closed form is at its best there: a few operations, with no
/// search that could fail to converge. What governs it is the count of
/// the rarer outcome, not the total. A thousand trials with ten failures
/// behave like ten (see the table on the method).
///
/// For exact intervals on a small sample, compute them offline:
/// `scipy.stats.beta.interval(confidence, alpha + s, beta + f)` with your
/// prior's `alpha` and `beta`, and `s` and `f` from the
/// [`summary`](Self::summary)'s `successes` and `failures`. To
/// start this type from a probability `p` fitted offline, trusted as much
/// as `n` outcomes, build it with `alpha = n p` and `beta = n (1 - p)`.
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::Confidence;
/// use nexus_stats_regression::estimation::BernoulliEstimator;
///
/// // Checked when this is compiled.
/// const NINETY_FIVE: Confidence = Confidence::new(0.95);
///
/// let mut fills = BernoulliEstimator::builder().build().unwrap();
/// fills.update(true);
/// fills.update_batch(29, 70);
/// // The prior (1, 1) counts as one success and one failure.
/// let summary = fills.summary();
/// assert_eq!(summary.probability(), 31.0 / 102.0);
/// let interval = summary.credible_interval(NINETY_FIVE).unwrap();
/// assert!(interval.contains(summary.probability()));
///
/// // What to expect of the next 204 orders.
/// assert!((fills.model().expected(204) - 62.0).abs() < 1e-12);
/// ```
#[derive(Debug, Clone)]
pub struct BernoulliEstimator {
    prior: Beta,
    /// Successes seen, apart from the prior.
    successes: u64,
    /// Failures seen, apart from the prior.
    failures: u64,
    runs: Runs,
}

/// Builder for [`BernoulliEstimator`].
#[derive(Debug, Clone)]
pub struct BernoulliEstimatorBuilder {
    alpha: f64,
    beta: f64,
}

impl BernoulliEstimator {
    /// Creates a builder. The prior defaults to `Beta(1, 1)`, which is
    /// uniform over `[0, 1]` and counts as one success and one failure.
    #[inline]
    #[must_use]
    pub fn builder() -> BernoulliEstimatorBuilder {
        BernoulliEstimatorBuilder {
            alpha: 1.0,
            beta: 1.0,
        }
    }

    /// Records one outcome.
    ///
    /// The counts are `u64` and add as `+` does, so past `u64::MAX` this
    /// panics in a debug build and wraps in a release one.
    #[inline]
    pub fn update(&mut self, success: bool) {
        self.successes += u64::from(success);
        self.failures += u64::from(!success);
        self.runs.record(success);
    }

    /// Records `successes` successes and `failures` failures at once.
    ///
    /// A batch of one kind is that many in a row. A batch of both kinds
    /// says nothing of their order, so after one the summary has no runs
    /// test until `reset`.
    #[inline]
    pub fn update_batch(&mut self, successes: u64, failures: u64) {
        self.successes += successes;
        self.failures += failures;
        self.runs.record_batch(successes, failures);
    }

    /// The fitted model, at the posterior mean of the probability.
    ///
    /// It carries the probability only. What uncertainty is left in it is
    /// in the [`summary`](Self::summary).
    #[inline]
    #[must_use]
    pub fn model(&self) -> BernoulliModel {
        BernoulliModel {
            probability: self.posterior().mean(),
        }
    }

    /// How good the fit is: the probability, how far off it may be, and
    /// what went into it. Changes nothing.
    #[inline]
    #[must_use]
    pub fn summary(&self) -> BernoulliSummary {
        BernoulliSummary {
            posterior: self.posterior(),
            successes: self.successes,
            failures: self.failures,
            runs: self.runs,
        }
    }

    /// Forgets every outcome. The prior is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.successes = 0;
        self.failures = 0;
        self.runs = Runs::default();
    }

    /// The prior with everything seen added to it.
    #[inline]
    fn posterior(&self) -> Beta {
        Beta {
            alpha: self.prior.alpha + self.successes as f64,
            beta: self.prior.beta + self.failures as f64,
        }
    }
}

impl BernoulliEstimatorBuilder {
    /// The prior's successes. Positive. Default 1.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = alpha;
        self
    }

    /// The prior's failures. Positive. Default 1.
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
    pub fn build(self) -> Result<BernoulliEstimator, nexus_stats_core::ConfigError> {
        use nexus_stats_core::ConfigError::Invalid;
        use nexus_stats_core::math::positive_finite;

        if !positive_finite(self.alpha) {
            return Err(Invalid(
                "BernoulliEstimator alpha must be positive and finite",
            ));
        }
        if !positive_finite(self.beta) {
            return Err(Invalid(
                "BernoulliEstimator beta must be positive and finite",
            ));
        }
        Ok(BernoulliEstimator {
            prior: Beta {
                alpha: self.alpha,
                beta: self.beta,
            },
            successes: 0,
            failures: 0,
            runs: Runs::default(),
        })
    }
}

/// The runs in a sequence of outcomes, counted as they arrive.
#[derive(Debug, Clone, Copy, PartialEq)]
struct Runs {
    count: u64,
    last: Option<bool>,
    /// False once a batch of both kinds has lost the order.
    ordered: bool,
}

impl Default for Runs {
    fn default() -> Self {
        Self {
            count: 0,
            last: None,
            ordered: true,
        }
    }
}

impl Runs {
    #[inline]
    fn record(&mut self, success: bool) {
        self.count += u64::from(self.last != Some(success));
        self.last = Some(success);
    }

    #[inline]
    fn record_batch(&mut self, successes: u64, failures: u64) {
        match (successes > 0, failures > 0) {
            (true, true) => self.ordered = false,
            (true, false) => self.record(true),
            (false, true) => self.record(false),
            (false, false) => {}
        }
    }

    #[inline]
    fn count(self) -> Option<u64> {
        self.ordered.then_some(self.count)
    }
}

/// The Wald-Wolfowitz runs test: the count of runs against what
/// independent outcomes would give.
// Without `sqrt` there is no p-value to read the run count or the variance.
#[cfg_attr(not(any(feature = "std", feature = "libm")), allow(dead_code))]
#[derive(Debug, Clone, Copy)]
struct RunsTest {
    runs: f64,
    successes: f64,
    failures: f64,
}

impl RunsTest {
    #[inline]
    fn mean(self) -> f64 {
        let trials = self.successes + self.failures;
        (2.0 * self.successes).fma(self.failures / trials, 1.0)
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    fn variance(self) -> f64 {
        let trials = self.successes + self.failures;
        let pairs = 2.0 * self.successes * self.failures;
        pairs * (pairs - trials) / (trials * trials * (trials - 1.0))
    }

    /// `None` where the count of runs cannot vary.
    #[cfg(any(feature = "std", feature = "libm"))]
    fn p_value(self) -> Option<f64> {
        use nexus_stats_core::math::probability::normal_upper_tail;

        let variance = self.variance();
        let can_vary = variance > 0.0;
        if !can_vary {
            return None;
        }
        // A count is a whole number: half a run of continuity correction.
        let distance = ((self.runs - self.mean()).abs() - 0.5).max(0.0);
        let z = distance / nexus_stats_core::math::sqrt(variance);
        Some(2.0 * normal_upper_tail(z))
    }
}

/// A beta distribution.
#[derive(Debug, Clone, Copy, PartialEq)]
struct Beta {
    alpha: f64,
    beta: f64,
}

impl Beta {
    #[inline]
    fn mean(self) -> f64 {
        self.alpha / (self.alpha + self.beta)
    }

    #[inline]
    fn variance(self) -> f64 {
        let sum = self.alpha + self.beta;
        (self.alpha * self.beta) / (sum * sum * (sum + 1.0))
    }

    /// Abramowitz and Stegun's estimate of the equal-tailed interval at
    /// `confidence`, where the form is of use.
    #[cfg(any(feature = "std", feature = "libm"))]
    fn interval(self, confidence: Confidence) -> Option<CredibleInterval> {
        use crate::probability::{beta_interval_approx, beta_one_sided_interval_approx};

        let (smaller, larger) = (self.alpha.min(self.beta), self.alpha.max(self.beta));
        let tail = confidence.tail();
        let (lower, upper) = if smaller >= 1.0 {
            beta_interval_approx(self.alpha, self.beta, tail)
        } else if smaller >= 0.5 && larger >= 10.0 {
            beta_one_sided_interval_approx(self.alpha, self.beta, tail)
        } else {
            return None;
        };
        Some(CredibleInterval::new(lower, upper))
    }
}

/// How good a [`BernoulliEstimator`]'s fit is, from its
/// [`summary`](BernoulliEstimator::summary).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BernoulliSummary {
    posterior: Beta,
    successes: u64,
    failures: u64,
    runs: Runs,
}

impl BernoulliSummary {
    /// The estimate: the posterior mean of the probability of success.
    #[inline]
    #[must_use]
    pub fn probability(&self) -> f64 {
        self.posterior.mean()
    }

    /// The posterior variance of the probability.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> f64 {
        self.posterior.variance()
    }

    /// An estimate of the equal-tailed interval that holds the probability
    /// of success with the given confidence: the posterior's quantiles at
    /// [`confidence.tail()`](Confidence::tail) from each end, by
    /// Abramowitz and Stegun's closed form (26.5.22).
    ///
    /// With a prior parameter below 1 there is a stretch with less than
    /// one success, or one failure, of evidence. Abramowitz and Stegun's
    /// form has no answer there. From one half up, which takes in the
    /// Jeffreys prior, a second closed form takes over once the other
    /// outcome has been seen about ten times: the rare side of the
    /// posterior is close to a Gamma. Its end away from the edge is
    /// within 2.5% of exact at 90% to 99% and 6% at 99.9%, and stays
    /// there however much data follows. `None` before that, and for a
    /// parameter below one half. The
    /// [`confidence_interval`](Self::confidence_interval) has an answer
    /// throughout.
    ///
    /// With `a = alpha + successes`, `b = beta + failures`, and `z` the
    /// standard normal quantile at `1 - tail`:
    ///
    /// ```text
    /// lambda = (z^2 - 3) / 6
    /// h      = 2 / (1 / (2a - 1) + 1 / (2b - 1))
    /// spread = z sqrt(h + lambda) / h
    /// skew   = (1 / (2b - 1) - 1 / (2a - 1)) (lambda + 5/6 - 2 / (3h))
    /// lower  = a / (a + b e^(2 (spread - skew)))
    /// upper  = a / (a + b e^(2 (-spread - skew)))
    /// ```
    ///
    /// Every answer is a little off the exact one, by an amount that
    /// shrinks as the rarer outcome is seen more. This is how far an end
    /// of the interval is from the exact end, as a fraction of its
    /// distance to the nearer of 0 and 1 (the farther of the two ends).
    /// The smaller parameter is the smaller of `a` and `b`. It is a
    /// distance, not a rate of failure. The same inputs always give the
    /// same answer.
    ///
    /// | Smaller parameter | 90% | 95% | 99% | 99.9% |
    /// |---|---|---|---|---|
    /// | 3 | 2.5% | 3.2% | 4.2% | 5.7% |
    /// | 5 | 0.90% | 1.1% | 1.2% | 1.2% |
    /// | 11 | 0.21% | 0.23% | 0.19% | 0.21% |
    /// | 31 | 0.037% | 0.037% | 0.020% | 0.050% |
    /// | 101 | 5.6e-5 | 5.3e-5 | 2.0e-5 | 8.7e-5 |
    /// | 1,001 | 1.6e-6 | 1.5e-6 | 3.3e-7 | 2.8e-6 |
    /// | 10,001 | 5.0e-8 | 4.4e-8 | 7.7e-9 | 8.8e-8 |
    /// | 100,001 | 1.6e-9 | 1.4e-9 | 2.3e-10 | 2.8e-9 |
    /// | 1,000,001 | 4.8e-11 | 4.5e-11 | 1.0e-11 | 1.1e-10 |
    ///
    /// The larger parameter hardly matters, and the table is the worst
    /// over a ratio of 1 to 1,000,000 between the two. With the default
    /// prior, 30 successes and 70 failures, the exact 95% interval is
    /// (0.21898, 0.39615) and this gives (0.21895, 0.39615).
    ///
    /// Between a smaller parameter of 1 and 3 the interval is poor: 8% off
    /// at 2, at 95%. At exactly 1, which is the default prior before the
    /// first success or the first failure, the quantile has an exact
    /// closed form and that is used. These are measurements against
    /// SciPy, not proven bounds.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn credible_interval(&self, confidence: Confidence) -> Option<CredibleInterval> {
        self.posterior.interval(confidence)
    }

    /// An estimate of the classical interval for the probability, from
    /// the data alone with no prior: the Clopper-Pearson interval, by the
    /// closed form [`credible_interval`](Self::credible_interval) uses.
    /// `None` before any outcome.
    ///
    /// With `s` successes and `f` failures, the lower end is the quantile
    /// of a `Beta(s, f + 1)` and the upper end that of a `Beta(s + 1, f)`.
    /// With no successes the lower end is 0, and with no failures the
    /// upper end is 1. The distance from exact is the table on
    /// `credible_interval`, read at the count of the rarer outcome, and
    /// the end beside an outcome never seen is exact. For the exact value,
    /// offline: `scipy.stats.binomtest(s, s + f).proportion_ci(confidence)`.
    ///
    /// It differs from the credible interval by the prior. With the
    /// default prior and many outcomes the two are nearly the same.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn confidence_interval(&self, confidence: Confidence) -> Option<ConfidenceInterval> {
        if self.trials() == 0 {
            return None;
        }
        let (successes, failures) = (self.successes as f64, self.failures as f64);
        // The form needs parameters of at least 1. An end whose parameter
        // would be 0 is known outright.
        let (lower, upper) = crate::probability::beta_interval_between(
            (successes.max(1.0), failures + 1.0),
            (successes + 1.0, failures.max(1.0)),
            confidence.tail(),
        );
        Some(ConfidenceInterval::new(
            if self.successes == 0 { 0.0 } else { lower },
            if self.failures == 0 { 1.0 } else { upper },
        ))
    }

    /// How far off the probability may be: the square root of the
    /// variance. Near one half it is about `1 / (2 sqrt(trials))`, so a
    /// hundred trials pin it to about 0.05 and ten thousand to 0.005.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn standard_error(&self) -> f64 {
        nexus_stats_core::math::sqrt(self.variance())
    }

    /// Successes recorded, apart from the prior.
    #[inline]
    #[must_use]
    pub fn successes(&self) -> u64 {
        self.successes
    }

    /// Failures recorded, apart from the prior.
    #[inline]
    #[must_use]
    pub fn failures(&self) -> u64 {
        self.failures
    }

    /// Outcomes recorded: successes and failures together. It adds as `+`
    /// does.
    #[inline]
    #[must_use]
    pub fn trials(&self) -> u64 {
        self.successes + self.failures
    }

    /// Runs seen: stretches of one outcome in a row. `Y Y N N N Y` has
    /// three. `None` once a batch of both kinds has lost the order.
    ///
    /// On its own the number says little. Read it against
    /// [`expected_runs`](Self::expected_runs).
    #[inline]
    #[must_use]
    pub fn runs(&self) -> Option<u64> {
        self.runs.count()
    }

    /// The runs that independent outcomes would give on average, for the
    /// successes `s` and failures `f` seen: `2 s f / (s + f) + 1`. `None`
    /// where [`runs`](Self::runs) is, and before any outcome.
    ///
    /// Fewer runs than this means the outcomes come in streaks. More
    /// means they alternate.
    #[inline]
    #[must_use]
    pub fn expected_runs(&self) -> Option<f64> {
        self.runs.count()?;
        if self.trials() == 0 {
            return None;
        }
        Some(self.runs_test().mean())
    }

    /// An estimate of the probability that independent outcomes would
    /// give a count of runs at least this far from the expected one, by
    /// the Wald-Wolfowitz runs test. Small means the outcomes are not
    /// independent: a single probability does not describe them. `None`
    /// where [`runs`](Self::runs) is, and until there are a success, a
    /// failure and three outcomes in all.
    ///
    /// The hypothesis under test is that the outcomes are independent. So
    /// a small value counts against the model, the other way round from
    /// the p-value of a regression coefficient.
    ///
    /// Reading it: below 0.05 is the usual line for "not independent". It
    /// does not say which way, so compare [`runs`](Self::runs) with
    /// [`expected_runs`](Self::expected_runs): fewer is streaks, more is
    /// alternation. With very many outcomes it turns small for a departure
    /// too slight to matter. The ratio of the two is the size of it: 0.99
    /// is trivially streaky and 0.7 is seriously so.
    ///
    /// ```text
    /// mean     = 2 s f / (s + f) + 1
    /// variance = 2 s f (2 s f - s - f) / ((s + f)^2 (s + f - 1))
    /// z        = (|runs - mean| - 1/2) / sqrt(variance)
    /// p        = twice the probability a standard normal is above z
    /// ```
    ///
    /// The half is a continuity correction, since a count of runs is a
    /// whole number. It is within 4% of the exact probability down to
    /// 0.05 once the rarer outcome has been seen ten times. Smaller
    /// values are reliable only when the two outcomes are roughly
    /// balanced.
    ///
    /// This is the test in statsmodels' `runstest_1samp` and R's
    /// `tseries::runs.test`, with the same mean and variance. They differ
    /// on the half: statsmodels applies it only below 50 outcomes and R
    /// never, so their values differ from this one. Against the exact
    /// distribution of runs, applying it always was the closest at every
    /// size measured. At 500 successes and 500 failures, near a
    /// probability of 0.05, it gives the exact value where leaving it out
    /// gives 0.93 of it.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn p_value(&self) -> Option<f64> {
        self.runs.count()?;
        self.runs_test().p_value()
    }

    #[inline]
    fn runs_test(&self) -> RunsTest {
        RunsTest {
            runs: self.runs.count as f64,
            successes: self.successes as f64,
            failures: self.failures as f64,
        }
    }
}

/// A yes-or-no outcome with a known probability of success: what to
/// expect from it.
///
/// Give it the probability, known already or fitted by a
/// [`BernoulliEstimator`].
///
/// # Examples
///
/// ```
/// use nexus_stats_regression::Probability;
/// use nexus_stats_regression::estimation::BernoulliModel;
///
/// // Checked when this is compiled.
/// const ONE_IN_FOUR: Probability = Probability::new(0.25);
///
/// let fills = BernoulliModel::new(ONE_IN_FOUR);
/// assert_eq!(fills.expected(200), 50.0);
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BernoulliModel {
    probability: f64,
}

impl BernoulliModel {
    /// A model with the given probability of success. 0 and 1 are models
    /// too: an outcome that never, or always, happens.
    #[inline]
    #[must_use]
    pub const fn new(probability: Probability) -> Self {
        Self {
            probability: probability.value(),
        }
    }

    /// The probability of success.
    #[inline]
    #[must_use]
    pub fn probability(&self) -> f64 {
        self.probability
    }

    /// The successes expected in `trials` outcomes: the probability times
    /// the trials.
    #[inline]
    #[must_use]
    pub fn expected(&self, trials: u64) -> f64 {
        self.probability * trials as f64
    }

    /// An estimate of the equal-tailed interval that holds the successes
    /// in `trials` outcomes with the given confidence.
    ///
    /// The exact count is binomial. This matches a Gamma to the mean and
    /// variance of the rarer outcome's count and takes that Gamma's
    /// interval by Wilson and Hilferty's closed form. With `q` the smaller
    /// of the probability and one minus it, and `m = trials q`:
    ///
    /// ```text
    /// shape = m / (1 - q)
    /// v     = 1 / (9 shape)
    /// lower = (1 - q) shape (1 - v - z sqrt(v))^3
    /// upper = (1 - q) shape (1 - v + z sqrt(v))^3
    /// ```
    ///
    /// counted in the rarer outcome, and taken from `trials` when that is
    /// the failures. A count is a whole number and the ends here are not.
    /// From 20 to 1,000,000 trials an end is within one count of the exact
    /// end at 95% and within about two and a half at 99.9% (SciPy's
    /// `binom.ppf` and `binom.isf`).
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn interval(&self, trials: u64, confidence: Confidence) -> PredictionInterval {
        let trials = trials as f64;
        let successes_are_rarer = self.probability <= 0.5;
        let rarer = if successes_are_rarer {
            self.probability
        } else {
            1.0 - self.probability
        };
        let (lower, upper) = crate::probability::count_interval_approx(
            trials * rarer,
            1.0 - rarer,
            confidence.tail(),
        );
        let upper = upper.min(trials);
        if successes_are_rarer {
            return PredictionInterval::new(lower, upper);
        }
        PredictionInterval::new(trials - upper, trials - lower)
    }
}

#[cfg(test)]
#[allow(clippy::unreadable_literal, clippy::excessive_precision)]
mod tests {
    use super::*;

    fn estimator(alpha: f64, beta: f64) -> BernoulliEstimator {
        BernoulliEstimator::builder()
            .alpha(alpha)
            .beta(beta)
            .build()
            .unwrap()
    }

    /// `Beta(a, b)` with `a = alpha + s` and `b = beta + f`: the mean is
    /// `a / (a + b)` and the variance `a b / ((a + b)^2 (a + b + 1))`.
    #[test]
    fn the_posterior_is_the_prior_plus_what_was_seen() {
        let mut bb = estimator(2.0, 3.0);
        bb.update_batch(8, 7);
        assert_eq!(bb.summary().probability(), 10.0 / 20.0);
        assert_eq!(bb.summary().variance(), 100.0 / (400.0 * 21.0));
    }

    #[test]
    fn the_prior_is_the_estimate_before_any_data() {
        let bb = estimator(10.0, 1.0);
        assert_eq!(bb.summary().probability(), 10.0 / 11.0);
        assert_eq!(bb.summary().trials(), 0);
        // The default prior is uniform.
        assert_eq!(
            BernoulliEstimator::builder()
                .build()
                .unwrap()
                .summary()
                .probability(),
            0.5
        );
    }

    #[test]
    fn one_at_a_time_and_a_batch_agree() {
        let mut single = estimator(1.0, 1.0);
        for outcome in 0..50 {
            single.update(outcome < 30);
        }
        let mut batch = estimator(1.0, 1.0);
        batch.update_batch(30, 20);
        assert_eq!(
            single.summary().probability(),
            batch.summary().probability()
        );
        assert_eq!(single.summary().variance(), batch.summary().variance());
        assert_eq!(
            (
                single.summary().successes(),
                single.summary().failures(),
                single.summary().trials()
            ),
            (30, 20, 50)
        );
        assert_eq!(
            (batch.summary().successes(), batch.summary().failures()),
            (30, 20)
        );
    }

    /// The counts are whole numbers kept apart from the prior, so a
    /// fractional prior does not blur them.
    #[test]
    fn the_counts_are_exact_with_a_fractional_prior() {
        let mut bb = estimator(0.1, 0.7);
        bb.update_batch(3, 1 << 60);
        assert_eq!(
            (bb.summary().successes(), bb.summary().failures()),
            (3, 1 << 60)
        );
    }

    #[test]
    fn more_data_narrows_the_estimate() {
        let mut bb = estimator(1.0, 1.0);
        let before = bb.summary().variance();
        bb.update_batch(50, 50);
        assert!(bb.summary().variance() < before);
    }

    // `(alpha, beta, s, f, confidence, lower, upper)`: exact intervals from
    // SciPy 1.18.1's `beta.interval(confidence, alpha + s, beta + f)`.
    #[cfg(any(feature = "std", feature = "libm"))]
    const INTERVALS: [(f64, f64, u64, u64, f64, f64, f64); 7] = [
        (
            1.0,
            1.0,
            30,
            70,
            0.95,
            0.2189787263040341,
            0.396147128647689,
        ),
        (
            1.0,
            1.0,
            5,
            995,
            0.95,
            0.0022027766157155008,
            0.011617891448578138,
        ),
        (
            1.0,
            1.0,
            5000,
            5000,
            0.999,
            0.48355305174216545,
            0.5164469482578347,
        ),
        (0.5, 0.5, 12, 3, 0.9, 0.5976129413845882, 0.9239876218505547),
        (3.0, 8.0, 0, 0, 0.95, 0.0667395111777345, 0.5560954623076415),
        (
            1.0,
            1.0,
            990,
            10,
            0.99,
            0.9787450746992187,
            0.9956706559505755,
        ),
        (
            1.0,
            1.0,
            123456,
            876544,
            0.95,
            0.12281271652550484,
            0.12410221622034964,
        ),
    ];

    /// The distance from exact the docs state, with a tenth of room, for
    /// the documented smaller parameter at or below `smaller` and the
    /// documented confidence whose tail is at or below `tail`.
    #[cfg(any(feature = "std", feature = "libm"))]
    fn documented_distance(smaller: f64, tail: f64) -> f64 {
        let by_confidence = match smaller {
            s if s >= 100_001.0 => [1.71e-9, 1.57e-9, 2.50e-10, 3.06e-9],
            s if s >= 10_001.0 => [5.47e-8, 4.83e-8, 8.47e-9, 9.67e-8],
            s if s >= 1_001.0 => [1.78e-6, 1.60e-6, 3.58e-7, 3.07e-6],
            s if s >= 101.0 => [6.11e-5, 5.78e-5, 2.17e-5, 9.59e-5],
            s if s >= 31.0 => [4.06e-4, 4.06e-4, 2.23e-4, 5.48e-4],
            s if s >= 11.0 => [2.35e-3, 2.55e-3, 2.04e-3, 2.33e-3],
            s if s >= 5.0 => [9.91e-3, 1.18e-2, 1.28e-2, 1.33e-2],
            _ => [2.71e-2, 3.49e-2, 4.63e-2, 6.28e-2],
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

    /// How far `got` is from `want`, as a fraction of `want`'s distance to
    /// the nearer of 0 and 1.
    #[cfg(any(feature = "std", feature = "libm"))]
    fn distance(got: f64, want: f64) -> f64 {
        (got - want).abs() / want.min(1.0 - want)
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn the_interval_is_as_close_to_exact_as_documented() {
        for (alpha, beta, successes, failures, confidence, lower, upper) in INTERVALS {
            let mut bb = estimator(alpha, beta);
            bb.update_batch(successes, failures);
            let got = bb
                .summary()
                .credible_interval(Confidence::new(confidence))
                .unwrap();
            let smaller = (alpha + successes as f64).min(beta + failures as f64);
            let limit = documented_distance(smaller, (1.0 - confidence) / 2.0);
            assert!(
                distance(got.lower(), lower) < limit && distance(got.upper(), upper) < limit,
                "({alpha}, {beta}) + ({successes}, {failures}) at {confidence}: {got:?}, limit {limit}"
            );
        }
    }

    /// With a prior below 1 and almost no data there is too little
    /// evidence for either closed form.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn there_is_no_interval_with_too_little_evidence() {
        let confidence = Confidence::new(0.95);
        let mut bb = estimator(0.5, 0.5);
        assert!(bb.summary().credible_interval(confidence).is_none());
        bb.update(true);
        assert!(bb.summary().credible_interval(confidence).is_none());
        bb.update(false);
        assert!(bb.summary().credible_interval(confidence).is_some());
        // The default prior always has one.
        assert!(
            estimator(1.0, 1.0)
                .summary()
                .credible_interval(confidence)
                .is_some()
        );
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn the_interval_narrows_with_data_and_widens_with_confidence() {
        let mut bb = estimator(1.0, 1.0);
        bb.update_batch(10, 10);
        let few = bb
            .summary()
            .credible_interval(Confidence::new(0.95))
            .unwrap();
        bb.update_batch(200, 200);
        let many = bb
            .summary()
            .credible_interval(Confidence::new(0.95))
            .unwrap();
        assert!(many.width() < few.width());

        let mut last = 0.0;
        for level in [0.5, 0.9, 0.95, 0.99, 0.999] {
            let interval = bb
                .summary()
                .credible_interval(Confidence::new(level))
                .unwrap();
            assert!(
                interval.lower() < bb.summary().probability()
                    && bb.summary().probability() < interval.upper()
            );
            assert!(interval.width() > last);
            last = interval.width();
        }
    }

    /// With every outcome a success the interval still sits inside
    /// `[0, 1]`.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn a_one_sided_record_keeps_the_interval_in_range() {
        let mut bb = estimator(1.0, 1.0);
        bb.update_batch(1_000_000, 0);
        let interval = bb
            .summary()
            .credible_interval(Confidence::new(0.999))
            .unwrap();
        assert!(
            0.0 < interval.lower()
                && interval.lower() < interval.upper()
                && interval.upper() <= 1.0
        );
    }

    #[test]
    fn reset_forgets_the_data_and_keeps_the_prior() {
        let mut bb = estimator(5.0, 3.0);
        bb.update_batch(100, 0);
        bb.reset();
        assert_eq!(bb.summary().probability(), 5.0 / 8.0);
        assert_eq!(
            (
                bb.summary().successes(),
                bb.summary().failures(),
                bb.summary().trials()
            ),
            (0, 0, 0)
        );
    }

    #[test]
    fn the_builder_checks_the_prior() {
        let build = |alpha, beta| {
            BernoulliEstimator::builder()
                .alpha(alpha)
                .beta(beta)
                .build()
        };
        for bad in [0.0, -1.0, f64::NAN, f64::INFINITY] {
            assert!(build(bad, 1.0).is_err(), "alpha {bad}");
            assert!(build(1.0, bad).is_err(), "beta {bad}");
        }
        assert!(build(0.5, 0.5).is_ok());
    }

    #[test]
    fn the_summary_carries_the_fit() {
        let mut bb = estimator(1.0, 1.0);
        bb.update_batch(30, 70);
        let summary = bb.summary();
        assert_eq!(summary.probability(), 31.0 / 102.0);
        assert_eq!(
            (summary.successes(), summary.failures(), summary.trials()),
            (30, 70, 100)
        );
        // Beta(31, 71): variance 31 * 71 / (102^2 * 103).
        assert_eq!(summary.variance(), 31.0 * 71.0 / (102.0 * 102.0 * 103.0));
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn the_standard_error_is_the_root_of_the_variance() {
        let mut bb = estimator(1.0, 1.0);
        bb.update_batch(5_000, 5_000);
        let summary = bb.summary();
        assert_eq!(summary.standard_error(), summary.variance().sqrt());
        assert!((summary.standard_error() - 0.005).abs() < 1e-5);
    }

    /// The Jeffreys prior on a record with no failures: an interval once
    /// there are about ten outcomes, from the form for one unseen side.
    /// Exact is SciPy 1.18.1's `beta.interval(0.95, 100.5, 0.5)`.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn a_one_sided_record_under_the_jeffreys_prior_has_an_interval() {
        let confidence = Confidence::new(0.95);
        let mut bb = estimator(0.5, 0.5);
        bb.update_batch(9, 0);
        assert!(bb.summary().credible_interval(confidence).is_none());
        bb.update_batch(91, 0);
        let got = bb.summary().credible_interval(confidence).unwrap();
        assert!(distance(got.lower(), 0.9752547299847301) < 0.025, "{got:?}");
        assert!(0.9999951019268956 <= got.upper() && got.upper() <= 1.0);
        assert!(got.contains(bb.summary().probability()) && !got.is_nan());
        // The classical interval never needed the prior.
        assert!(bb.summary().confidence_interval(confidence).is_some());
    }

    #[test]
    fn the_model_is_the_fitted_probability() {
        let mut bb = estimator(1.0, 1.0);
        bb.update_batch(30, 70);
        assert_eq!(bb.model().probability(), bb.summary().probability());
        assert_eq!(
            BernoulliModel::new(Probability::new(0.25)).expected(200),
            50.0
        );
    }

    /// `(s, f, confidence, lower, upper)`: the Clopper-Pearson interval from
    /// SciPy 1.18.1's `binomtest(s, s + f).proportion_ci(confidence, 'exact')`.
    #[cfg(any(feature = "std", feature = "libm"))]
    const CONFIDENCE_INTERVALS: [(u64, u64, f64, f64, f64); 6] = [
        (12, 88, 0.95, 0.06356890256115931, 0.2002356836199688),
        (5, 995, 0.95, 0.0016254195175627604, 0.011629470559812172),
        (5000, 5000, 0.999, 0.48350226772804283, 0.5164977322719572),
        (0, 50, 0.95, 0.0, 0.07112173646419766),
        (40, 0, 0.99, 0.8759397804706242, 1.0),
        (990, 10, 0.9, 0.9830968248794375, 0.9945648598552932),
    ];

    /// The prior plays no part in it.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn the_confidence_interval_is_from_the_data_alone() {
        for (successes, failures, confidence, lower, upper) in CONFIDENCE_INTERVALS {
            let mut bb = estimator(40.0, 0.25);
            bb.update_batch(successes, failures);
            let got = bb
                .summary()
                .confidence_interval(Confidence::new(confidence))
                .unwrap();
            let rarer = successes.min(failures) as f64;
            let limit = documented_distance(rarer, (1.0 - confidence) / 2.0);
            let close = |got: f64, want: f64| {
                let room = want.min(1.0 - want);
                (got - want).abs() <= limit * room
            };
            assert!(
                close(got.lower(), lower) && close(got.upper(), upper),
                "({successes}, {failures}) at {confidence}: {got:?} vs ({lower}, {upper})"
            );
        }
        let none = estimator(1.0, 1.0).summary();
        assert_eq!(none.confidence_interval(Confidence::new(0.95)), None);
    }

    /// `(p, trials, confidence, lower, upper)`: exact ends from SciPy
    /// 1.18.1's `binom.ppf` and `binom.isf`.
    #[cfg(any(feature = "std", feature = "libm"))]
    const PREDICTION_INTERVALS: [(f64, u64, f64, f64, f64); 5] = [
        (0.25, 200, 0.95, 38.0, 62.0),
        (0.5, 1000, 0.95, 469.0, 531.0),
        (0.01, 100000, 0.999, 898.0, 1105.0),
        (0.9, 5000, 0.95, 4458.0, 4541.0),
        (0.1, 50, 0.9, 2.0, 9.0),
    ];

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn the_prediction_interval_is_within_the_documented_counts_of_exact() {
        for (probability, trials, confidence, lower, upper) in PREDICTION_INTERVALS {
            let model = BernoulliModel::new(Probability::new(probability));
            let got = model.interval(trials, Confidence::new(confidence));
            let limit = if confidence > 0.95 { 2.6 } else { 1.0 };
            assert!(
                (got.lower() - lower).abs() < limit && (got.upper() - upper).abs() < limit,
                "{probability} over {trials} at {confidence}: {got:?} vs ({lower}, {upper})"
            );
        }
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn a_certain_outcome_has_a_prediction_interval_of_no_width() {
        let confidence = Confidence::new(0.95);
        let never = BernoulliModel::new(Probability::new(0.0)).interval(100, confidence);
        assert_eq!((never.lower(), never.upper()), (0.0, 0.0));
        let always = BernoulliModel::new(Probability::new(1.0)).interval(100, confidence);
        assert_eq!((always.lower(), always.upper()), (100.0, 100.0));
    }

    /// A sequence with `successes`, `failures` and exactly `runs` runs,
    /// fed one outcome at a time.
    fn sequence(successes: u64, failures: u64, runs: u64) -> BernoulliEstimator {
        // Alternate single outcomes, then spend what is left of each kind
        // on the last two runs.
        let mut bb = estimator(1.0, 1.0);
        let (mut s, mut f) = (successes, failures);
        for run in 0..runs {
            let success = run % 2 == 0;
            let left = if success { &mut s } else { &mut f };
            let last_of_kind = run + 2 >= runs;
            let length = if last_of_kind { *left } else { 1 };
            *left -= length;
            for _ in 0..length {
                bb.update(success);
            }
        }
        assert_eq!((s, f), (0, 0));
        bb
    }

    #[test]
    fn the_runs_are_the_stretches_of_one_outcome() {
        let mut bb = estimator(1.0, 1.0);
        assert_eq!(bb.summary().runs(), Some(0));
        assert_eq!(bb.summary().expected_runs(), None);
        for success in [true, true, false, false, false, true] {
            bb.update(success);
        }
        assert_eq!(bb.summary().runs(), Some(3));
        // 2 * 3 * 3 / 6 + 1.
        assert_eq!(bb.summary().expected_runs(), Some(4.0));
    }

    // `(s, f, runs, expected runs, p)`: the two-sided normal p-value with
    // half a run of continuity correction, from SciPy 1.18.1's `norm.sf`.
    // The mean and variance are statsmodels' `Runs.runs_test`.
    #[cfg(any(feature = "std", feature = "libm"))]
    const RUNS: [(u64, u64, u64, f64, f64); 5] = [
        (30, 70, 25, 43.0, 2.7162863312644742e-05),
        (30, 70, 43, 43.0, 1.0),
        (500, 500, 460, 501.0, 0.01038534121762965),
        (12, 8, 5, 10.6, 0.014421267248466502),
        (40, 60, 60, 49.0, 0.02783757550247296),
    ];

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn the_runs_test_tells_streaks_from_independent_outcomes() {
        for (successes, failures, runs, expected, p) in RUNS {
            let summary = sequence(successes, failures, runs).summary();
            assert_eq!(summary.runs(), Some(runs));
            assert!((summary.expected_runs().unwrap() - expected).abs() < 1e-12);
            let got = summary.p_value().unwrap();
            assert!(
                (got - p).abs() < 3e-7,
                "({successes}, {failures}, {runs}): {got} vs {p}"
            );
        }
    }

    /// A batch of one kind is a run. A batch of both has no order.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn a_mixed_batch_ends_the_runs_test() {
        let mut bb = estimator(1.0, 1.0);
        bb.update_batch(5, 0);
        bb.update_batch(0, 4);
        bb.update_batch(3, 0);
        assert_eq!(bb.summary().runs(), Some(3));
        assert!(bb.summary().p_value().is_some());
        bb.update_batch(2, 2);
        let summary = bb.summary();
        assert_eq!(
            (summary.runs(), summary.expected_runs(), summary.p_value()),
            (None, None, None)
        );
        bb.reset();
        assert_eq!(bb.summary().runs(), Some(0));
    }

    /// With one outcome never seen, or one of each, the count of runs
    /// cannot vary.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn there_is_no_p_value_where_the_runs_cannot_vary() {
        let mut bb = estimator(1.0, 1.0);
        bb.update_batch(50, 0);
        assert_eq!(bb.summary().p_value(), None);
        bb.update(false);
        assert!(bb.summary().p_value().is_some());
        let mut pair = estimator(1.0, 1.0);
        pair.update(true);
        pair.update(false);
        assert_eq!(pair.summary().p_value(), None);
    }

    /// At any confidence a float can express, on each of the closed
    /// forms, the ends are numbers in order inside `[0, 1]`.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn the_ends_stay_in_order_and_in_range_at_every_confidence() {
        let levels = (1..=16).map(|nines| 1.0 - 10f64.powi(-nines)).chain([
            0.5,
            1e-9,
            1.0 - f64::EPSILON / 2.0,
        ]);
        for level in levels {
            let confidence = Confidence::new(level);
            for (alpha, beta, successes, failures) in [
                (1.0, 1.0, 30, 70),
                (1.0, 1.0, 1_000, 0),
                (0.5, 0.5, 0, 10),
                (0.5, 0.5, 400, 0),
                (0.9, 0.6, 25, 0),
            ] {
                let mut bb = estimator(alpha, beta);
                bb.update_batch(successes, failures);
                let summary = bb.summary();
                let credible = summary
                    .credible_interval(confidence)
                    .map(|interval| (interval.lower(), interval.upper()));
                let classical = summary
                    .confidence_interval(confidence)
                    .map(|interval| (interval.lower(), interval.upper()));
                assert!(credible.is_some() && classical.is_some());
                for (lower, upper) in [credible, classical].into_iter().flatten() {
                    assert!(
                        0.0 <= lower && lower <= upper && upper <= 1.0,
                        "({alpha}, {beta}) + ({successes}, {failures}) at {level}: ({lower}, {upper})"
                    );
                }
            }
        }
    }
}
