use nexus_stats_core::parts::{EwWeight, Warmup, Weight};

/// Errors, counted three ways from one stream of outcomes.
///
/// Feed it each event's outcome. It gives:
///
/// - **The count of errors**, in total and per interval. This is the
///   Errors of Brendan Gregg's
///   [USE method](https://www.brendangregg.com/usemethod.html): "the count
///   of error events". A count above zero is worth a look, more so while
///   it is still rising.
/// - **The ratio of events that failed, per interval.** This is the Errors
///   signal of Google's
///   [SRE book](https://sre.google/sre-book/monitoring-distributed-systems/):
///   "the rate of requests that fail".
/// - **A smoothed ratio**, an exponentially weighted average of the same
///   thing over every event since the start. This one is ours: a single
///   number for the recent tendency that needs no interval.
///
/// An interval is whatever passes between two calls to
/// [`take`](Self::take). Gregg's caution applies to the ratios: an average
/// over a long interval hides a short burst.
///
/// It reports numbers and no verdict. What counts as too many errors is
/// the caller's decision.
///
/// # Examples
///
/// ```
/// use nexus_stats_monitoring::ErrorRate;
///
/// let mut errors = ErrorRate::builder().alpha(0.5).build().unwrap();
/// for ok in [true, true, false, true] {
///     errors.update(ok);
/// }
/// let interval = errors.take();
/// assert_eq!((interval.errors(), interval.events()), (1, 4));
/// assert_eq!(interval.ratio(), Some(0.25));
///
/// errors.update(false);
/// assert_eq!(errors.take().errors(), 1); // this interval only
/// assert_eq!(errors.total_errors(), 2); // since the start
/// ```
#[derive(Debug, Clone)]
pub struct ErrorRate {
    weight: Weight,
    smoothed: f64,
    warmup: Warmup,
    /// Since construction or `reset`.
    total: ErrorSummary,
    /// The totals at the last `take`.
    taken: ErrorSummary,
}

/// Errors and events over a span of an [`ErrorRate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ErrorSummary {
    errors: u64,
    events: u64,
}

/// Builder for [`ErrorRate`].
#[derive(Debug, Clone)]
pub struct ErrorRateBuilder {
    weight: Option<EwWeight>,
    min_samples: u64,
}

impl ErrorSummary {
    const NONE: Self = Self {
        errors: 0,
        events: 0,
    };

    /// What was added to an `earlier` summary of the same stream.
    fn since(self, earlier: Self) -> Self {
        Self {
            errors: self.errors - earlier.errors,
            events: self.events - earlier.events,
        }
    }

    /// The count of events that failed.
    #[must_use]
    pub fn errors(&self) -> u64 {
        self.errors
    }

    /// The count of events, failed or not.
    #[must_use]
    pub fn events(&self) -> u64 {
        self.events
    }

    /// The ratio of events that failed, or `None` if there were no events.
    #[must_use]
    pub fn ratio(&self) -> Option<f64> {
        if self.events == 0 {
            return None;
        }
        Some(self.errors as f64 / self.events as f64)
    }
}

impl ErrorRate {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> ErrorRateBuilder {
        ErrorRateBuilder {
            weight: None,
            min_samples: 1,
        }
    }

    /// Records one event: `true` if it succeeded, `false` if it failed.
    #[inline]
    pub fn update(&mut self, success: bool) {
        let failed = !success;
        self.total.events += 1;
        self.total.errors += u64::from(failed);
        // PERF: the indicator as a number, not a select between constants.
        let indicator = f64::from(u8::from(failed));
        let first = self.warmup.awaits_first_sample();
        self.warmup.tick();
        self.smoothed = if first {
            indicator
        } else {
            self.weight.blend(indicator, self.smoothed)
        };
    }

    /// The errors and events since the last `take`, and starts a new
    /// interval.
    pub fn take(&mut self) -> ErrorSummary {
        let interval = self.total.since(self.taken);
        self.taken = self.total;
        interval
    }

    /// The count of errors since construction or `reset`.
    #[must_use]
    pub fn total_errors(&self) -> u64 {
        self.total.errors
    }

    /// The count of events since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total.events
    }

    /// The exponentially weighted ratio of events that failed, or `None`
    /// until `min_samples` events have been fed.
    #[must_use]
    pub fn smoothed_ratio(&self) -> Option<f64> {
        if !self.warmup.is_primed() {
            return None;
        }
        Some(self.smoothed)
    }

    /// Whether the smoothed ratio is available.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.warmup.is_primed()
    }

    /// Forgets every count and the smoothed ratio. The weight is kept.
    pub fn reset(&mut self) {
        self.smoothed = 0.0;
        self.warmup.reset();
        self.total = ErrorSummary::NONE;
        self.taken = ErrorSummary::NONE;
    }
}

impl ErrorRateBuilder {
    /// Weight of the smoothed ratio, in `(0, 1)`. Larger follows recent
    /// events more closely.
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.weight = Some(EwWeight::Alpha(alpha));
        self
    }

    /// Weight of the smoothed ratio as a half-life, in events.
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn halflife(mut self, halflife: f64) -> Self {
        self.weight = Some(EwWeight::Halflife(halflife));
        self
    }

    /// Weight of the smoothed ratio as a span (`alpha = 2 / (n + 1)`). Must
    /// be at least 2.
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.weight = Some(EwWeight::Span(n));
        self
    }

    /// Events before the smoothed ratio is given. Default 1. The counts
    /// and the interval ratio need none.
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the tracker.
    ///
    /// # Errors
    ///
    /// - `Missing` if no weight was set.
    /// - `Invalid` if the weight is out of range, or `min_samples` is 0.
    pub fn build(self) -> Result<ErrorRate, nexus_stats_core::ConfigError> {
        use nexus_stats_core::ConfigError::{Invalid, Missing};

        let alpha = self.weight.ok_or(Missing("alpha"))?.resolve()?;
        if self.min_samples == 0 {
            return Err(Invalid("min_samples must be >= 1"));
        }
        Ok(ErrorRate {
            weight: Weight::new(alpha),
            smoothed: 0.0,
            warmup: Warmup::new(self.min_samples, false),
            total: ErrorSummary::NONE,
            taken: ErrorSummary::NONE,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nexus_stats_core::ConfigError;

    fn errors(alpha: f64) -> ErrorRate {
        ErrorRate::builder().alpha(alpha).build().unwrap()
    }

    fn feed(rate: &mut ErrorRate, outcomes: &[bool]) {
        for &ok in outcomes {
            rate.update(ok);
        }
    }

    #[test]
    fn an_interval_counts_only_what_came_since_the_last_take() {
        let mut rate = errors(0.5);
        feed(&mut rate, &[true, false, false, true]);
        let first = rate.take();
        assert_eq!(
            (first.errors(), first.events(), first.ratio()),
            (2, 4, Some(0.5))
        );
        feed(&mut rate, &[true, true, false]);
        let second = rate.take();
        assert_eq!((second.errors(), second.events()), (1, 3));
        assert_eq!(second.ratio(), Some(1.0 / 3.0));
        // The totals run on.
        assert_eq!((rate.total_errors(), rate.count()), (3, 7));
    }

    #[test]
    fn an_empty_interval_has_no_ratio() {
        let mut rate = errors(0.5);
        let empty = rate.take();
        assert_eq!(
            (empty.errors(), empty.events(), empty.ratio()),
            (0, 0, None)
        );
        rate.update(true);
        rate.take();
        assert_eq!(rate.take().ratio(), None);
    }

    #[test]
    fn the_ratio_of_an_interval_is_exact() {
        let mut rate = errors(0.1);
        for i in 0..1_000u32 {
            rate.update(i % 8 != 0);
        }
        let interval = rate.take();
        assert_eq!((interval.errors(), interval.events()), (125, 1_000));
        assert_eq!(interval.ratio(), Some(0.125));
    }

    /// The first event is the smoothed ratio; each later one is blended in.
    #[test]
    fn the_smoothed_ratio_is_an_average_of_the_failure_indicator() {
        let mut rate = errors(0.5);
        assert_eq!(rate.smoothed_ratio(), None);
        rate.update(false);
        assert_eq!(rate.smoothed_ratio(), Some(1.0));
        rate.update(true);
        assert_eq!(rate.smoothed_ratio(), Some(0.5));
        rate.update(true);
        assert_eq!(rate.smoothed_ratio(), Some(0.25));
        rate.update(false);
        assert_eq!(rate.smoothed_ratio(), Some(0.625));
        // `take` does not touch it.
        rate.take();
        assert_eq!(rate.smoothed_ratio(), Some(0.625));
    }

    #[test]
    fn the_smoothed_ratio_settles_at_the_failure_share() {
        let mut rate = ErrorRate::builder().span(199).build().unwrap();
        for i in 0..20_000u32 {
            rate.update(i % 4 != 0);
        }
        assert!((rate.smoothed_ratio().unwrap() - 0.25).abs() < 0.02);
        let mut clean = errors(0.3);
        feed(&mut clean, &[true; 50]);
        assert_eq!(clean.smoothed_ratio(), Some(0.0));
        assert_eq!(clean.total_errors(), 0);
    }

    #[test]
    fn min_samples_delays_only_the_smoothed_ratio() {
        let mut rate = ErrorRate::builder()
            .alpha(0.5)
            .min_samples(3)
            .build()
            .unwrap();
        feed(&mut rate, &[false, true]);
        assert_eq!((rate.smoothed_ratio(), rate.is_primed()), (None, false));
        assert_eq!(rate.total_errors(), 1);
        rate.update(true);
        assert_eq!(rate.smoothed_ratio(), Some(0.25));
        assert_eq!(rate.take().ratio(), Some(1.0 / 3.0));
    }

    #[test]
    fn reset_forgets_the_counts_and_the_smoothed_ratio() {
        let mut rate = errors(0.5);
        feed(&mut rate, &[false, false, true]);
        rate.take();
        rate.update(false);
        rate.reset();
        assert_eq!((rate.total_errors(), rate.count()), (0, 0));
        assert_eq!(rate.smoothed_ratio(), None);
        assert_eq!(rate.take().events(), 0);
        rate.update(true);
        assert_eq!(rate.smoothed_ratio(), Some(0.0));
    }

    #[test]
    fn the_builder_checks_its_configuration() {
        assert!(matches!(
            ErrorRate::builder().build(),
            Err(ConfigError::Missing("alpha"))
        ));
        for bad in [0.0, 1.0, -0.5, f64::NAN] {
            assert!(ErrorRate::builder().alpha(bad).build().is_err(), "{bad}");
        }
        assert!(ErrorRate::builder().span(1).build().is_err());
        assert!(
            ErrorRate::builder()
                .alpha(0.5)
                .min_samples(0)
                .build()
                .is_err()
        );
        assert!(ErrorRate::builder().halflife(10.0).build().is_ok());
    }
}
