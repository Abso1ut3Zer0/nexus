use crate::Direction;

/// CUSUM — Cumulative Sum change detector (Page, 1954).
///
/// Detects persistent shifts in the mean of a streaming process
/// in either direction. Signals when cumulative deviation from a
/// target exceeds a threshold.
///
/// Supports asymmetric slack and threshold parameters for different
/// sensitivity to upward vs downward shifts.
///
/// # After an alarm
///
/// By default the sums are not cleared when a side crosses its threshold:
/// `update` keeps reporting that direction until the sum drains back under
/// the threshold or the caller calls [`reset`](Self::reset). That suits "is
/// the process still off target", and a long excursion takes as long to
/// drain as it took to build. Set
/// [`restart_on_alarm`](CusumBuilder::restart_on_alarm) for the classic
/// restarting CUSUM, which zeroes the alarming side as it reports, so each
/// alarm is a fresh detection.
///
/// If both sides are over threshold at once, the one further over (relative
/// to its threshold) is reported; [`upper`](Self::upper) and
/// [`lower`](Self::lower) expose both sums.
///
/// # Use Cases
/// - Exchange ack latency degradation (detect shift up)
/// - Recovery detection (detect shift back down)
/// - Market data feed quality monitoring
#[derive(Debug, Clone)]
#[allow(clippy::struct_excessive_bools)]
pub struct Cusum {
    target: f64,
    slack_upper: f64,
    slack_lower: f64,
    threshold_upper: f64,
    threshold_lower: f64,
    upper: f64,
    lower: f64,
    count: u64,
    min_samples: u64,
    /// Samples needed before a direction is reported: `min_samples`, or 0
    /// when seeded.
    prime_at: u64,
    /// What `reset` restores (0.0 when unseeded).
    seed_upper: f64,
    seed_lower: f64,
    restart_on_alarm: bool,
    // Track whether user explicitly set slack/threshold so
    // reset_with_target knows whether to recompute defaults.
    slack_upper_explicit: bool,
    slack_lower_explicit: bool,
    threshold_upper_explicit: bool,
    threshold_lower_explicit: bool,
}

/// Builder for [`Cusum`].
///
/// # Example
///
/// ```
/// use nexus_stats_core::detection::*;
/// let mut cusum = Cusum::builder(100.0)
///     .slack(5.0)
///     .threshold(50.0)
///     .min_samples(20)
///     .build()
///     .unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct CusumBuilder {
    target: f64,
    slack_upper: Option<f64>,
    slack_lower: Option<f64>,
    threshold_upper: Option<f64>,
    threshold_lower: Option<f64>,
    min_samples: u64,
    seed_upper: Option<f64>,
    seed_lower: Option<f64>,
    restart_on_alarm: bool,
}

impl Cusum {
    /// Creates a builder with the target (expected baseline mean).
    #[inline]
    #[must_use]
    pub fn builder(target: f64) -> CusumBuilder {
        CusumBuilder {
            target,
            slack_upper: None,
            slack_lower: None,
            threshold_upper: None,
            threshold_lower: None,
            min_samples: 0,
            seed_upper: None,
            seed_lower: None,
            restart_on_alarm: false,
        }
    }

    /// Feeds a sample. Returns shift direction once primed.
    ///
    /// Returns `Ok(None)` until `min_samples` have been processed.
    /// After priming, returns `Ok(Some(Direction::Rising))`, `Ok(Some(Direction::Falling))`,
    /// or `Ok(Some(Direction::Neutral))`. A direction keeps being reported
    /// while its sum stays over threshold; see "After an alarm" on the type.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<Direction>, crate::DataError> {
        check_finite!(sample);
        self.count += 1;

        let diff = sample - self.target;

        let s_high = self.upper + diff - self.slack_upper;
        self.upper = s_high.max(0.0);

        let s_low = self.lower - diff - self.slack_lower;
        self.lower = s_low.max(0.0);

        if self.count < self.prime_at {
            return Ok(None);
        }

        let rising = self.upper > self.threshold_upper;
        let falling = self.lower > self.threshold_lower;
        if !(rising || falling) {
            return Ok(Some(Direction::Neutral));
        }
        // Both over: the side further over relative to its own threshold,
        // compared as cross-products (thresholds are positive).
        let report_rising = rising
            && (!falling || self.upper * self.threshold_lower >= self.lower * self.threshold_upper);
        if report_rising {
            if self.restart_on_alarm {
                self.upper = 0.0;
            }
            Ok(Some(Direction::Rising))
        } else {
            if self.restart_on_alarm {
                self.lower = 0.0;
            }
            Ok(Some(Direction::Falling))
        }
    }

    /// Upper cumulative sum (tracks upward drift).
    #[inline]
    #[must_use]
    pub fn upper(&self) -> f64 {
        self.upper
    }

    /// Lower cumulative sum (tracks downward drift).
    #[inline]
    #[must_use]
    pub fn lower(&self) -> f64 {
        self.lower
    }

    /// Number of samples processed since construction or the last reset. A
    /// seed is not a sample.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether directions are being reported: `min_samples` reached, or
    /// seeded.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.prime_at
    }

    /// Returns to the as-built state: count zero and the sums at their seeds
    /// (zero when unseeded). Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.upper = self.seed_upper;
        self.lower = self.seed_lower;
        self.count = 0;
    }

    /// Resets and updates the target mean.
    ///
    /// Seeds were calibrated against the old target, so they are dropped:
    /// the sums start at zero and `min_samples` applies again.
    ///
    /// If slack or threshold were not explicitly set by the user, they are
    /// recomputed from the new target using the defaults (5% and 50% of
    /// target respectively).
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if the target is not finite, or if it is zero
    /// while a threshold is left to its default (which would be zero and fire
    /// on any deviation). The detector is left unchanged on error.
    #[inline]
    pub fn reset_with_target(&mut self, new_target: f64) -> Result<(), crate::ConfigError> {
        if !new_target.is_finite() {
            return Err(crate::ConfigError::Invalid("target must be finite"));
        }
        let slack = CusumBuilder::default_slack(new_target);
        let threshold = CusumBuilder::default_threshold(new_target);
        let default_threshold_in_use =
            !self.threshold_upper_explicit || !self.threshold_lower_explicit;
        if default_threshold_in_use && !crate::math::positive_finite(threshold) {
            return Err(crate::ConfigError::Invalid(
                "default threshold is zero for target 0; set thresholds explicitly",
            ));
        }
        self.target = new_target;
        self.seed_upper = 0.0;
        self.seed_lower = 0.0;
        self.prime_at = self.min_samples;
        self.upper = 0.0;
        self.lower = 0.0;
        self.count = 0;
        if !self.slack_upper_explicit {
            self.slack_upper = slack;
        }
        if !self.slack_lower_explicit {
            self.slack_lower = slack;
        }
        if !self.threshold_upper_explicit {
            self.threshold_upper = threshold;
        }
        if !self.threshold_lower_explicit {
            self.threshold_lower = threshold;
        }
        Ok(())
    }

    /// The target (expected baseline mean).
    #[inline]
    #[must_use]
    pub fn target(&self) -> f64 {
        self.target
    }

    /// Upper slack parameter.
    #[inline]
    #[must_use]
    pub fn slack_upper(&self) -> f64 {
        self.slack_upper
    }

    /// Lower slack parameter.
    #[inline]
    #[must_use]
    pub fn slack_lower(&self) -> f64 {
        self.slack_lower
    }

    /// Upper threshold parameter.
    #[inline]
    #[must_use]
    pub fn threshold_upper(&self) -> f64 {
        self.threshold_upper
    }

    /// Lower threshold parameter.
    #[inline]
    #[must_use]
    pub fn threshold_lower(&self) -> f64 {
        self.threshold_lower
    }

    /// Minimum samples required before detection activates.
    #[inline]
    #[must_use]
    pub fn min_samples(&self) -> u64 {
        self.min_samples
    }

    /// Updates all tuning parameters without resetting cumulative sums or count.
    ///
    /// # Errors
    ///
    /// - Slack values must be non-negative.
    /// - Threshold values must be positive.
    #[inline]
    pub fn reconfigure(
        &mut self,
        target: f64,
        slack_upper: f64,
        slack_lower: f64,
        threshold_upper: f64,
        threshold_lower: f64,
    ) -> Result<(), crate::ConfigError> {
        if !target.is_finite() {
            return Err(crate::ConfigError::Invalid("target must be finite"));
        }
        if !crate::math::nonnegative_finite(slack_upper) {
            return Err(crate::ConfigError::Invalid(
                "slack_upper must be non-negative",
            ));
        }
        if !crate::math::nonnegative_finite(slack_lower) {
            return Err(crate::ConfigError::Invalid(
                "slack_lower must be non-negative",
            ));
        }
        if !crate::math::positive_finite(threshold_upper) {
            return Err(crate::ConfigError::Invalid(
                "threshold_upper must be positive",
            ));
        }
        if !crate::math::positive_finite(threshold_lower) {
            return Err(crate::ConfigError::Invalid(
                "threshold_lower must be positive",
            ));
        }

        self.target = target;
        self.slack_upper = slack_upper;
        self.slack_lower = slack_lower;
        self.threshold_upper = threshold_upper;
        self.threshold_lower = threshold_lower;
        self.slack_upper_explicit = true;
        self.slack_lower_explicit = true;
        self.threshold_upper_explicit = true;
        self.threshold_lower_explicit = true;
        Ok(())
    }
}

impl CusumBuilder {
    #[inline]
    fn default_slack(target: f64) -> f64 {
        // 5% of target magnitude
        target.abs() / 20.0
    }

    #[inline]
    fn default_threshold(target: f64) -> f64 {
        // 50% of target magnitude
        let abs_target = target.abs();
        abs_target / 2.0
    }

    /// Sets both upper and lower slack (symmetric sensitivity).
    ///
    /// Slack controls sensitivity — smaller values detect smaller shifts
    /// but increase false alarm rate. Typically set to half the minimum
    /// shift you want to detect.
    #[inline]
    #[must_use]
    pub fn slack(mut self, slack: f64) -> Self {
        self.slack_upper = Some(slack);
        self.slack_lower = Some(slack);
        self
    }

    /// Sets the upper slack independently.
    ///
    /// Controls sensitivity to upward shifts only.
    #[inline]
    #[must_use]
    pub fn slack_upper(mut self, slack: f64) -> Self {
        self.slack_upper = Some(slack);
        self
    }

    /// Sets the lower slack independently.
    ///
    /// Controls sensitivity to downward shifts only.
    #[inline]
    #[must_use]
    pub fn slack_lower(mut self, slack: f64) -> Self {
        self.slack_lower = Some(slack);
        self
    }

    /// Sets both upper and lower thresholds (symmetric decision boundary).
    ///
    /// Larger thresholds mean fewer false alarms but slower detection.
    #[inline]
    #[must_use]
    pub fn threshold(mut self, threshold: f64) -> Self {
        self.threshold_upper = Some(threshold);
        self.threshold_lower = Some(threshold);
        self
    }

    /// Sets the upper threshold independently.
    ///
    /// Decision boundary for upward shift detection only.
    #[inline]
    #[must_use]
    pub fn threshold_upper(mut self, threshold: f64) -> Self {
        self.threshold_upper = Some(threshold);
        self
    }

    /// Sets the lower threshold independently.
    ///
    /// Decision boundary for downward shift detection only.
    #[inline]
    #[must_use]
    pub fn threshold_lower(mut self, threshold: f64) -> Self {
        self.threshold_lower = Some(threshold);
        self
    }

    /// Minimum samples before detection activates. Default: 0.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Pre-loads the upper cumulative sum from calibration data. Must be
    /// finite and non-negative (the sums never go below zero).
    ///
    /// When seeded, `is_primed()` returns true immediately and `reset()`
    /// returns to the seed.
    #[inline]
    #[must_use]
    pub fn seed_upper(mut self, val: f64) -> Self {
        self.seed_upper = Some(val);
        self
    }

    /// Pre-loads the lower cumulative sum from calibration data. Must be
    /// finite and non-negative.
    ///
    /// When seeded, `is_primed()` returns true immediately and `reset()`
    /// returns to the seed.
    #[inline]
    #[must_use]
    pub fn seed_lower(mut self, val: f64) -> Self {
        self.seed_lower = Some(val);
        self
    }

    /// Zeroes a side's sum when it reports an alarm, so every alarm is a new
    /// detection instead of a state that persists until it drains. Off by
    /// default; see "After an alarm" on [`Cusum`].
    #[inline]
    #[must_use]
    pub fn restart_on_alarm(mut self) -> Self {
        self.restart_on_alarm = true;
        self
    }

    /// Builds the detector.
    ///
    /// # Errors
    ///
    /// - The target must be finite.
    /// - Slack values must be finite and non-negative.
    /// - Threshold values must be finite and positive. With a target of 0
    ///   the default threshold is 0, so thresholds must be set explicitly.
    /// - Seeds must be finite and non-negative.
    #[inline]
    pub fn build(self) -> Result<Cusum, crate::ConfigError> {
        if !self.target.is_finite() {
            return Err(crate::ConfigError::Invalid("target must be finite"));
        }
        let slack_upper_explicit = self.slack_upper.is_some();
        let slack_lower_explicit = self.slack_lower.is_some();
        let threshold_upper_explicit = self.threshold_upper.is_some();
        let threshold_lower_explicit = self.threshold_lower.is_some();

        let slack_upper = self
            .slack_upper
            .unwrap_or_else(|| Self::default_slack(self.target));
        let slack_lower = self
            .slack_lower
            .unwrap_or_else(|| Self::default_slack(self.target));
        let threshold_upper = self
            .threshold_upper
            .unwrap_or_else(|| Self::default_threshold(self.target));
        let threshold_lower = self
            .threshold_lower
            .unwrap_or_else(|| Self::default_threshold(self.target));

        if !crate::math::nonnegative_finite(slack_upper) {
            return Err(crate::ConfigError::Invalid(
                "slack_upper must be non-negative",
            ));
        }
        if !crate::math::nonnegative_finite(slack_lower) {
            return Err(crate::ConfigError::Invalid(
                "slack_lower must be non-negative",
            ));
        }
        #[allow(clippy::float_cmp)]
        if self.target == 0.0 && !(threshold_upper_explicit && threshold_lower_explicit) {
            return Err(crate::ConfigError::Invalid(
                "default threshold is zero for target 0; set thresholds explicitly",
            ));
        }
        if !crate::math::positive_finite(threshold_upper) {
            return Err(crate::ConfigError::Invalid(
                "threshold_upper must be positive",
            ));
        }
        if !crate::math::positive_finite(threshold_lower) {
            return Err(crate::ConfigError::Invalid(
                "threshold_lower must be positive",
            ));
        }

        if self
            .seed_upper
            .is_some_and(|s| !crate::math::nonnegative_finite(s))
            || self
                .seed_lower
                .is_some_and(|s| !crate::math::nonnegative_finite(s))
        {
            return Err(crate::ConfigError::Invalid(
                "seed values must be finite and non-negative",
            ));
        }
        let seeded = self.seed_upper.is_some() || self.seed_lower.is_some();
        let seed_upper = self.seed_upper.unwrap_or(0.0);
        let seed_lower = self.seed_lower.unwrap_or(0.0);

        Ok(Cusum {
            target: self.target,
            slack_upper,
            slack_lower,
            threshold_upper,
            threshold_lower,
            upper: seed_upper,
            lower: seed_lower,
            count: 0,
            min_samples: self.min_samples,
            prime_at: if seeded { 0 } else { self.min_samples },
            seed_upper,
            seed_lower,
            restart_on_alarm: self.restart_on_alarm,
            slack_upper_explicit,
            slack_lower_explicit,
            threshold_upper_explicit,
            threshold_lower_explicit,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn feed(c: &mut Cusum, xs: &[f64]) -> Vec<Option<Direction>> {
        xs.iter().map(|&x| c.update(x).unwrap()).collect()
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn sums_follow_the_clamped_recursion() {
        // target 10, slack 1: upper += x - 11, lower += 9 - x, each floored at 0.
        let mut c = Cusum::builder(10.0)
            .slack(1.0)
            .threshold(5.0)
            .build()
            .unwrap();
        let out = feed(&mut c, &[13.0, 14.0, 12.0, 5.0]);
        // upper: 2, 5, 6, 0.   lower: 0, 0, 0, 4.
        assert_eq!(
            out,
            [
                Some(Direction::Neutral),
                Some(Direction::Neutral), // 5 is not over a threshold of 5
                Some(Direction::Rising),
                Some(Direction::Neutral),
            ]
        );
        assert_eq!((c.upper(), c.lower()), (0.0, 4.0));
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn an_alarm_persists_until_the_sum_drains() {
        let mut c = Cusum::builder(0.0)
            .slack(1.0)
            .threshold(3.0)
            .build()
            .unwrap();
        // upper: 4 (alarm), then on-target samples drain it by the slack.
        let out = feed(&mut c, &[5.0, 0.0, 0.0, 0.0]);
        assert_eq!(
            out,
            [
                Some(Direction::Rising),
                Some(Direction::Neutral), // 3 is not over 3
                Some(Direction::Neutral),
                Some(Direction::Neutral),
            ]
        );
        let mut c = Cusum::builder(0.0)
            .slack(1.0)
            .threshold(3.0)
            .build()
            .unwrap();
        let out = feed(&mut c, &[9.0, 0.0, 0.0]);
        // upper: 8, 7, 6: still reported with no further evidence.
        assert_eq!(out, [Some(Direction::Rising); 3]);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn restart_on_alarm_zeroes_the_alarming_side_only() {
        let mut c = Cusum::builder(0.0)
            .slack(1.0)
            .threshold(3.0)
            .seed_lower(2.0)
            .restart_on_alarm()
            .build()
            .unwrap();
        // upper 8 > 3: reported and zeroed. lower 2 - 9 - 1 floors at 0.
        assert_eq!(c.update(9.0).unwrap(), Some(Direction::Rising));
        assert_eq!(c.upper(), 0.0);
        assert_eq!(c.update(0.0).unwrap(), Some(Direction::Neutral));
        // A fresh excursion is a fresh alarm.
        assert_eq!(c.update(9.0).unwrap(), Some(Direction::Rising));
    }

    #[test]
    fn with_both_sides_over_the_one_further_over_its_threshold_is_reported() {
        // Seed both sides over threshold; the lower is 3x over, the upper 2x.
        let mut c = Cusum::builder(0.0)
            .slack(0.0)
            .threshold_upper(10.0)
            .threshold_lower(4.0)
            .seed_upper(20.0)
            .seed_lower(12.0)
            .build()
            .unwrap();
        assert_eq!(c.update(0.0).unwrap(), Some(Direction::Falling));
        // Swap the ratio: upper 5x over, lower 3x.
        let mut c = Cusum::builder(0.0)
            .slack(0.0)
            .threshold_upper(10.0)
            .threshold_lower(4.0)
            .seed_upper(50.0)
            .seed_lower(12.0)
            .build()
            .unwrap();
        assert_eq!(c.update(0.0).unwrap(), Some(Direction::Rising));
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn seeds_prime_without_counting_and_survive_reset() {
        let mut c = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .min_samples(20)
            .seed_upper(30.0)
            .build()
            .unwrap();
        assert!(c.is_primed());
        assert_eq!(c.count(), 0);
        assert_eq!((c.upper(), c.lower()), (30.0, 0.0));
        // 30 + (130 - 100) - 5 = 55 > 50 on the very first sample.
        assert_eq!(c.update(130.0).unwrap(), Some(Direction::Rising));
        assert_eq!(c.count(), 1);
        c.reset();
        assert_eq!((c.upper(), c.count()), (30.0, 0));
        assert!(c.is_primed());
        // A new target drops the seed and min_samples applies again.
        c.reset_with_target(200.0).unwrap();
        assert_eq!(c.upper(), 0.0);
        assert!(!c.is_primed());
        assert_eq!(c.update(200.0).unwrap(), None);
    }

    #[test]
    fn config_errors_name_the_real_problem() {
        use crate::ConfigError::Invalid;
        assert_eq!(
            Cusum::builder(f64::NAN).build().unwrap_err(),
            Invalid("target must be finite")
        );
        assert_eq!(
            Cusum::builder(0.0).build().unwrap_err(),
            Invalid("default threshold is zero for target 0; set thresholds explicitly")
        );
        assert!(Cusum::builder(0.0).threshold(1.0).build().is_ok());
        for seed in [-1.0, f64::NAN, f64::INFINITY] {
            assert_eq!(
                Cusum::builder(1.0).seed_upper(seed).build().unwrap_err(),
                Invalid("seed values must be finite and non-negative")
            );
            assert_eq!(
                Cusum::builder(1.0).seed_lower(seed).build().unwrap_err(),
                Invalid("seed values must be finite and non-negative")
            );
        }
    }

    // =========================================================================
    // Basic shift detection
    // =========================================================================

    #[test]
    fn detects_upward_shift() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        // Feed normal samples — should not trigger
        for _ in 0..10 {
            let result = cusum.update(100.0).unwrap();
            assert_eq!(result, Some(Direction::Neutral));
        }

        // Feed elevated samples — should eventually trigger upper
        let mut triggered = false;
        for _ in 0..100 {
            if cusum.update(120.0).unwrap() == Some(Direction::Rising) {
                triggered = true;
                break;
            }
        }
        assert!(triggered, "should have detected upward shift");
    }

    #[test]
    fn detects_downward_shift() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        // Feed depressed samples — should eventually trigger lower
        let mut triggered = false;
        for _ in 0..100 {
            if cusum.update(80.0).unwrap() == Some(Direction::Falling) {
                triggered = true;
                break;
            }
        }
        assert!(triggered, "should have detected downward shift");
    }

    #[test]
    fn no_false_positive_at_target() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..1000 {
            assert_eq!(cusum.update(100.0).unwrap(), Some(Direction::Neutral));
        }
    }

    // =========================================================================
    // Priming behavior
    // =========================================================================

    #[test]
    fn returns_none_before_primed() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .min_samples(10)
            .build()
            .unwrap();

        for _ in 0..9 {
            assert_eq!(cusum.update(200.0).unwrap(), None);
        }
        assert!(!cusum.is_primed());

        // 10th sample should be primed
        let result = cusum.update(200.0).unwrap();
        assert!(result.is_some());
        assert!(cusum.is_primed());
    }

    #[test]
    fn primed_immediately_with_zero_min_samples() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        assert_eq!(cusum.min_samples(), 0);
        // First sample should return Some
        assert!(cusum.update(100.0).unwrap().is_some());
    }

    // =========================================================================
    // Reset
    // =========================================================================

    #[test]
    #[allow(clippy::float_cmp)]
    fn reset_clears_state() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..10 {
            let _ = cusum.update(120.0);
        }
        assert!(cusum.upper() > 0.0);
        assert!(cusum.count() > 0);

        cusum.reset();
        assert_eq!(cusum.upper(), 0.0);
        assert_eq!(cusum.lower(), 0.0);
        assert_eq!(cusum.count(), 0);
    }

    #[test]
    fn reset_with_target_updates_defaults() {
        let mut cusum = Cusum::builder(100.0).build().unwrap();

        // Defaults based on 100.0
        let original_slack = cusum.slack_upper();
        let original_threshold = cusum.threshold_upper();

        cusum.reset_with_target(200.0).unwrap();

        // Defaults should scale with new target
        assert!(cusum.slack_upper() > original_slack);
        assert!(cusum.threshold_upper() > original_threshold);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn reset_with_target_preserves_explicit_params() {
        let mut cusum = Cusum::builder(100.0)
            .slack(10.0)
            .threshold(75.0)
            .build()
            .unwrap();

        cusum.reset_with_target(200.0).unwrap();

        // Explicit values should not change
        assert_eq!(cusum.slack_upper(), 10.0);
        assert_eq!(cusum.slack_lower(), 10.0);
        assert_eq!(cusum.threshold_upper(), 75.0);
        assert_eq!(cusum.threshold_lower(), 75.0);
    }

    // =========================================================================
    // Asymmetric slack and threshold
    // =========================================================================

    #[test]
    fn asymmetric_slack() {
        // Tight upper slack (sensitive to increases), loose lower slack
        let mut cusum = Cusum::builder(100.0)
            .slack_upper(2.0)
            .slack_lower(10.0)
            .threshold(50.0)
            .build()
            .unwrap();

        // Small upward deviation should accumulate faster than downward
        for _ in 0..10 {
            let _ = cusum.update(110.0);
        }
        let upper_after = cusum.upper();

        cusum.reset();
        for _ in 0..10 {
            let _ = cusum.update(90.0);
        }
        let lower_after = cusum.lower();

        // Upper should accumulate more (slack_upper=2 eats less of the deviation)
        assert!(
            upper_after > lower_after,
            "upper ({upper_after}) should accumulate faster than lower ({lower_after}) with tighter slack"
        );
    }

    #[test]
    fn asymmetric_threshold() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold_upper(20.0) // trigger fast on increases
            .threshold_lower(500.0) // very slow to trigger on decreases
            .build()
            .unwrap();

        // Upward shift should trigger quickly
        let mut upper_triggered = false;
        for _ in 0..20 {
            if cusum.update(120.0).unwrap() == Some(Direction::Rising) {
                upper_triggered = true;
                break;
            }
        }
        assert!(upper_triggered);

        // Downward shift should NOT trigger with same number of samples
        // deviation per sample: 15, over 20 samples = 300 < 500
        cusum.reset();
        let mut lower_triggered = false;
        for _ in 0..20 {
            if cusum.update(80.0).unwrap() == Some(Direction::Falling) {
                lower_triggered = true;
                break;
            }
        }
        assert!(
            !lower_triggered,
            "lower should not trigger with high threshold"
        );
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn symmetric_slack_sets_both() {
        let cusum = Cusum::builder(100.0).slack(7.5).build().unwrap();

        assert_eq!(cusum.slack_upper(), 7.5);
        assert_eq!(cusum.slack_lower(), 7.5);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn symmetric_threshold_sets_both() {
        let cusum = Cusum::builder(100.0).threshold(42.0).build().unwrap();

        assert_eq!(cusum.threshold_upper(), 42.0);
        assert_eq!(cusum.threshold_lower(), 42.0);
    }

    // =========================================================================
    // Builder validation
    // =========================================================================

    #[test]
    fn rejects_negative_slack_upper() {
        let result = Cusum::builder(100.0).slack_upper(-1.0).build();
        assert!(matches!(
            result,
            Err(crate::ConfigError::Invalid(
                "slack_upper must be non-negative"
            ))
        ));
    }

    #[test]
    fn rejects_negative_slack_lower() {
        let result = Cusum::builder(100.0).slack_lower(-1.0).build();
        assert!(matches!(
            result,
            Err(crate::ConfigError::Invalid(
                "slack_lower must be non-negative"
            ))
        ));
    }

    #[test]
    fn rejects_zero_threshold() {
        let result = Cusum::builder(100.0).threshold(0.0).build();
        assert!(matches!(
            result,
            Err(crate::ConfigError::Invalid(
                "threshold_upper must be positive"
            ))
        ));
    }

    #[test]
    fn rejects_negative_threshold_lower() {
        let result = Cusum::builder(100.0).threshold_lower(-1.0).build();
        assert!(matches!(
            result,
            Err(crate::ConfigError::Invalid(
                "threshold_lower must be positive"
            ))
        ));
    }

    // =========================================================================
    // Edge cases
    // =========================================================================

    #[test]
    fn count_increments() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        assert_eq!(cusum.count(), 0);
        let _ = cusum.update(100.0);
        assert_eq!(cusum.count(), 1);
        let _ = cusum.update(100.0);
        assert_eq!(cusum.count(), 2);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn upper_and_lower_start_at_zero() {
        let cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        assert_eq!(cusum.upper(), 0.0);
        assert_eq!(cusum.lower(), 0.0);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn cusum_at_exactly_slack_no_accumulation() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        // Deviation exactly equals slack — S_high = max(0, 0 + 5 - 5) = 0
        let _ = cusum.update(105.0);
        assert_eq!(cusum.upper(), 0.0);
    }

    // =========================================================================
    // Reconfigure
    // =========================================================================

    #[test]
    #[allow(clippy::float_cmp)]
    fn reconfigure_changes_params_preserves_state() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        // Accumulate some state
        for _ in 0..5 {
            let _ = cusum.update(120.0);
        }
        let upper_before = cusum.upper();
        let count_before = cusum.count();
        assert!(upper_before > 0.0);

        // Reconfigure
        cusum.reconfigure(200.0, 10.0, 10.0, 100.0, 100.0).unwrap();

        // Parameters changed
        assert_eq!(cusum.target(), 200.0);
        assert_eq!(cusum.slack_upper(), 10.0);
        assert_eq!(cusum.slack_lower(), 10.0);
        assert_eq!(cusum.threshold_upper(), 100.0);
        assert_eq!(cusum.threshold_lower(), 100.0);

        // State preserved
        assert_eq!(cusum.upper(), upper_before);
        assert_eq!(cusum.count(), count_before);
    }

    #[test]
    fn reconfigure_validates() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        assert!(cusum.reconfigure(100.0, -1.0, 0.0, 1.0, 1.0).is_err());
        assert!(cusum.reconfigure(100.0, 0.0, -1.0, 1.0, 1.0).is_err());
        assert!(cusum.reconfigure(100.0, 0.0, 0.0, 0.0, 1.0).is_err());
        assert!(cusum.reconfigure(100.0, 0.0, 0.0, 1.0, 0.0).is_err());
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut cusum = Cusum::builder(100.0)
            .slack(5.0)
            .threshold(50.0)
            .build()
            .unwrap();

        assert_eq!(
            cusum.update(f64::NAN).unwrap_err(),
            crate::DataError::NotANumber
        );
        assert_eq!(
            cusum.update(f64::INFINITY).unwrap_err(),
            crate::DataError::Infinite
        );
        assert_eq!(
            cusum.update(f64::NEG_INFINITY).unwrap_err(),
            crate::DataError::Infinite
        );
        // State unchanged after rejected inputs
        assert_eq!(cusum.count(), 0);
    }
}
