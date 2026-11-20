// Checking m2 == 0.0 is intentional: zero variance means all samples
// are identical, and correlation is undefined. This is exact, not approximate.
#![allow(clippy::float_cmp)]

// Online Autocorrelation at Fixed Lag
//
// Maintains a circular buffer of size `lag` for delayed values, plus
// Welford-style accumulators for variance and the cross-moment
// between x(t) and x(t-lag).
//
// r(k) = cross_m / m2 — the 1/N normalization cancels.

use nexus_stats_core::statistics::Welford;
use nexus_stats_core::storage::Ring;

/// Online autocorrelation at a configurable lag.
///
/// Maintains a circular buffer of previous values and computes
/// the autocorrelation coefficient between x(t) and x(t-lag) using
/// Welford-style running accumulators.
///
/// # Use Cases
/// - "Is this signal trending or mean-reverting?" (positive vs negative lag-1)
/// - Detecting periodicity at a known lag
/// - Stationarity monitoring
///
/// # Complexity
/// - O(1) per update, heap-allocated circular buffer.
///
/// # Examples
///
/// ```
/// use nexus_stats_detection::signal::Autocorrelation;
///
/// // Strongly periodic signal: lag-1 autocorrelation of alternating values
/// let mut ac = Autocorrelation::builder().lag(1).build().unwrap();
/// for i in 0..200u64 {
///     ac.update(if i % 2 == 0 { 1.0 } else { -1.0 }).unwrap();
/// }
/// let r = ac.correlation().unwrap();
/// assert!(r < -0.9, "alternating signal should have negative lag-1 autocorrelation");
/// ```
#[derive(Debug, Clone)]
pub struct Autocorrelation {
    ring: Ring<f64>,
    lag: usize,
    /// Running mean and M2 of the stream (the shared kernel).
    stats: Welford,
    cross_m: f64,
}

/// Builder for [`Autocorrelation`].
#[derive(Debug, Clone)]
pub struct AutocorrelationBuilder {
    lag: Option<usize>,
}

impl Autocorrelation {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> AutocorrelationBuilder {
        AutocorrelationBuilder { lag: None }
    }

    /// Feeds a sample.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(sample);
        self.stats.update(sample);
        // A sample has been fed, so the mean exists; the fallback is never
        // taken.
        let mean = self.stats.mean().unwrap_or(sample);

        // Cross-moment: accumulate (x_new - mean)(x_lagged - mean) once the
        // ring is full, i.e. from the (lag + 1)-th observation. The slot
        // `replace` hands back is exactly the sample from `lag` steps ago.
        let was_full = self.ring.is_full();
        let x_lagged = self.ring.replace(sample);
        if was_full {
            self.cross_m += (sample - mean) * (x_lagged - mean);
        }
        Ok(())
    }

    /// Autocorrelation coefficient in \[-1, 1\], or `None` if fewer
    /// than `lag + 2` samples.
    ///
    /// Defined as γ(k)/γ(0) where γ(k) is the autocovariance at lag k
    /// and γ(0) is the variance. Returns `None` if variance is zero.
    #[inline]
    #[must_use]
    pub fn correlation(&self) -> Option<f64> {
        let count = self.stats.count();
        if count < (self.lag as u64 + 2) {
            return None;
        }
        let m2 = self.stats.m2();
        if m2 == 0.0 {
            return None;
        }
        // cross_m accumulated over (count - lag) pairs,
        // m2 accumulated over (count - 1) samples.
        // Normalize both to get comparable per-observation values.
        let n_pairs = (count - self.lag as u64) as f64;
        let n_samples = (count - 1) as f64;
        Some(self.cross_m * n_samples / (m2 * n_pairs))
    }

    /// Raw autocovariance at the configured lag, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn covariance(&self) -> Option<f64> {
        let count = self.stats.count();
        if count < (self.lag as u64 + 2) {
            return None;
        }
        let n_pairs = (count - self.lag as u64) as f64;
        Some(self.cross_m / n_pairs)
    }

    /// The configured lag.
    #[inline]
    #[must_use]
    pub fn lag(&self) -> usize {
        self.lag
    }

    /// Number of observations processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.stats.count()
    }

    /// Whether enough data has been collected (>= lag + 2).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.stats.count() >= self.lag as u64 + 2
    }

    /// Resets to empty state. Configuration and buffer allocation preserved.
    #[inline]
    pub fn reset(&mut self) {
        self.ring.clear(0.0);
        self.stats.reset();
        self.cross_m = 0.0;
    }
}

impl AutocorrelationBuilder {
    /// Sets the lag (required, >= 1).
    #[inline]
    #[must_use]
    pub fn lag(mut self, lag: usize) -> Self {
        self.lag = Some(lag);
        self
    }

    /// Builds the autocorrelation tracker.
    ///
    /// # Errors
    /// Returns `ConfigError` if lag is missing or < 1.
    #[inline]
    pub fn build(self) -> Result<Autocorrelation, nexus_stats_core::ConfigError> {
        let lag = self
            .lag
            .ok_or(nexus_stats_core::ConfigError::Missing("lag"))?;
        if lag < 1 {
            return Err(nexus_stats_core::ConfigError::Invalid("lag must be >= 1"));
        }
        Ok(Autocorrelation {
            ring: Ring::new(lag, 0.0)?,
            lag,
            stats: Welford::new(),
            cross_m: 0.0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alternating_negative_lag1() {
        let mut ac = Autocorrelation::builder().lag(1).build().unwrap();
        for i in 0..1000u64 {
            ac.update(if i % 2 == 0 { 1.0 } else { -1.0 }).unwrap();
        }
        let r = ac.correlation().unwrap();
        assert!(r < -0.9, "alternating should be strongly negative, got {r}");
    }

    #[test]
    fn trending_positive_lag1() {
        let mut ac = Autocorrelation::builder().lag(1).build().unwrap();
        for i in 0..1000u64 {
            ac.update(i as f64).unwrap();
        }
        let r = ac.correlation().unwrap();
        assert!(
            r > 0.9,
            "monotone trend should have positive lag-1, got {r}"
        );
    }

    #[test]
    fn lag10_periodic() {
        let mut ac = Autocorrelation::builder().lag(10).build().unwrap();
        for i in 0..2000u64 {
            ac.update((i % 10) as f64).unwrap();
        }
        let r = ac.correlation().unwrap();
        assert!(
            r > 0.8,
            "period-10 signal should correlate at lag 10, got {r}"
        );
    }

    #[test]
    fn constant_input_zero_variance() {
        let mut ac = Autocorrelation::builder().lag(1).build().unwrap();
        for _ in 0..100 {
            ac.update(42.0).unwrap();
        }
        assert!(ac.correlation().is_none());
    }

    #[test]
    fn not_primed_until_lag_plus_2() {
        let mut ac = Autocorrelation::builder().lag(5).build().unwrap();
        for i in 0..6 {
            ac.update(i as f64).unwrap();
            assert!(!ac.is_primed(), "should not be primed at count {}", i + 1);
        }
        ac.update(6.0).unwrap();
        assert!(ac.is_primed(), "should be primed at count 7 (lag+2)");
    }

    #[test]
    fn covariance_sign_matches_correlation() {
        let mut ac = Autocorrelation::builder().lag(1).build().unwrap();
        for i in 0..500u64 {
            ac.update(i as f64).unwrap();
        }
        let corr = ac.correlation().unwrap();
        let cov = ac.covariance().unwrap();
        assert!(
            corr.signum() == cov.signum(),
            "corr={corr}, cov={cov} — signs should match"
        );
    }

    #[test]
    fn reset_clears_state() {
        let mut ac = Autocorrelation::builder().lag(1).build().unwrap();
        for i in 0..100 {
            ac.update(i as f64).unwrap();
        }
        ac.reset();
        assert_eq!(ac.count(), 0);
        assert!(!ac.is_primed());
        assert!(ac.correlation().is_none());
    }

    #[test]
    fn lag_accessor() {
        let ac = Autocorrelation::builder().lag(7).build().unwrap();
        assert_eq!(ac.lag(), 7);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut ac = Autocorrelation::builder().lag(1).build().unwrap();
        assert_eq!(
            ac.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            ac.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(ac.count(), 0);
    }

    #[test]
    fn builder_requires_lag() {
        let result = Autocorrelation::builder().build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("lag"))
        ));
    }

    #[test]
    fn builder_rejects_zero_lag() {
        let result = Autocorrelation::builder().lag(0).build();
        assert!(result.is_err());
    }

    /// `reset` leaves no residue in the lag ring or the moments.
    #[test]
    fn reset_then_replay_matches() {
        let mut ac = Autocorrelation::builder().lag(3).build().unwrap();
        let stream = [1.0, 2.0, 3.0, 2.0, 1.0, 2.0, 3.0, 2.0, 1.0, 2.0, 3.0, 2.0];
        let run = |ac: &mut Autocorrelation| -> Vec<Option<u64>> {
            stream
                .iter()
                .map(|&x| {
                    ac.update(x).unwrap();
                    ac.correlation().map(f64::to_bits)
                })
                .collect()
        };
        let first = run(&mut ac);
        ac.reset();
        assert_eq!(ac.count(), 0);
        let second = run(&mut ac);
        assert_eq!(first, second);
    }
}
