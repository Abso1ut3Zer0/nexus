//! Hampel filter — three-zone outlier handling.

use crate::WindowedMedian;
use nexus_stats_core::math::MulAdd;

/// Hampel filter — soft outlier filter with three zones.
///
/// Uses a rolling median and MAD (Median Absolute Deviation) to
/// classify each observation:
///
/// - `|z| < inner_threshold`: pass through unchanged
/// - `inner_threshold < |z| < outer_threshold`: Winsorize (shrink toward median)
/// - `|z| > outer_threshold`: reject (replace with median)
///
/// Where `z = (x - median) / (mad_scale * MAD)` is the modified z-score.
///
/// # Use Cases
///
/// - Spread smoothing — remove tick spikes without losing legitimate moves
/// - Sensor data cleaning — three zones give finer control than hard rejection
#[derive(Debug, Clone)]
pub struct Hampel {
    median: WindowedMedian<f64>,
    inner_threshold: f64,
    outer_threshold: f64,
    mad_scale: f64,
    value: f64,
    count: u64,
}

/// Builder for [`Hampel`].
#[derive(Debug, Clone)]
pub struct HampelBuilder {
    window_size: usize,
    inner_threshold: f64,
    outer_threshold: f64,
    mad_scale: f64,
}

impl Hampel {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> HampelBuilder {
        HampelBuilder {
            window_size: 21,
            inner_threshold: 2.0,
            outer_threshold: 3.5,
            mad_scale: 1.4826, // MAD → σ for Gaussian
        }
    }

    /// Feed an observation. Returns the filtered value.
    ///
    /// Before the window is primed, observations pass through unchanged.
    ///
    /// # Errors
    ///
    /// Returns `DataError` if the input is NaN or infinite.
    #[inline]
    pub fn update(&mut self, x: f64) -> Result<f64, nexus_stats_core::DataError> {
        check_finite!(x);

        self.median.update(x)?;
        self.count += 1;

        // Before primed, pass through
        if !self.median.is_primed() {
            self.value = x;
            return Ok(x);
        }

        // Both are `None` only for an empty window, which `is_primed` rules out.
        let (Some(median), Some(mad)) = (self.median.median(), self.median.mad()) else {
            self.value = x;
            return Ok(x);
        };
        let sigma = self.mad_scale * mad;

        // If MAD is zero (constant window), pass through
        if sigma < f64::EPSILON {
            self.value = x;
            return Ok(x);
        }

        let z = (x - median).abs() / sigma;

        let filtered = if z <= self.inner_threshold {
            // Pass through — normal observation
            x
        } else if z <= self.outer_threshold {
            // Winsorize — shrink toward median
            // Linear interpolation between x (at inner) and median (at outer)
            let t = (z - self.inner_threshold) / (self.outer_threshold - self.inner_threshold);
            (median - x).fma(t, x)
        } else {
            // Reject — replace with median
            median
        };

        self.value = filtered;
        Ok(filtered)
    }

    /// Current filtered value, or `None` if no observations have been fed.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<f64> {
        if self.count > 0 {
            Some(self.value)
        } else {
            None
        }
    }

    /// Current median of the window.
    #[inline]
    #[must_use]
    pub fn median(&self) -> Option<f64> {
        self.median.median()
    }

    /// Whether the window is fully populated.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.median.is_primed()
    }

    /// Number of observations processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Reset to initial state.
    #[inline]
    pub fn reset(&mut self) {
        self.median.reset();
        self.value = 0.0;
        self.count = 0;
    }
}

impl HampelBuilder {
    /// Sliding window size for the median. Default: 21.
    #[inline]
    #[must_use]
    pub fn window_size(mut self, n: usize) -> Self {
        self.window_size = n;
        self
    }

    /// Inner threshold — observations within this z-score pass unchanged.
    /// Default: 2.0.
    #[inline]
    #[must_use]
    pub fn inner_threshold(mut self, t: f64) -> Self {
        self.inner_threshold = t;
        self
    }

    /// Outer threshold — observations beyond this z-score are replaced with
    /// the median. Between inner and outer, values are Winsorized. Default: 3.5.
    #[inline]
    #[must_use]
    pub fn outer_threshold(mut self, t: f64) -> Self {
        self.outer_threshold = t;
        self
    }

    /// Scale factor for MAD → σ conversion. Default: 1.4826 (Gaussian).
    #[inline]
    #[must_use]
    pub fn mad_scale(mut self, s: f64) -> Self {
        self.mad_scale = s;
        self
    }

    /// Build the Hampel filter.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if thresholds are invalid.
    #[inline]
    pub fn build(self) -> Result<Hampel, nexus_stats_core::ConfigError> {
        if self.inner_threshold <= 0.0 || !self.inner_threshold.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "inner_threshold must be positive and finite",
            ));
        }
        if self.outer_threshold <= self.inner_threshold || !self.outer_threshold.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "outer_threshold must be greater than inner_threshold and finite",
            ));
        }
        if self.mad_scale <= 0.0 || !self.mad_scale.is_finite() {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "mad_scale must be positive and finite",
            ));
        }
        if self.window_size < 3 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "window_size must be at least 3",
            ));
        }

        Ok(Hampel {
            median: WindowedMedian::<f64>::new(self.window_size)?,
            inner_threshold: self.inner_threshold,
            outer_threshold: self.outer_threshold,
            mad_scale: self.mad_scale,
            value: 0.0,
            count: 0,
        })
    }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    fn basic_hampel() -> Hampel {
        Hampel::builder().window_size(5).build().unwrap()
    }

    #[test]
    fn clean_signal_passes_through() {
        let mut h = basic_hampel();
        // Constant signal — all within inner threshold
        for _ in 0..20 {
            let v = h.update(10.0).unwrap();
            if h.is_primed() {
                assert!(
                    (v - 10.0).abs() < 1e-10,
                    "clean signal should pass through, got {v}"
                );
            }
        }
    }

    #[test]
    fn large_outlier_replaced_with_median() {
        let mut h = basic_hampel();
        // Fill window with slight variance so MAD > 0
        for &v in &[9.5, 10.0, 10.5, 10.0, 9.5] {
            h.update(v).unwrap();
        }
        // Large outlier — should be replaced with median (~10.0)
        let v = h.update(1000.0).unwrap();
        let median = h.median().unwrap();
        assert!(
            (v - median).abs() < 1.0,
            "large outlier should be replaced with median ({median}), got {v}"
        );
    }

    #[test]
    fn moderate_outlier_is_winsorized() {
        let mut h = Hampel::builder()
            .window_size(5)
            .inner_threshold(1.0)
            .outer_threshold(5.0)
            .build()
            .unwrap();

        // Fill with constant data
        for _ in 0..5 {
            h.update(10.0).unwrap();
        }

        // Moderate deviation — between inner and outer
        // Need MAD > 0 for z-score to be meaningful. Add some variance.
        let mut h2 = Hampel::builder()
            .window_size(5)
            .inner_threshold(1.0)
            .outer_threshold(5.0)
            .build()
            .unwrap();
        for &v in &[9.0, 10.0, 11.0, 10.0, 9.0] {
            h2.update(v).unwrap();
        }
        // Now feed a value that's between thresholds
        let result = h2.update(16.0).unwrap();
        // Should be shrunk toward median but not replaced entirely
        assert!(
            result < 16.0,
            "should be Winsorized below 16.0, got {result}"
        );
        let median = h2.median().unwrap();
        assert!(
            result > median,
            "should be above median {median}, got {result}"
        );
    }

    #[test]
    fn step_change_eventually_tracked() {
        let mut h = basic_hampel();
        // Start at 10
        for _ in 0..20 {
            h.update(10.0).unwrap();
        }
        // Step change to 20 — median should shift
        for _ in 0..20 {
            h.update(20.0).unwrap();
        }
        let v = h.update(20.0).unwrap();
        assert!(
            (v - 20.0).abs() < 1.0,
            "after step change, should track new level, got {v}"
        );
    }

    #[test]
    fn priming_behavior() {
        let mut h = Hampel::builder().window_size(5).build().unwrap();
        assert!(!h.is_primed());
        for i in 0..5 {
            h.update(i as f64).unwrap();
        }
        assert!(h.is_primed());
    }

    #[test]
    fn reset_clears_state() {
        let mut h = basic_hampel();
        for _ in 0..10 {
            h.update(42.0).unwrap();
        }
        h.reset();
        assert_eq!(h.count(), 0);
        assert!(!h.is_primed());
    }

    #[test]
    fn rejects_invalid_config() {
        assert!(Hampel::builder().inner_threshold(0.0).build().is_err());
        assert!(
            Hampel::builder()
                .inner_threshold(3.0)
                .outer_threshold(2.0)
                .build()
                .is_err()
        );
        assert!(Hampel::builder().window_size(2).build().is_err());
    }
}
