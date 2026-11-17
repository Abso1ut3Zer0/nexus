use crate::storage::Ring;

/// Rolling Hurst exponent via rescaled range (R/S) analysis.
///
/// Maintains a window of observations and computes the Hurst exponent
/// on the full window. H < 0.5 indicates mean reversion, H > 0.5
/// indicates trending/persistence, H ≈ 0.5 indicates a random walk.
///
/// This is intended for bucket-level updates (e.g., per-bar), not
/// tick-by-tick data, since R/S analysis requires a reasonable
/// sample size to be meaningful. `update` is O(1); the `hurst()` query
/// is O(window).
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::Hurst;
///
/// let mut h = Hurst::builder()
///     .window_size(100)
///     .build().unwrap();
///
/// // Feed trending data
/// for i in 0..200 {
///     h.update(i as f64).unwrap();
/// }
///
/// if let Some(hurst) = h.hurst() {
///     // Trending data should have H > 0.5
///     assert!(hurst > 0.5);
/// }
/// ```
#[derive(Debug, Clone)]
pub struct Hurst {
    window: Ring<f64>,
    count: u64,
}

/// Builder for [`Hurst`].
#[derive(Debug, Clone)]
pub struct HurstBuilder {
    window_size: Option<usize>,
}

impl Hurst {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> HurstBuilder {
        HurstBuilder { window_size: None }
    }

    /// Feed a value (typically a return or price level).
    ///
    /// # Errors
    ///
    /// Returns `DataError` if the value is NaN or infinite.
    #[inline]
    pub fn update(&mut self, value: f64) -> Result<(), crate::DataError> {
        check_finite!(value);

        self.count += 1;
        self.window.push(value);

        Ok(())
    }

    /// Compute the Hurst exponent on the current window.
    ///
    /// Returns `None` if the window has fewer than 20 observations
    /// or if the standard deviation is zero.
    #[must_use]
    pub fn hurst(&self) -> Option<f64> {
        if !self.window.is_full() {
            return None;
        }
        let n = self.window.capacity();

        // Compute mean
        let sum: f64 = self.window.iter().sum();
        let mean = sum / n as f64;

        // Compute standard deviation
        let var: f64 = self
            .window
            .iter()
            .map(|x| {
                let d = x - mean;
                d * d
            })
            .sum::<f64>()
            / n as f64;

        if var <= 0.0 {
            return None;
        }
        let std_dev = crate::math::sqrt(var);

        // Cumulative deviations from mean
        let mut cum_dev = 0.0;
        let mut max_cum = f64::NEG_INFINITY;
        let mut min_cum = f64::INFINITY;

        for &x in self.window.iter() {
            cum_dev += x - mean;
            if cum_dev > max_cum {
                max_cum = cum_dev;
            }
            if cum_dev < min_cum {
                min_cum = cum_dev;
            }
        }

        let range = max_cum - min_cum;
        if range <= 0.0 {
            return None;
        }

        // R/S = range / std_dev
        // H ≈ log(R/S) / log(n)
        let rs = range / std_dev;
        let h = crate::math::ln(rs) / crate::math::ln(n as f64);

        Some(h)
    }

    /// Whether the series appears mean-reverting (H < 0.5).
    #[inline]
    #[must_use]
    pub fn is_mean_reverting(&self) -> bool {
        self.hurst().is_some_and(|h| h < 0.5)
    }

    /// Whether the series appears trending (H > 0.5).
    #[inline]
    #[must_use]
    pub fn is_trending(&self) -> bool {
        self.hurst().is_some_and(|h| h > 0.5)
    }

    /// Total number of observations fed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the window is full enough for computation.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.window.is_full()
    }

    /// Reset all state.
    pub fn reset(&mut self) {
        self.window.clear(0.0);
        self.count = 0;
    }
}

impl HurstBuilder {
    /// Rolling window size. Default: 100.
    #[inline]
    #[must_use]
    pub fn window_size(mut self, size: usize) -> Self {
        self.window_size = Some(size);
        self
    }

    /// Build the Hurst estimator.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if window_size < 20 (minimum for
    /// meaningful R/S analysis).
    #[inline]
    pub fn build(self) -> Result<Hurst, crate::ConfigError> {
        let window_size = self.window_size.unwrap_or(100);
        if window_size < 20 {
            return Err(crate::ConfigError::Invalid(
                "window_size must be >= 20 for meaningful R/S analysis",
            ));
        }
        Ok(Hurst {
            window: Ring::new(window_size, 0.0)?,
            count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alternating_series_low_hurst() {
        let mut h = Hurst::builder().window_size(200).build().unwrap();

        // Strongly mean-reverting: +1, -1, +1, -1, ...
        for i in 0..200 {
            let val = if i % 2 == 0 { 1.0 } else { -1.0 };
            h.update(val).unwrap();
        }

        let hurst = h.hurst().unwrap();
        assert!(
            hurst < 0.5,
            "alternating series should have H < 0.5, got {hurst}"
        );
        assert!(h.is_mean_reverting());
    }

    #[test]
    fn trending_series_high_hurst() {
        let mut h = Hurst::builder().window_size(200).build().unwrap();

        // Strongly trending: monotonically increasing
        for i in 0..200 {
            h.update(i as f64).unwrap();
        }

        let hurst = h.hurst().unwrap();
        assert!(
            hurst > 0.5,
            "trending series should have H > 0.5, got {hurst}"
        );
        assert!(h.is_trending());
    }

    #[test]
    fn primes_at_the_configured_window_not_at_a_fixed_count() {
        let mut h = Hurst::builder().window_size(20).build().unwrap();
        for i in 0..19 {
            h.update(i as f64).unwrap();
        }
        assert!(!h.is_primed());
        assert!(h.hurst().is_none());
        h.update(19.0).unwrap();
        assert!(h.is_primed());
        assert!(h.hurst().is_some());

        let mut wide = Hurst::builder().window_size(100).build().unwrap();
        for i in 0..20 {
            wide.update(i as f64).unwrap();
        }
        assert!(!wide.is_primed(), "a 100-sample window is not primed at 20");
    }

    #[test]
    fn reset_clears_state() {
        let mut h = Hurst::builder().window_size(100).build().unwrap();
        for i in 0..50 {
            h.update(i as f64).unwrap();
        }
        h.reset();
        assert_eq!(h.count(), 0);
        assert!(!h.is_primed());
    }

    #[test]
    fn nan_rejected() {
        let mut h = Hurst::builder().window_size(100).build().unwrap();
        assert!(h.update(f64::NAN).is_err());
    }

    #[test]
    fn inf_rejected() {
        let mut h = Hurst::builder().window_size(100).build().unwrap();
        assert!(h.update(f64::INFINITY).is_err());
    }

    #[test]
    fn constant_series_no_hurst() {
        let mut h = Hurst::builder().window_size(50).build().unwrap();
        for _ in 0..50 {
            h.update(5.0).unwrap();
        }
        // Zero variance → None
        assert!(h.hurst().is_none());
    }
}
