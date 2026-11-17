use alloc::boxed::Box;
use alloc::vec;

/// Two-scale realized variance — noise-corrected volatility estimator.
///
/// Combines high-frequency (all-tick) and subsampled (every K ticks)
/// realized variance to cancel microstructure noise bias.
///
/// TSRV = `[Y,Y]^{(avg)}` - (n̄ / n) · `[Y,Y]^{(all)}`
///
/// where `[Y,Y]^{(avg)}` = Σ(K-tick returns²) / K and n̄ = n_slow / K.
///
/// Zhang, Mykland, Aït-Sahalia (2005).
///
/// # Parameters
///
/// - `k` — subsampling frequency (typically 5–20)
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::TwoScaleRv;
///
/// let mut tsrv = TwoScaleRv::builder()
///     .k(5)
///     .min_samples(20)
///     .build()
///     .unwrap();
///
/// for i in 0..100 {
///     tsrv.update(100.0 + (i as f64) * 0.01).unwrap();
/// }
/// assert!(tsrv.realized_variance().is_some());
/// ```
#[derive(Debug, Clone)]
pub struct TwoScaleRv {
    fast_sum_sq: f64,
    slow_sum_sq: f64,
    buffer: Box<[f64]>,
    write_idx: usize,
    filled: bool,
    prev_price: f64,
    k: usize,
    n_slow: u64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`TwoScaleRv`].
#[derive(Debug, Clone)]
pub struct TwoScaleRvBuilder {
    k: Option<usize>,
    min_samples: Option<u64>,
}

impl TwoScaleRv {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> TwoScaleRvBuilder {
        TwoScaleRvBuilder {
            k: Option::None,
            min_samples: Option::None,
        }
    }

    /// Feeds a trade price.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the price is NaN, or
    /// `DataError::Infinite` if the price is infinite.
    #[inline]
    pub fn update(&mut self, price: f64) -> Result<(), crate::DataError> {
        check_finite!(price);
        self.count += 1;

        if self.count >= 2 {
            let fast_diff = price - self.prev_price;
            self.fast_sum_sq += fast_diff * fast_diff;
        }

        let oldest = if self.filled {
            Some(self.buffer[self.write_idx])
        } else {
            None
        };
        self.buffer[self.write_idx] = price;

        if let Some(old_price) = oldest {
            let slow_diff = price - old_price;
            self.slow_sum_sq += slow_diff * slow_diff;
            self.n_slow += 1;
        }

        self.write_idx += 1;
        if self.write_idx == self.k {
            self.write_idx = 0;
            self.filled = true;
        }

        self.prev_price = price;
        Ok(())
    }

    /// Noise-corrected two-scale realized variance.
    ///
    /// Returns `None` if not primed.
    #[inline]
    #[must_use]
    pub fn realized_variance(&self) -> Option<f64> {
        if !self.is_primed() {
            return Option::None;
        }
        let n_fast = self.count - 1;
        if n_fast == 0 || self.n_slow == 0 {
            return Option::None;
        }

        let n_bar = self.n_slow as f64 / self.k as f64;
        let correction = n_bar / n_fast as f64;
        let tsrv = crate::math::MulAdd::fma(
            -correction,
            self.fast_sum_sq,
            self.slow_sum_sq / self.k as f64,
        );

        Option::Some(if tsrv > 0.0 { tsrv } else { 0.0 })
    }

    /// Noise-corrected realized volatility: `√(TSRV)`.
    ///
    /// Returns `None` if not primed.
    #[inline]
    #[must_use]
    pub fn realized_volatility(&self) -> Option<f64> {
        self.realized_variance().map(crate::math::sqrt)
    }

    /// Raw all-tick realized variance (noisy, unnormalized).
    ///
    /// Returns the sum of squared one-tick returns: `[Y,Y]^{(all)}`.
    /// Returns `None` if not primed.
    #[inline]
    #[must_use]
    pub fn fast_rv(&self) -> Option<f64> {
        if !self.is_primed() || self.count < 2 {
            return Option::None;
        }
        Option::Some(self.fast_sum_sq)
    }

    /// Estimated noise variance per observation: `([Y,Y]^{(all)} - TSRV) / 2n`.
    ///
    /// Returns `None` if not primed.
    #[inline]
    #[must_use]
    pub fn noise_variance(&self) -> Option<f64> {
        let fast = self.fast_rv()?;
        let tsrv = self.realized_variance()?;
        let n_fast = (self.count - 1) as f64;
        let noise = (fast - tsrv) / (2.0 * n_fast);
        Option::Some(if noise > 0.0 { noise } else { 0.0 })
    }

    /// Number of prices seen.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough samples have been observed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to empty state. Parameters and allocation preserved.
    #[inline]
    pub fn reset(&mut self) {
        self.fast_sum_sq = 0.0;
        self.slow_sum_sq = 0.0;
        self.buffer.fill(0.0);
        self.write_idx = 0;
        self.filled = false;
        self.prev_price = 0.0;
        self.n_slow = 0;
        self.count = 0;
    }
}

impl TwoScaleRvBuilder {
    /// Subsampling frequency (required, >= 2).
    #[inline]
    #[must_use]
    pub fn k(mut self, k: usize) -> Self {
        self.k = Option::Some(k);
        self
    }

    /// Minimum prices before results are valid. Default: `k * 10`.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = Option::Some(min);
        self
    }

    /// Builds the two-scale RV estimator.
    ///
    /// # Errors
    ///
    /// - `k` must have been set and be >= 2.
    #[inline]
    pub fn build(self) -> Result<TwoScaleRv, crate::ConfigError> {
        let k = self.k.ok_or(crate::ConfigError::Missing("k"))?;
        if k < 2 {
            return Err(crate::ConfigError::Invalid("TwoScaleRv k must be >= 2"));
        }

        let min_samples = self.min_samples.unwrap_or((k * 10) as u64);

        Ok(TwoScaleRv {
            fast_sum_sq: 0.0,
            slow_sum_sq: 0.0,
            buffer: vec![0.0; k].into_boxed_slice(),
            write_idx: 0,
            filled: false,
            prev_price: 0.0,
            k,
            n_slow: 0,
            count: 0,
            min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn white_noise_correction() {
        let mut tsrv = TwoScaleRv::builder().k(5).min_samples(10).build().unwrap();

        // Noisy prices: smooth trend + noise
        for i in 0..500 {
            let noise = if i % 3 == 0 {
                0.1
            } else if i % 3 == 1 {
                -0.1
            } else {
                0.0
            };
            tsrv.update((i as f64).mul_add(0.001, 100.0) + noise)
                .unwrap();
        }

        let fast = tsrv.fast_rv().unwrap();
        let corrected = tsrv.realized_variance().unwrap();
        assert!(
            corrected < fast,
            "TSRV ({corrected}) should be less than fast RV ({fast}) for noisy data"
        );
    }

    #[test]
    fn clean_signal_produces_valid_result() {
        let mut tsrv = TwoScaleRv::builder().k(5).min_samples(10).build().unwrap();

        for i in 0..200 {
            tsrv.update((i as f64).mul_add(0.01, 100.0)).unwrap();
        }

        let corrected = tsrv.realized_variance().unwrap();
        assert!(
            corrected >= 0.0,
            "TSRV should be non-negative for clean data, got {corrected}"
        );
        let vol = tsrv.realized_volatility().unwrap();
        assert!(vol >= 0.0, "volatility should be non-negative, got {vol}");
    }

    #[test]
    fn noise_variance_positive() {
        let mut tsrv = TwoScaleRv::builder().k(5).min_samples(10).build().unwrap();

        for i in 0..500 {
            let noise = if i % 2 == 0 { 0.1 } else { -0.1 };
            tsrv.update(100.0 + noise).unwrap();
        }

        let nv = tsrv.noise_variance().unwrap();
        assert!(nv >= 0.0, "noise variance should be non-negative, got {nv}");
    }

    #[test]
    fn volatility_is_sqrt() {
        let mut tsrv = TwoScaleRv::builder().k(5).min_samples(10).build().unwrap();

        for i in 0..200 {
            tsrv.update((i as f64).mul_add(0.01, 100.0)).unwrap();
        }

        let var = tsrv.realized_variance().unwrap();
        let vol = tsrv.realized_volatility().unwrap();
        assert!(
            (vol * vol - var).abs() < 1e-10,
            "vol² ({}) should equal var ({var})",
            vol * vol
        );
    }

    #[test]
    fn k_sensitivity() {
        let prices: alloc::vec::Vec<f64> = (0..500)
            .map(|i| {
                let noise = if i % 2 == 0 { 0.1 } else { -0.1 };
                (i as f64).mul_add(0.001, 100.0) + noise
            })
            .collect();

        let mut tsrv_small = TwoScaleRv::builder().k(3).min_samples(10).build().unwrap();
        let mut tsrv_large = TwoScaleRv::builder().k(10).min_samples(10).build().unwrap();

        for &p in &prices {
            tsrv_small.update(p).unwrap();
            tsrv_large.update(p).unwrap();
        }

        // Both should produce valid results
        assert!(tsrv_small.realized_variance().is_some());
        assert!(tsrv_large.realized_variance().is_some());
    }

    #[test]
    fn reset_clears() {
        let mut tsrv = TwoScaleRv::builder().k(5).min_samples(10).build().unwrap();

        for i in 0..50 {
            tsrv.update((i as f64).mul_add(0.01, 100.0)).unwrap();
        }
        tsrv.reset();
        assert_eq!(tsrv.count(), 0);
        assert!(tsrv.realized_variance().is_none());
    }

    #[test]
    fn nan_rejected() {
        let mut tsrv = TwoScaleRv::builder().k(5).build().unwrap();
        assert!(matches!(
            tsrv.update(f64::NAN),
            Err(crate::DataError::NotANumber)
        ));
    }

    #[test]
    fn inf_rejected() {
        let mut tsrv = TwoScaleRv::builder().k(5).build().unwrap();
        assert!(matches!(
            tsrv.update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        ));
    }

    #[test]
    fn builder_validation() {
        assert!(matches!(
            TwoScaleRv::builder().build(),
            Err(crate::ConfigError::Missing("k"))
        ));
        assert!(matches!(
            TwoScaleRv::builder().k(1).build(),
            Err(crate::ConfigError::Invalid(_))
        ));
    }
}
