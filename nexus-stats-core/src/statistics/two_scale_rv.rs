use crate::math::MulAdd;
use crate::storage::Ring;

/// Two-scale realized variance: the variance of a price path, with the
/// noise of tick-by-tick trading removed.
///
/// Squared returns sampled at every tick are inflated by bid-ask bounce.
/// Sampled every `k` ticks they are much less so. The estimator takes the
/// slow-scale variance and subtracts the noise it still carries, which the
/// fast scale measures (Zhang, Mykland and Aït-Sahalia, 2005, "A Tale of
/// Two Time Scales", *Journal of the American Statistical Association*):
///
/// ```text
/// TSRV = (1 - n̄/n)⁻¹ · ( [Y,Y]avg − (n̄/n) · [Y,Y]all )
/// ```
///
/// `Y` is the log price, `[Y,Y]all` the sum of squared one-tick returns,
/// `[Y,Y]avg` the sum of squared `k`-tick returns divided by `k`, `n` the
/// number of one-tick returns and `n̄ = (n − k + 1) / k`. The leading factor
/// is the paper's small-sample adjustment (its equation 64).
///
/// The sums run from the last [`reset`](Self::reset): reset at the start of
/// each period you want a variance for. The paper's guidance is a `k` on
/// the order of `n^(2/3)`.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::TwoScaleRv;
///
/// let mut tsrv = TwoScaleRv::builder().k(5).build().unwrap();
/// for i in 0..200 {
///     tsrv.update(100.0 + f64::from(i % 7) * 0.01);
/// }
/// let estimate = tsrv.estimate().unwrap();
/// assert!(estimate.noise_variance > 0.0);
/// ```
#[derive(Debug, Clone)]
pub struct TwoScaleRv {
    /// Sum of squared one-tick log returns: `[Y,Y]all`.
    fast: f64,
    /// Sum of squared `k`-tick log returns, over every starting tick.
    slow: f64,
    /// The last `k` log prices.
    log_prices: Ring<f64>,
    prev_log_price: f64,
    count: u64,
    min_samples: u64,
}

/// A [`TwoScaleRv`] reading.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TwoScaleEstimate {
    /// Noise-corrected variance of the log price over the period. The
    /// subtraction can leave it slightly negative on a short or very noisy
    /// sample.
    pub variance: f64,
    /// Sum of squared one-tick log returns: the uncorrected realized
    /// variance, noise included.
    pub realized_variance: f64,
    /// Variance of the noise in one observed price: `[Y,Y]all / 2n`.
    pub noise_variance: f64,
    /// One-tick returns in the period.
    pub returns: u64,
}

impl TwoScaleEstimate {
    /// Square root of the corrected variance, taking a negative estimate as
    /// zero.
    #[inline]
    #[must_use]
    pub fn volatility(&self) -> f64 {
        crate::math::sqrt(self.variance.max(0.0))
    }
}

/// Builder for [`TwoScaleRv`].
#[derive(Debug, Clone)]
pub struct TwoScaleRvBuilder {
    k: Option<usize>,
    min_samples: Option<u64>,
}

impl TwoScaleRv {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> TwoScaleRvBuilder {
        TwoScaleRvBuilder {
            k: None,
            min_samples: None,
        }
    }

    /// Feeds a price. The logarithm is taken here.
    ///
    /// Does not validate `price`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, price: f64) {
        let log_price = crate::math::ln(price);
        self.count += 1;

        if self.count >= 2 {
            let fast_return = log_price - self.prev_log_price;
            self.fast = fast_return.fma(fast_return, self.fast);
        }
        // The price evicted is the one `k` ticks back.
        if let Some(earlier) = self.log_prices.push(log_price) {
            let slow_return = log_price - earlier;
            self.slow = slow_return.fma(slow_return, self.slow);
        }
        self.prev_log_price = log_price;
    }

    /// Checked update. Feeds `price`, or returns an error and leaves the
    /// estimator unchanged if `price` is NaN, infinite, zero or negative.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `price`
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if `price` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if `price`
    ///   is zero or negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::{DataError, statistics::TwoScaleRv};
    ///
    /// let mut tsrv = TwoScaleRv::builder().k(5).build().unwrap();
    /// assert_eq!(tsrv.checked_update(100.0), Ok(()));
    /// assert_eq!(tsrv.checked_update(0.0), Err(DataError::OutOfRange));
    /// assert_eq!(tsrv.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(&mut self, price: f64) -> Result<(), crate::DataError> {
        // Any positive price is allowed: its logarithm is small.
        crate::math::check_input(price, f64::MAX)?;
        if price <= 0.0 {
            return Err(crate::DataError::OutOfRange);
        }
        self.update(price);
        Ok(())
    }

    /// The reading since the last reset, or `None` until `min_samples`
    /// prices have been fed.
    #[must_use]
    pub fn estimate(&self) -> Option<TwoScaleEstimate> {
        if self.count < self.min_samples {
            return None;
        }

        let k = self.log_prices.capacity() as f64;
        let returns = self.count - 1;
        let n = returns as f64;
        let n_bar = (n - k + 1.0) / k;
        let share = n_bar / n;

        let averaged = self.slow / k;
        let variance = (-share).fma(self.fast, averaged) / (1.0 - share);
        Some(TwoScaleEstimate {
            variance,
            realized_variance: self.fast,
            noise_variance: self.fast / (2.0 * n),
            returns,
        })
    }

    /// Number of prices fed since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether `min_samples` prices have been fed.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Starts a new period. Parameters and allocation unchanged.
    pub fn reset(&mut self) {
        self.fast = 0.0;
        self.slow = 0.0;
        self.log_prices.clear(0.0);
        self.prev_log_price = 0.0;
        self.count = 0;
    }
}

impl TwoScaleRvBuilder {
    /// The slow scale, in ticks. Required, at least 2.
    #[must_use]
    pub fn k(mut self, k: usize) -> Self {
        self.k = Some(k);
        self
    }

    /// Minimum prices before a reading. Default `10 * k`; at least `k + 1`,
    /// the first price count with a `k`-tick return.
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = Some(min);
        self
    }

    /// Builds the estimator.
    ///
    /// # Errors
    ///
    /// - `Missing("k")` if `k` was not set.
    /// - `Invalid` if `k` is below 2 or `min_samples` is below `k + 1`.
    pub fn build(self) -> Result<TwoScaleRv, crate::ConfigError> {
        let k = self.k.ok_or(crate::ConfigError::Missing("k"))?;
        if k < 2 {
            return Err(crate::ConfigError::Invalid("k must be >= 2"));
        }
        let min_samples = self.min_samples.unwrap_or(10 * k as u64);
        if min_samples <= k as u64 {
            return Err(crate::ConfigError::Invalid(
                "min_samples must be at least k + 1",
            ));
        }

        Ok(TwoScaleRv {
            fast: 0.0,
            slow: 0.0,
            log_prices: Ring::new(k, 0.0)?,
            prev_log_price: 0.0,
            count: 0,
            min_samples,
        })
    }
}

#[cfg(test)]
// Expected values are written as plain arithmetic, independent of the fused
// forms the code under test uses.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    fn close(a: f64, b: f64) -> bool {
        (a - b).abs() <= 1e-12 * b.abs().max(1e-12)
    }

    /// The paper's definitions, from the stored log prices: the average over
    /// the `k` subgrids, each started one tick later.
    fn reference(prices: &[f64], k: usize) -> TwoScaleEstimate {
        let y: Vec<f64> = prices.iter().map(|p| p.ln()).collect();
        let n = y.len() - 1;
        let all: f64 = (1..=n).map(|i| (y[i] - y[i - 1]).powi(2)).sum();
        let mut averaged = 0.0;
        for start in 0..k {
            let mut i = start;
            while i + k <= n {
                averaged += (y[i + k] - y[i]).powi(2);
                i += k;
            }
        }
        averaged /= k as f64;
        let n_bar = (n - k + 1) as f64 / k as f64;
        let share = n_bar / n as f64;
        TwoScaleEstimate {
            variance: (averaged - share * all) / (1.0 - share),
            realized_variance: all,
            noise_variance: all / (2.0 * n as f64),
            returns: n as u64,
        }
    }

    fn prices(len: usize) -> Vec<f64> {
        (0..len)
            .map(|i| {
                let i = i as f64;
                100.0 * (0.002 * (i * 0.37).sin() + 0.0005 * (i * 2.9).cos() + 0.0001 * i).exp()
            })
            .collect()
    }

    #[test]
    fn matches_the_papers_definitions_at_every_step() {
        for k in [2, 3, 5, 8] {
            let series = prices(120);
            let mut tsrv = TwoScaleRv::builder()
                .k(k)
                .min_samples(k as u64 + 1)
                .build()
                .unwrap();
            for (i, &p) in series.iter().enumerate() {
                tsrv.update(p);
                let got = tsrv.estimate();
                if i < k {
                    assert_eq!(got, None, "k {k} step {i}");
                    continue;
                }
                let (got, want) = (got.unwrap(), reference(&series[..=i], k));
                assert!(
                    close(got.variance, want.variance)
                        && close(got.realized_variance, want.realized_variance)
                        && close(got.noise_variance, want.noise_variance)
                        && got.returns == want.returns,
                    "k {k} step {i}: {got:?} vs {want:?}"
                );
            }
        }
    }

    #[test]
    fn noise_is_removed_from_the_variance() {
        // A smooth path, and the same path with independent noise on every
        // tick: uniform on [-a, a] in the log price, so its variance is
        // a^2 / 3.
        let (k, a) = (10, 0.0005);
        let mut clean = TwoScaleRv::builder().k(k).build().unwrap();
        let mut noisy = TwoScaleRv::builder().k(k).build().unwrap();
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        for i in 0..20_000u32 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let uniform = (state >> 11) as f64 / (1u64 << 53) as f64;
            let path = 100.0 * (0.01 * (f64::from(i) * 0.0005).sin()).exp();
            clean.update(path);
            noisy.update(path * (a * (2.0 * uniform - 1.0)).exp());
        }
        let (clean, noisy) = (clean.estimate().unwrap(), noisy.estimate().unwrap());

        // Tick-by-tick realized variance is swamped by the noise.
        assert!(noisy.realized_variance > 1000.0 * clean.realized_variance);
        // The corrected variance is not.
        assert!(
            (noisy.variance - clean.variance).abs() < 0.02 * noisy.realized_variance,
            "{noisy:?} {clean:?}"
        );
        // And the noise estimate recovers a^2 / 3.
        let truth = a * a / 3.0;
        assert!(
            (noisy.noise_variance - truth).abs() < 0.05 * truth,
            "{noisy:?}"
        );
    }

    #[test]
    fn scaling_every_price_changes_nothing() {
        let series = prices(100);
        let mut a = TwoScaleRv::builder().k(4).build().unwrap();
        let mut b = TwoScaleRv::builder().k(4).build().unwrap();
        for &p in &series {
            a.update(p);
            b.update(p * 1000.0);
        }
        let (a, b) = (a.estimate().unwrap(), b.estimate().unwrap());
        assert!((a.variance - b.variance).abs() < 1e-12, "{a:?} {b:?}");
    }

    #[test]
    fn volatility_is_the_root_and_never_nan() {
        let positive = TwoScaleEstimate {
            variance: 0.04,
            realized_variance: 0.0,
            noise_variance: 0.0,
            returns: 1,
        };
        assert_eq!(positive.volatility(), 0.2);
        let negative = TwoScaleEstimate {
            variance: -1e-9,
            ..positive
        };
        assert_eq!(negative.volatility(), 0.0);
    }

    #[test]
    fn min_samples_withholds_the_reading() {
        let mut tsrv = TwoScaleRv::builder().k(3).min_samples(10).build().unwrap();
        for i in 0..9u32 {
            tsrv.update(100.0 + f64::from(i));
            assert_eq!(tsrv.estimate(), None);
            assert!(!tsrv.is_primed());
        }
        tsrv.update(110.0);
        assert!(tsrv.estimate().is_some());
    }

    #[test]
    fn reset_starts_a_new_period() {
        let series = prices(60);
        let mut tsrv = TwoScaleRv::builder().k(3).min_samples(4).build().unwrap();
        for &p in &series {
            tsrv.update(p);
        }
        tsrv.reset();
        assert_eq!((tsrv.count(), tsrv.estimate()), (0, None));
        for &p in &series[..20] {
            tsrv.update(p);
        }
        let (got, want) = (tsrv.estimate().unwrap(), reference(&series[..20], 3));
        assert!(close(got.variance, want.variance), "{got:?} vs {want:?}");
    }

    #[test]
    fn builder_validation() {
        use crate::ConfigError::{Invalid, Missing};
        let b = TwoScaleRv::builder;
        assert_eq!(b().build().unwrap_err(), Missing("k"));
        assert_eq!(b().k(1).build().unwrap_err(), Invalid("k must be >= 2"));
        assert_eq!(
            b().k(5).min_samples(5).build().unwrap_err(),
            Invalid("min_samples must be at least k + 1")
        );
        assert!(b().k(5).min_samples(6).build().is_ok());
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let mut tsrv = TwoScaleRv::builder().k(2).min_samples(3).build().unwrap();
        for p in [100.0, 101.0, 100.5, 102.0] {
            tsrv.checked_update(p).unwrap();
        }
        let before = (tsrv.count(), tsrv.estimate());

        assert_eq!(tsrv.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(tsrv.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(tsrv.checked_update(0.0), Err(OutOfRange));
        assert_eq!(tsrv.checked_update(-1.0), Err(OutOfRange));

        assert_eq!((tsrv.count(), tsrv.estimate()), before);
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = TwoScaleRv::builder().k(3).min_samples(4).build().unwrap();
        let mut unchecked = checked.clone();
        for &p in &prices(40) {
            checked.checked_update(p).unwrap();
            unchecked.update(p);
        }
        assert_eq!(checked.estimate(), unchecked.estimate());
    }

    #[test]
    fn update_does_not_validate() {
        let mut tsrv = TwoScaleRv::builder().k(2).min_samples(3).build().unwrap();
        for p in [100.0, f64::NAN, 101.0, 102.0] {
            tsrv.update(p);
        }
        assert!(tsrv.estimate().unwrap().variance.is_nan());
    }
}
