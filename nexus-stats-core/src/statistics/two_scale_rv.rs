use crate::math::MulAdd;
use crate::storage::Ring;

/// Two-scale realized variance: a volatility estimate that is robust to
/// microstructure noise (Zhang, Mykland & Aït-Sahalia, 2005).
///
/// Observed prices are an efficient price plus noise (bid-ask bounce,
/// discreteness). The realized variance of every tick, `sum (dp)^2`, adds
/// twice the noise variance per tick, so at high frequency it measures
/// mostly noise. Two-scale realized variance combines two time scales:
///
/// - the **slow** scale: the average over the `K` offset grids of the
///   realized variance of `K`-tick changes, `sum (p_i - p_{i-K})^2 / K`,
///   which noise inflates much less;
/// - the **fast** scale: the all-tick realized variance, used to estimate
///   and remove the noise that remains in the slow scale.
///
/// `TSRV = slow - (n_bar / n) * fast` (the paper's equation 2.2), with `n`
/// the number of ticks and `n_bar = (n - K + 1) / K` the average number of
/// `K`-tick changes per grid, then scaled by the paper's small-sample
/// refinement `1 / (1 - n_bar / n)` (equation 2.4), which makes it unbiased
/// to higher order: without it the estimate reads low by about `1 / K`
/// even on noise-free data. Equation numbers are those of Aït-Sahalia,
/// Mykland & Zhang, "Ultra High Frequency Volatility Estimation with
/// Dependent Microstructure Noise".
///
/// The result is a total over the period since the last
/// [`reset`](Self::reset), like any realized variance: reset at the start
/// of each period and read at its end.
///
/// # Parameters
///
/// - `k`: the slow scale in ticks (typically 5 to 20).
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::TwoScaleRv;
///
/// let mut tsrv = TwoScaleRv::builder().k(5).build().unwrap();
///
/// // A price that only bounces between bid and ask: all noise, no
/// // movement in the efficient price.
/// let mut estimate = None;
/// for i in 0..2_000 {
///     let bounce = if i % 2 == 0 { 0.01 } else { -0.01 };
///     estimate = tsrv.update(100.0 + bounce);
/// }
/// let e = estimate.unwrap();
/// // The all-tick realized variance is all bounce...
/// assert!(e.realized_variance > 0.79);
/// // ...and the two-scale estimate removes it.
/// assert!(e.two_scale_variance < 0.01 * e.realized_variance);
/// ```
#[derive(Debug, Clone)]
pub struct TwoScaleRv {
    /// `sum (p_i - p_{i-1})^2`.
    fast_sum_sq: f64,
    /// `sum (p_i - p_{i-K})^2`.
    slow_sum_sq: f64,
    /// The last `K` prices: the oldest is the price `K` ticks back.
    history: Ring<f64>,
    count: u64,
    min_samples: u64,
}

/// A [`TwoScaleRv`] reading, over the period since the last reset.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TwoScaleEstimate {
    /// Two-scale realized variance: the noise-corrected total variation of
    /// the efficient price. Floored at zero (in short or very noisy samples
    /// the raw estimate can fall below it).
    pub two_scale_variance: f64,
    /// Realized variance, `sum (dp)^2` over every tick: what a naive
    /// estimator reports, noise included. The same quantity as
    /// [`JumpDecomposition::realized_variance`](crate::statistics::JumpDecomposition).
    pub realized_variance: f64,
    /// Estimated variance of the noise on a single price observation,
    /// `realized_variance / (2 n)` (the paper's equation 2.1), taking the
    /// noise to be independent from tick to tick. It includes the efficient
    /// price's own per-tick variance, which at high frequency is small
    /// beside the noise.
    pub noise_variance: f64,
}

impl TwoScaleEstimate {
    /// Two-scale volatility: the square root of the two-scale variance.
    #[inline]
    #[must_use]
    pub fn two_scale_volatility(&self) -> f64 {
        crate::math::sqrt(self.two_scale_variance)
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
    #[inline]
    #[must_use]
    pub fn builder() -> TwoScaleRvBuilder {
        TwoScaleRvBuilder {
            k: None,
            min_samples: None,
        }
    }

    /// Feeds a trade price. Returns the estimate once primed.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in. A
    /// NaN or an infinity makes the readings NaN from then on, until
    /// [`reset`](Self::reset); a finite value above
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT) in magnitude can overflow them. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, price: f64) -> Option<TwoScaleEstimate> {
        self.count += 1;
        if let Some(&previous) = self.history.newest() {
            let diff = price - previous;
            self.fast_sum_sq += diff * diff;
        }
        if let Some(k_ticks_back) = self.history.push(price) {
            let diff = price - k_ticks_back;
            self.slow_sum_sq += diff * diff;
        }
        self.last()
    }

    /// [`update`](Self::update) with the input validated first: refuses a
    /// value that is NaN, infinite, or above [`INPUT_LIMIT`](crate::INPUT_LIMIT) in
    /// magnitude, and leaves the state untouched. Fed only through this
    /// method, no reading is ever NaN, or infinite unless its documentation
    /// says so.
    ///
    /// # Errors
    ///
    /// `DataError::NotANumber`, `DataError::Infinite`, or
    /// `DataError::OutOfRange` for a finite magnitude above the limit.
    #[inline]
    pub fn checked_update(
        &mut self,
        price: f64,
    ) -> Result<Option<TwoScaleEstimate>, crate::DataError> {
        check_magnitude!(price, crate::INPUT_LIMIT);
        Ok(self.update(price))
    }

    /// The current estimate, or `None` if not primed.
    #[inline]
    #[must_use]
    #[allow(clippy::cast_precision_loss)]
    pub fn last(&self) -> Option<TwoScaleEstimate> {
        if !self.is_primed() {
            return None;
        }
        // `min_samples >= 2 k` makes both counts positive.
        let k = self.history.capacity() as f64;
        let ticks = (self.count - 1) as f64;
        let slow_changes = (self.count - self.history.capacity() as u64) as f64;
        // n_bar / n.
        let ratio = slow_changes / (k * ticks);
        let raw = (-ratio).fma(self.fast_sum_sq, self.slow_sum_sq / k);
        Some(TwoScaleEstimate {
            two_scale_variance: (raw / (1.0 - ratio)).max(0.0),
            realized_variance: self.fast_sum_sq,
            noise_variance: self.fast_sum_sq / (2.0 * ticks),
        })
    }

    /// The slow scale `K`, in ticks.
    #[inline]
    #[must_use]
    pub fn k(&self) -> usize {
        self.history.capacity()
    }

    /// Number of prices seen since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether `min_samples` prices have been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Starts a new period: forgets every price. Parameters unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.fast_sum_sq = 0.0;
        self.slow_sum_sq = 0.0;
        self.history.clear(0.0);
        self.count = 0;
    }
}

impl TwoScaleRvBuilder {
    /// The slow scale in ticks (required, >= 2).
    #[inline]
    #[must_use]
    pub fn k(mut self, k: usize) -> Self {
        self.k = Some(k);
        self
    }

    /// Minimum prices before an estimate is returned. Default: `10 * k`.
    /// At least `2 * k`.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = Some(min);
        self
    }

    /// Builds the two-scale estimator.
    ///
    /// # Errors
    ///
    /// - `Missing("k")` if `k` was not set.
    /// - `Invalid` if `k` is below 2, or `min_samples` is below `2 * k`.
    #[inline]
    pub fn build(self) -> Result<TwoScaleRv, crate::ConfigError> {
        let k = self.k.ok_or(crate::ConfigError::Missing("k"))?;
        if k < 2 {
            return Err(crate::ConfigError::Invalid("k must be >= 2"));
        }
        let floor = 2 * k as u64;
        let min_samples = self.min_samples.unwrap_or(10 * k as u64);
        if min_samples < floor {
            return Err(crate::ConfigError::Invalid(
                "min_samples must be at least 2 * k",
            ));
        }
        Ok(TwoScaleRv {
            fast_sum_sq: 0.0,
            slow_sum_sq: 0.0,
            history: Ring::new(k, 0.0)?,
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

    fn lcg(state: &mut u64) -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*state >> 11) as f64 / (1u64 << 53) as f64 - 0.5
    }

    fn fed(k: usize, prices: impl IntoIterator<Item = f64>) -> TwoScaleRv {
        let mut t = TwoScaleRv::builder().k(k).build().unwrap();
        for p in prices {
            let _ = t.update(p);
        }
        t
    }

    /// The paper's formula computed directly from the stored prices.
    fn reference(prices: &[f64], k: usize) -> TwoScaleEstimate {
        let n = (prices.len() - 1) as f64;
        let fast: f64 = prices.windows(2).map(|w| (w[1] - w[0]).powi(2)).sum();
        let slow: f64 = (k..prices.len())
            .map(|i| (prices[i] - prices[i - k]).powi(2))
            .sum::<f64>()
            / k as f64;
        let n_bar = (n - k as f64 + 1.0) / k as f64;
        let rv = ((slow - n_bar / n * fast) / (1.0 - n_bar / n)).max(0.0);
        TwoScaleEstimate {
            two_scale_variance: rv,
            realized_variance: fast,
            noise_variance: fast / (2.0 * n),
        }
    }

    #[test]
    fn matches_the_formula_computed_from_stored_prices() {
        let mut state = 5;
        let mut price = 100.0;
        let prices: Vec<f64> = (0..400)
            .map(|_| {
                price += lcg(&mut state) * 0.1;
                price + lcg(&mut state) * 0.05
            })
            .collect();
        for k in [2usize, 5, 13] {
            let mut t = TwoScaleRv::builder()
                .k(k)
                .min_samples(2 * k as u64)
                .build()
                .unwrap();
            for (i, &p) in prices.iter().enumerate() {
                let got = t.update(p);
                if i + 1 < 2 * k {
                    assert_eq!(got, None);
                    continue;
                }
                let want = reference(&prices[..=i], k);
                let got = got.unwrap();
                let close = |a: f64, b: f64| (a - b).abs() <= 1e-9 * b.abs().max(1e-6);
                assert!(
                    close(got.two_scale_variance, want.two_scale_variance)
                        && close(got.realized_variance, want.realized_variance)
                        && close(got.noise_variance, want.noise_variance),
                    "k {k} step {i}: {got:?} vs {want:?}"
                );
            }
        }
    }

    #[test]
    fn noise_free_random_walk_reads_its_true_variation() {
        // Without the small-sample adjustment this reads low by 1 / K.
        for k in [5usize, 20] {
            let n = 20_000;
            let (mut sum, walks) = (0.0, 40);
            for seed in 0..walks {
                let mut state = 1 + seed;
                let mut price = 100.0;
                let t = fed(
                    k,
                    (0..=n).map(|_| {
                        price += lcg(&mut state);
                        price
                    }),
                );
                sum += t.last().unwrap().two_scale_variance;
            }
            // Uniform(-0.5, 0.5) steps have variance 1/12.
            let truth = n as f64 / 12.0;
            let mean = sum / walks as f64;
            assert!((mean / truth - 1.0).abs() < 0.03, "k {k}: {}", mean / truth);
        }
    }

    #[test]
    fn noise_is_removed_and_measured() {
        // Efficient price: random walk with step variance 1/1200. Observed
        // with independent noise of variance 1/12 per tick, a hundred times
        // larger: the all-tick variance is almost entirely noise.
        let n = 50_000;
        let mut state = 77;
        let mut price = 100.0;
        let t = fed(
            20,
            (0..=n).map(|_| {
                price += lcg(&mut state) * 0.1;
                price + lcg(&mut state)
            }),
        );
        let e = t.last().unwrap();
        let truth = n as f64 / 1200.0;
        assert!(e.realized_variance > 150.0 * truth);
        assert!(
            (e.two_scale_variance / truth - 1.0).abs() < 0.5,
            "{} vs {truth}",
            e.two_scale_variance
        );
        assert!((e.noise_variance * 12.0 - 1.0).abs() < 0.05, "{e:?}");
        assert!((e.two_scale_volatility().powi(2) - e.two_scale_variance).abs() < 1e-9);
    }

    #[test]
    fn pure_bounce_has_no_variation_left() {
        let t = fed(
            5,
            (0..2_000).map(|i| if i % 2 == 0 { 100.01 } else { 99.99 }),
        );
        let e = t.last().unwrap();
        // 1999 changes of 0.02.
        assert!((e.realized_variance - 1999.0 * 0.0004).abs() < 1e-9);
        assert!(e.two_scale_variance < 0.01 * e.realized_variance, "{e:?}");
        // The noise estimate assumes independent noise, for which a change
        // has twice the variance of one observation: (0.02)^2 / 2. A strict
        // alternation is not independent, so this is twice the bounce's own
        // variance of 1e-4.
        assert!((e.noise_variance - 2e-4).abs() < 2e-6, "{e:?}");
    }

    #[test]
    fn primes_at_min_samples_and_resets() {
        let mut t = TwoScaleRv::builder().k(3).min_samples(6).build().unwrap();
        for i in 0..5 {
            assert_eq!(t.update(f64::from(i)), None);
            assert!(!t.is_primed());
        }
        assert!(t.update(5.0).is_some());
        assert_eq!(t.k(), 3);
        t.reset();
        assert_eq!(t.count(), 0);
        assert_eq!(t.last(), None);
        // A flat price after the reset: nothing carried over.
        for _ in 0..6 {
            let _ = t.update(9.0);
        }
        let e = t.last().unwrap();
        assert_eq!((e.two_scale_variance, e.realized_variance), (0.0, 0.0));
    }

    #[test]
    fn builder_validation() {
        use crate::ConfigError::{Invalid, Missing};
        let b = TwoScaleRv::builder;
        assert_eq!(b().build().unwrap_err(), Missing("k"));
        assert_eq!(b().k(1).build().unwrap_err(), Invalid("k must be >= 2"));
        for min in [0, 9] {
            assert_eq!(
                b().k(5).min_samples(min).build().unwrap_err(),
                Invalid("min_samples must be at least 2 * k")
            );
        }
        assert!(b().k(5).min_samples(10).build().is_ok());
        assert_eq!(b().k(5).build().unwrap().min_samples, 50);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut t = TwoScaleRv::builder().k(5).build().unwrap();
        assert_eq!(
            t.checked_update(f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        assert_eq!(
            t.checked_update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(t.count(), 0);
    }
}
