use crate::math::MulAdd;
use crate::storage::Ring;

/// Variance ratio over a sliding window: is the price a random walk?
///
/// If returns are independent, the variance of a `q`-period return is `q`
/// times the variance of a one-period return, and the ratio of the two is
/// 1. A ratio below 1 points to mean reversion, above 1 to trending.
///
/// This is the statistic of Lo and MacKinlay (1988, "Stock Market Prices Do
/// Not Follow Random Walks", *Review of Financial Studies*), computed on the
/// log price over the last `window` returns: overlapping `q`-period returns,
/// the drift taken from the window's two end prices, and their two bias
/// corrections. It gives the value `arch.unitroot.VarianceRatio` reports
/// with its defaults.
///
/// `update` stores the price; the ratio is computed when read, in time
/// proportional to the window, from the stored prices and not from running
/// totals, so it cannot drift.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::VarianceRatio;
///
/// let mut vr = VarianceRatio::builder().q(2).window(64).build().unwrap();
/// // A price that bounces between two levels reverts every step.
/// for i in 0..100 {
///     vr.update(if i % 2 == 0 { 100.0 } else { 101.0 });
/// }
/// assert!(vr.variance_ratio().unwrap() < 0.1);
/// ```
#[derive(Debug, Clone)]
pub struct VarianceRatio {
    q: usize,
    /// The last `window + 1` log prices.
    log_prices: Ring<f64>,
    count: u64,
}

/// Builder for [`VarianceRatio`].
#[derive(Debug, Clone)]
pub struct VarianceRatioBuilder {
    q: Option<usize>,
    window: Option<usize>,
}

impl VarianceRatio {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> VarianceRatioBuilder {
        VarianceRatioBuilder {
            q: None,
            window: None,
        }
    }

    /// Feeds a price. The logarithm is taken here.
    ///
    /// Does not validate `price`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, price: f64) {
        self.count += 1;
        self.log_prices.push(crate::math::ln(price));
    }

    /// Checked update. Feeds `price`, or returns an error and leaves the
    /// window unchanged if `price` is NaN, infinite, zero or negative.
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
    /// use nexus_stats_core::{DataError, statistics::VarianceRatio};
    ///
    /// let mut vr = VarianceRatio::builder().q(2).window(64).build().unwrap();
    /// assert_eq!(vr.checked_update(100.0), Ok(()));
    /// assert_eq!(vr.checked_update(-1.0), Err(DataError::OutOfRange));
    /// assert_eq!(vr.count(), 1);
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

    /// The variance ratio over the window, or `None` until the window is
    /// full, or while the price has not moved within it.
    ///
    /// Costs time proportional to the window.
    #[must_use]
    pub fn variance_ratio(&self) -> Option<f64> {
        if !self.log_prices.is_full() {
            return None;
        }
        let (oldest, newest) = (*self.log_prices.oldest()?, *self.log_prices.newest()?);

        let n = (self.log_prices.capacity() - 1) as f64;
        let q = self.q as f64;
        // The drift per period, from the window's two ends.
        let drift = (newest - oldest) / n;

        let squares_at_lag = |lag: usize| {
            let expected = lag as f64 * drift;
            let earlier = self.log_prices.iter();
            let later = self.log_prices.iter().skip(lag);
            earlier.zip(later).fold(0.0, |sum, (from, to)| {
                let deviation = to - from - expected;
                deviation.fma(deviation, sum)
            })
        };

        let one_period = squares_at_lag(1) / (n - 1.0);
        if one_period <= 0.0 {
            return None;
        }
        // Lo and MacKinlay's divisor for the overlapping q-period sum.
        let m = q * (n - q + 1.0) * (1.0 - q / n);
        Some(squares_at_lag(self.q) / m / one_period)
    }

    /// The return horizon `q`.
    #[must_use]
    pub fn q(&self) -> usize {
        self.q
    }

    /// The window, in one-period returns.
    #[must_use]
    pub fn window(&self) -> usize {
        self.log_prices.capacity() - 1
    }

    /// Number of prices fed since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the window is full.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.log_prices.is_full()
    }

    /// Empties the window. Parameters and allocation unchanged.
    pub fn reset(&mut self) {
        self.log_prices.clear(0.0);
        self.count = 0;
    }
}

impl VarianceRatioBuilder {
    /// The longer return horizon, in periods. Required, at least 2.
    #[must_use]
    pub fn q(mut self, q: usize) -> Self {
        self.q = Some(q);
        self
    }

    /// The window, in one-period returns. Required, more than `q`. The
    /// window holds one more price than this.
    #[must_use]
    pub fn window(mut self, returns: usize) -> Self {
        self.window = Some(returns);
        self
    }

    /// Builds the tracker.
    ///
    /// # Errors
    ///
    /// - `Missing` if `q` or `window` was not set.
    /// - `Invalid` if `q` is below 2 or `window` is not more than `q`.
    pub fn build(self) -> Result<VarianceRatio, crate::ConfigError> {
        let q = self.q.ok_or(crate::ConfigError::Missing("q"))?;
        let window = self.window.ok_or(crate::ConfigError::Missing("window"))?;
        if q < 2 {
            return Err(crate::ConfigError::Invalid("q must be >= 2"));
        }
        if window <= q {
            return Err(crate::ConfigError::Invalid("window must be more than q"));
        }

        Ok(VarianceRatio {
            q,
            log_prices: Ring::new(window + 1, 0.0)?,
            count: 0,
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

    fn prices(len: usize) -> Vec<f64> {
        (0..len)
            .map(|i| {
                let i = i as f64;
                100.0 * (0.002 * (i * 0.37).sin() + 0.0005 * (i * 2.9).cos() + 0.0001 * i).exp()
            })
            .collect()
    }

    fn ratio(prices: &[f64], q: usize) -> Option<f64> {
        let mut vr = VarianceRatio::builder()
            .q(q)
            .window(prices.len() - 1)
            .build()
            .unwrap();
        for &p in prices {
            vr.update(p);
        }
        vr.variance_ratio()
    }

    /// Lo and MacKinlay's estimators, written out from the log prices.
    fn reference(prices: &[f64], q: usize) -> f64 {
        let x: Vec<f64> = prices.iter().map(|p| p.ln()).collect();
        let nq = x.len() - 1;
        let mu = (x[nq] - x[0]) / nq as f64;
        let sigma_a: f64 = (1..=nq)
            .map(|k| (x[k] - x[k - 1] - mu).powi(2))
            .sum::<f64>()
            / (nq - 1) as f64;
        let m = q as f64 * (nq - q + 1) as f64 * (1.0 - q as f64 / nq as f64);
        let sigma_c: f64 = (q..=nq)
            .map(|k| (x[k] - x[k - q] - q as f64 * mu).powi(2))
            .sum::<f64>()
            / m;
        sigma_c / sigma_a
    }

    #[test]
    fn matches_arch_reference_values() {
        // arch 7: VarianceRatio(log_prices, lags=q, trend="c", overlap=True,
        // debiased=True).vr on the first `window + 1` of `prices`.
        let series = prices(400);
        for (window, q, expected) in [
            (64, 2, 0.731_486_452_686_802_2),
            (64, 4, 1.316_490_814_184_074),
            (64, 8, 1.579_690_504_251_915_2),
            (200, 5, 1.454_284_838_771_653_6),
            (399, 16, 0.059_892_612_772_668_02),
        ] {
            let got = ratio(&series[..=window], q).unwrap();
            assert!(
                (got - expected).abs() < 1e-9 * expected,
                "window {window} q {q}: {got} vs {expected}"
            );
        }
    }

    #[test]
    fn the_window_slides() {
        // arch on prices 100..=164, reached here by feeding all 165.
        let series = prices(165);
        let mut vr = VarianceRatio::builder().q(4).window(64).build().unwrap();
        for &p in &series {
            vr.update(p);
        }
        let got = vr.variance_ratio().unwrap();
        assert!((got - 1.304_359_880_378_319_6).abs() < 1e-9, "{got}");
    }

    #[test]
    fn matches_the_written_out_estimators() {
        let series = prices(300);
        for (window, q) in [(3, 2), (10, 3), (50, 7), (299, 50)] {
            let (got, want) = (
                ratio(&series[..=window], q).unwrap(),
                reference(&series[..=window], q),
            );
            assert!(
                (got - want).abs() < 1e-10 * want.abs(),
                "window {window} q {q}: {got} vs {want}"
            );
        }
    }

    #[test]
    fn a_random_walk_reads_near_one() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut price = 100.0f64;
        let mut vr = VarianceRatio::builder()
            .q(8)
            .window(20_000)
            .build()
            .unwrap();
        for _ in 0..=20_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let uniform = (state >> 11) as f64 / (1u64 << 53) as f64;
            price *= (0.001 * (2.0 * uniform - 1.0)).exp();
            vr.update(price);
        }
        let got = vr.variance_ratio().unwrap();
        assert!((got - 1.0).abs() < 0.05, "{got}");
    }

    #[test]
    fn scaling_every_price_changes_nothing() {
        let series = prices(100);
        let scaled: Vec<f64> = series.iter().map(|p| p * 1000.0).collect();
        let (a, b) = (ratio(&series, 5).unwrap(), ratio(&scaled, 5).unwrap());
        assert!((a - b).abs() < 1e-9, "{a} {b}");
    }

    #[test]
    fn none_until_full_and_while_flat() {
        let mut vr = VarianceRatio::builder().q(2).window(4).build().unwrap();
        for p in [100.0, 101.0, 100.0, 102.0] {
            vr.update(p);
            assert_eq!(vr.variance_ratio(), None);
            assert!(!vr.is_primed());
        }
        vr.update(101.0);
        assert!(vr.is_primed());
        assert!(vr.variance_ratio().is_some());

        for _ in 0..5 {
            vr.update(100.0);
        }
        assert_eq!(vr.variance_ratio(), None);
    }

    #[test]
    fn reset_empties_the_window() {
        let series = prices(40);
        let mut vr = VarianceRatio::builder().q(3).window(20).build().unwrap();
        for &p in &series {
            vr.update(p);
        }
        vr.reset();
        assert_eq!((vr.count(), vr.variance_ratio()), (0, None));
        for &p in &series[..21] {
            vr.update(p);
        }
        let (got, want) = (vr.variance_ratio().unwrap(), reference(&series[..21], 3));
        assert!((got - want).abs() < 1e-10 * want.abs(), "{got} vs {want}");
    }

    #[test]
    fn builder_validation() {
        use crate::ConfigError::{Invalid, Missing};
        let b = VarianceRatio::builder;
        assert_eq!(b().window(10).build().unwrap_err(), Missing("q"));
        assert_eq!(b().q(2).build().unwrap_err(), Missing("window"));
        assert_eq!(
            b().q(1).window(10).build().unwrap_err(),
            Invalid("q must be >= 2")
        );
        assert_eq!(
            b().q(5).window(5).build().unwrap_err(),
            Invalid("window must be more than q")
        );
        let vr = b().q(5).window(6).build().unwrap();
        assert_eq!((vr.q(), vr.window()), (5, 6));
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let mut vr = VarianceRatio::builder().q(2).window(4).build().unwrap();
        for p in [100.0, 101.0, 100.0, 102.0, 101.0] {
            vr.checked_update(p).unwrap();
        }
        let before = (vr.count(), vr.variance_ratio());

        assert_eq!(vr.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(vr.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(vr.checked_update(0.0), Err(OutOfRange));
        assert_eq!(vr.checked_update(-1.0), Err(OutOfRange));

        assert_eq!((vr.count(), vr.variance_ratio()), before);
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = VarianceRatio::builder().q(3).window(30).build().unwrap();
        let mut unchecked = checked.clone();
        for &p in &prices(60) {
            checked.checked_update(p).unwrap();
            unchecked.update(p);
        }
        assert_eq!(checked.variance_ratio(), unchecked.variance_ratio());
    }

    #[test]
    fn update_does_not_validate() {
        let mut vr = VarianceRatio::builder().q(2).window(4).build().unwrap();
        for p in [100.0, f64::NAN, 101.0, 102.0, 101.0] {
            vr.update(p);
        }
        assert!(vr.variance_ratio().is_none_or(f64::is_nan));
    }
}
