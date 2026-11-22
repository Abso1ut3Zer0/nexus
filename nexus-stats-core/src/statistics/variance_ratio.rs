use alloc::boxed::Box;
use alloc::vec;

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
/// # Cost and rounding
///
/// The sums behind the reading are running totals: `update` adds the
/// newest terms and subtracts the oldest, and both it and
/// [`estimate`](Self::estimate) cost time proportional to `q`, whatever the
/// window. That keeps a reading cheap when many instruments are read on
/// the same bar.
///
/// Three things keep the totals honest over a long run:
///
/// - Each total keeps the digits a plain sum would drop, so a price far
///   off the market passes through and leaves nothing behind.
/// - A window in which the price has not moved reads `None`, by a test
///   that allows for rounding.
/// - The totals are measured about the window's drift as of the last
///   [`resync`](Self::resync), so a strong trend is not lost in the
///   subtraction.
///
/// What remains is slow: rounding in the compensation itself, and the
/// drift moving away from where it was at the last `resync`.
/// [`resync`](Self::resync) recomputes everything from the stored prices.
/// Call it when there is time to spare (once a session), and after the
/// window first fills if the price trends far more than it wanders.
#[derive(Debug, Clone)]
pub struct VarianceRatio {
    q: usize,
    /// The last `window + 1` log prices.
    log_prices: Ring<f64>,
    /// The return every total is measured about: zero, then the window's
    /// drift as of the last `resync`.
    pivot: f64,
    /// Sum of squared one-period returns in the window.
    one_period_squares: Total,
    /// Sum, and sum of squares, of the overlapping `q`-period returns.
    long_sum: Total,
    long_squares: Total,
    /// Totals over pairs of one-period returns `lag` apart, for lag 1 to
    /// `q - 1`.
    lags: Box<[LagTotals]>,
    count: u64,
}

/// A running total that keeps the digits a plain sum drops.
///
/// A term far larger than the total pushes the total's low digits out, and
/// subtracting the term later does not bring them back. `lost` holds them.
#[derive(Debug, Clone, Copy, Default)]
struct Total {
    sum: f64,
    lost: f64,
}

impl Total {
    /// Adds `term`. The rounding error of the addition is recovered exactly
    /// (Knuth's two-sum) and kept.
    #[inline]
    fn add(&mut self, term: f64) {
        let sum = self.sum + term;
        let term_as_added = sum - self.sum;
        self.lost += (self.sum - (sum - term_as_added)) + (term - term_as_added);
        self.sum = sum;
    }

    #[inline]
    fn value(&self) -> f64 {
        self.sum + self.lost
    }
}

/// Running totals over the pairs `(a, b)` of one-period returns a fixed lag
/// apart: what the z statistic needs once the drift is taken out.
#[derive(Debug, Clone, Copy, Default)]
struct LagTotals {
    /// Sum of `a^2 * b^2`.
    squares: Total,
    /// Sum of `a^2 * b + a * b^2`.
    mixed: Total,
    /// Sum of `a * b`.
    products: Total,
    /// Sum of `a^2 + b^2`.
    sum_of_squares: Total,
    /// Sum of `a + b`.
    sum: Total,
}

impl LagTotals {
    /// Adds the pair `(a, b)`, or removes it with a `weight` of -1.
    #[inline]
    fn add(&mut self, a: f64, b: f64, weight: f64) {
        let (a_squared, b_squared, product) = (a * a, b * b, a * b);
        self.squares.add(weight * a_squared * b_squared);
        self.mixed.add(weight * product * (a + b));
        self.products.add(weight * product);
        self.sum_of_squares.add(weight * (a_squared + b_squared));
        self.sum.add(weight * (a + b));
    }

    /// Sum of `(a - shift)^2 * (b - shift)^2` over `pairs` pairs, expanded
    /// in powers of `shift`.
    // Written as the expansion reads; fused forms would hide it.
    #[allow(clippy::suboptimal_flops)]
    fn squares_about(&self, shift: f64, pairs: f64) -> f64 {
        let shift_squared = shift * shift;
        self.squares.value() - 2.0 * shift * self.mixed.value()
            + shift_squared * (self.sum_of_squares.value() + 4.0 * self.products.value())
            - 2.0 * shift_squared * shift * self.sum.value()
            + pairs * shift_squared * shift_squared
    }
}

/// A [`VarianceRatio`] reading.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct VarianceRatioEstimate {
    /// Variance of `q`-period returns over `q` times the variance of
    /// one-period returns. 1 for a random walk.
    pub ratio: f64,
    /// How far `ratio` is from 1, in standard errors; positive for a ratio
    /// above 1. Standard normal if the price is a random walk.
    ///
    /// Lo and MacKinlay's heteroskedasticity-robust statistic (their `z*`):
    /// the standard error is estimated from the returns, so volatility that
    /// changes over time does not pass for memory. `arch` reports it as
    /// `stat`.
    pub z_statistic: f64,
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
        let log_price = crate::math::ln(price);
        self.count += 1;

        // The terms the oldest price is part of leave the totals.
        if self.log_prices.is_full() {
            self.add_terms_from_the_oldest(-1.0);
        }
        self.log_prices.push(log_price);
        self.add_terms_to_the_newest(1.0);
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

    /// The ratio and its test statistic over the window.
    ///
    /// `None` until the window is full, while the price has not moved within
    /// it, or when the standard error cannot be estimated (no two returns
    /// within `q - 1` periods of each other both moved).
    ///
    /// Costs time proportional to `q`.
    #[must_use]
    pub fn estimate(&self) -> Option<VarianceRatioEstimate> {
        if !self.log_prices.is_full() {
            return None;
        }
        let (oldest, newest) = (*self.log_prices.oldest()?, *self.log_prices.newest()?);

        let n = (self.log_prices.capacity() - 1) as f64;
        let q = self.q as f64;
        // The drift per period, from the window's two ends, and how far it
        // is from the return the totals are measured about.
        let drift = (newest - oldest) / n;
        let shift = drift - self.pivot;

        // Sums of squares about the drift, from the totals about the pivot.
        let one_period = (-n * shift).fma(shift, self.one_period_squares.value());
        // SciPy's zero-variance test at the scale of the values subtracted,
        // which are log prices: a variance this small is rounding.
        if one_period / (n - 1.0) <= crate::math::rounding_variance(newest) {
            return None;
        }
        let long_terms = n - q + 1.0;
        let expected = q * shift;
        // sum((D - e)^2) = sum(D^2) - 2e * sum(D) + terms * e^2
        let long = (long_terms * expected).fma(
            expected,
            (-2.0 * expected).fma(self.long_sum.value(), self.long_squares.value()),
        );

        // Lo and MacKinlay's divisors: n - 1, and m for the overlapping sum.
        let m = q * long_terms * (1.0 - q / n);
        let ratio = (long / m) / (one_period / (n - 1.0));

        // The variance of the ratio: each lag's weight times how much the
        // squared one-period returns move together at that lag.
        let one_period_squared = one_period * one_period;
        let mut variance = 0.0;
        for (index, totals) in self.lags.iter().enumerate() {
            let lag = (index + 1) as f64;
            let together = totals.squares_about(shift, n - lag);
            let weight = 2.0 * (1.0 - lag / q);
            variance += weight * weight * (n * together / one_period_squared);
        }
        if variance <= 0.0 {
            return None;
        }

        Some(VarianceRatioEstimate {
            ratio,
            z_statistic: crate::math::sqrt(n) * (ratio - 1.0) / crate::math::sqrt(variance),
        })
    }

    /// Recomputes the running totals from the stored prices, measured about
    /// the window's current drift. Removes what rounding has accumulated.
    ///
    /// The reading does not need it to stay usable; see
    /// [Cost and rounding](Self#cost-and-rounding). It is for a slow path:
    /// it costs time proportional to the window times `q`.
    pub fn resync(&mut self) {
        self.clear_totals();

        let prices = &self.log_prices;
        // Measure about the drift of what is held, so the removal of the
        // drift at read time subtracts little.
        self.pivot = match (prices.oldest(), prices.newest()) {
            (Some(&oldest), Some(&newest)) if prices.len() > 1 => {
                (newest - oldest) / (prices.len() - 1) as f64
            }
            _ => 0.0,
        };
        // Returns over `lag` periods, less what the pivot expects of them.
        let (pivot, long_pivot) = (self.pivot, self.q as f64 * self.pivot);
        let returns_at = |lag: usize, expected: f64| {
            prices
                .iter()
                .zip(prices.iter().skip(lag))
                .map(move |(from, to)| to - from - expected)
        };

        for one_period in returns_at(1, pivot) {
            self.one_period_squares.add(one_period * one_period);
        }
        for (index, totals) in self.lags.iter_mut().enumerate() {
            let pairs = returns_at(1, pivot).zip(returns_at(1, pivot).skip(index + 1));
            pairs.for_each(|(earlier, later)| totals.add(earlier, later, 1.0));
        }
        for long in returns_at(self.q, long_pivot) {
            self.long_sum.add(long);
            self.long_squares.add(long * long);
        }
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
        self.clear_totals();
        self.count = 0;
    }

    fn clear_totals(&mut self) {
        self.pivot = 0.0;
        self.one_period_squares = Total::default();
        self.long_sum = Total::default();
        self.long_squares = Total::default();
        self.lags.fill(LagTotals::default());
    }

    /// Adds every term that ends at the newest price (`weight` 1).
    #[inline]
    fn add_terms_to_the_newest(&mut self, weight: f64) {
        let mut newest_first = self.log_prices.iter().rev();
        let (Some(&newest), Some(&before)) = (newest_first.next(), newest_first.next()) else {
            return;
        };
        let newest_return = newest - before - self.pivot;
        self.one_period_squares
            .add(weight * newest_return * newest_return);

        // Each earlier return, paired with the newest at its lag.
        let mut later_price = before;
        for (totals, &price) in self.lags.iter_mut().zip(newest_first) {
            totals.add(later_price - price - self.pivot, newest_return, weight);
            later_price = price;
        }

        if let Some(&q_back) = self.log_prices.iter().rev().nth(self.q) {
            let long_pivot = self.q as f64 * self.pivot;
            let long_return = newest - q_back - long_pivot;
            self.long_sum.add(weight * long_return);
            self.long_squares.add(weight * long_return * long_return);
        }
    }

    /// Adds every term that starts at the oldest price (`weight` 1), or
    /// removes them (`weight` -1).
    #[inline]
    fn add_terms_from_the_oldest(&mut self, weight: f64) {
        let mut oldest_first = self.log_prices.iter();
        let (Some(&oldest), Some(&after)) = (oldest_first.next(), oldest_first.next()) else {
            return;
        };
        let oldest_return = after - oldest - self.pivot;
        self.one_period_squares
            .add(weight * oldest_return * oldest_return);

        // The oldest return, paired with each later one at its lag.
        let mut earlier_price = after;
        for (totals, &price) in self.lags.iter_mut().zip(oldest_first) {
            totals.add(oldest_return, price - earlier_price - self.pivot, weight);
            earlier_price = price;
        }

        if let Some(&q_on) = self.log_prices.iter().nth(self.q) {
            let long_pivot = self.q as f64 * self.pivot;
            let long_return = q_on - oldest - long_pivot;
            self.long_sum.add(weight * long_return);
            self.long_squares.add(weight * long_return * long_return);
        }
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
            pivot: 0.0,
            one_period_squares: Total::default(),
            long_sum: Total::default(),
            long_squares: Total::default(),
            lags: vec![LagTotals::default(); q - 1].into_boxed_slice(),
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
        vr.estimate().map(|e| e.ratio)
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
    fn z_statistic_matches_arch_reference_values() {
        // The same calls, `.stat` (robust=True, the default).
        let series = prices(400);
        for (window, q, expected) in [
            (64, 2, -3.364_206_799_043_805_6),
            (64, 4, 1.540_712_270_349_799),
            (64, 8, 1.699_862_016_389_469_8),
            (200, 5, 3.193_698_283_701_168_7),
            (399, 16, -4.490_751_545_252_455),
        ] {
            let mut vr = VarianceRatio::builder()
                .q(q)
                .window(window)
                .build()
                .unwrap();
            for &p in &series[..=window] {
                vr.update(p);
            }
            let got = vr.estimate().map(|e| e.z_statistic).unwrap();
            assert!(
                (got - expected).abs() < 1e-8 * expected.abs(),
                "window {window} q {q}: {got} vs {expected}"
            );
        }
    }

    #[test]
    fn z_statistic_has_the_sign_of_the_departure_and_is_small_for_a_random_walk() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut uniform = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            2.0 * ((state >> 11) as f64 / (1u64 << 53) as f64) - 1.0
        };
        let mut walk = VarianceRatio::builder().q(4).window(2000).build().unwrap();
        let mut reverting = walk.clone();
        let mut trending = walk.clone();
        let (mut price, mut previous) = (100.0f64, 0.0);
        let (mut reverting_price, mut trending_price) = (100.0f64, 100.0f64);
        let (mut reverting_previous, mut trending_previous) = (0.0, 0.0);
        for _ in 0..=2000 {
            let shock = 0.001 * uniform();
            price *= (shock + 0.0 * previous).exp();
            previous = shock;
            reverting_previous = -0.5 * reverting_previous + shock;
            reverting_price *= f64::exp(reverting_previous);
            trending_previous = 0.5 * trending_previous + shock;
            trending_price *= f64::exp(trending_previous);
            walk.update(price);
            reverting.update(reverting_price);
            trending.update(trending_price);
        }
        let z = walk.estimate().map(|e| e.z_statistic).unwrap();
        assert!(z.abs() < 3.0, "{z}");
        assert!(reverting.estimate().map(|e| e.z_statistic).unwrap() < -5.0);
        assert!(trending.estimate().map(|e| e.z_statistic).unwrap() > 5.0);
    }

    #[test]
    fn none_when_the_standard_error_cannot_be_estimated() {
        // Two moves, three periods apart: with q = 2 only lag 1 is used, and
        // no two neighbouring returns both moved.
        let mut vr = VarianceRatio::builder().q(2).window(4).build().unwrap();
        for p in [100.0, 101.0, 101.0, 101.0, 100.0] {
            vr.update(p);
        }
        assert!(vr.is_primed());
        assert_eq!(vr.estimate(), None);
    }

    #[test]
    fn running_totals_stay_with_the_exact_recompute() {
        // 60,000 prices through a window of 500, with a burst of moves a
        // hundred times larger in the middle.
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut price = 100.0f64;
        let mut vr = VarianceRatio::builder().q(6).window(500).build().unwrap();
        for i in 0..60_000u32 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let uniform = 2.0 * ((state >> 11) as f64 / (1u64 << 53) as f64) - 1.0;
            let size = if (30_000..30_050).contains(&i) {
                1e-2
            } else {
                1e-4
            };
            price *= (size * uniform).exp();
            vr.update(price);
        }
        let running = vr.estimate().unwrap();
        vr.resync();
        let exact = vr.estimate().unwrap();
        assert!(
            (running.ratio - exact.ratio).abs() < 1e-9 * exact.ratio,
            "{running:?} {exact:?}"
        );
        assert!(
            (running.z_statistic - exact.z_statistic).abs() < 1e-6,
            "{running:?} {exact:?}"
        );
    }

    #[test]
    fn resync_matches_the_written_out_estimators_and_can_be_repeated() {
        let series = prices(300);
        let mut vr = VarianceRatio::builder().q(7).window(50).build().unwrap();
        for &p in &series {
            vr.update(p);
        }
        vr.resync();
        let once = vr.estimate().unwrap();
        vr.resync();
        assert_eq!(vr.estimate(), Some(once));
        let want = reference(&series[series.len() - 51..], 7);
        assert!(
            (once.ratio - want).abs() < 1e-10 * want.abs(),
            "{once:?} {want}"
        );

        // And updating carries on correctly from resynced totals.
        vr.update(101.0);
        assert!(vr.estimate().is_some());
    }

    /// The estimate from the stored prices alone: every deviation formed
    /// directly, nothing expanded and nothing carried over.
    fn exact(prices: &[f64], q: usize) -> Option<VarianceRatioEstimate> {
        let x: Vec<f64> = prices.iter().map(|p| p.ln()).collect();
        let n = x.len() - 1;
        let mu = (x[n] - x[0]) / n as f64;
        let z2: Vec<f64> = (1..=n).map(|k| (x[k] - x[k - 1] - mu).powi(2)).collect();
        let one: f64 = z2.iter().sum();
        if one <= 0.0 {
            return None;
        }
        let long: f64 = (q..=n)
            .map(|k| (x[k] - x[k - q] - q as f64 * mu).powi(2))
            .sum();
        let m = q as f64 * (n - q + 1) as f64 * (1.0 - q as f64 / n as f64);
        let ratio = (long / m) / (one / (n - 1) as f64);
        let mut variance = 0.0;
        for lag in 1..q {
            let together: f64 = (lag..n).map(|t| z2[t] * z2[t - lag]).sum();
            let weight = 2.0 * (1.0 - lag as f64 / q as f64);
            variance += weight * weight * n as f64 * together / (one * one);
        }
        (variance > 0.0).then(|| VarianceRatioEstimate {
            ratio,
            z_statistic: (n as f64).sqrt() * (ratio - 1.0) / variance.sqrt(),
        })
    }

    struct Noise(u64);
    impl Noise {
        /// Uniform on [-1, 1].
        fn next(&mut self) -> f64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            2.0 * ((self.0 >> 11) as f64 / (1u64 << 53) as f64) - 1.0
        }
    }

    /// Feeds `prices` and, at every full window, compares the running
    /// estimate with `exact` on that window.
    fn assert_tracks_exact(prices: &[f64], q: usize, window: usize, ratio_tol: f64, z_tol: f64) {
        let mut vr = VarianceRatio::builder()
            .q(q)
            .window(window)
            .build()
            .unwrap();
        for (i, &p) in prices.iter().enumerate() {
            vr.update(p);
            if i < window {
                continue;
            }
            let want = exact(&prices[i - window..=i], q);
            let got = vr.estimate();
            match (got, want) {
                (Some(got), Some(want)) => assert!(
                    (got.ratio - want.ratio).abs() <= ratio_tol * want.ratio.abs()
                        && (got.z_statistic - want.z_statistic).abs()
                            <= z_tol * want.z_statistic.abs().max(1.0),
                    "price {i}: {got:?} vs {want:?}"
                ),
                (None, None) => {}
                (got, want) => panic!("price {i}: {got:?} vs {want:?}"),
            }
        }
    }

    #[test]
    fn a_halt_after_activity_reads_none() {
        // A walk, then the price held: once the window holds no move, there
        // is no reading, whatever passed through the totals before.
        for (seed, size, q, window) in (1..=40u64).flat_map(|seed| {
            [(1e-2, 2, 64), (5e-2, 8, 150), (1e-3, 4, 64)].map(|(s, q, w)| (seed, s, q, w))
        }) {
            let mut noise = Noise(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut price = 100.0f64;
            let mut prices: Vec<f64> = (0..2 * window)
                .map(|_| {
                    price *= (size * noise.next()).exp();
                    price
                })
                .collect();
            prices.extend(core::iter::repeat_n(price, 2 * window));

            let mut vr = VarianceRatio::builder()
                .q(q)
                .window(window)
                .build()
                .unwrap();
            for (i, &p) in prices.iter().enumerate() {
                vr.update(p);
                // The window is all flat from here on.
                if i >= 3 * window {
                    assert_eq!(
                        vr.estimate(),
                        None,
                        "seed {seed} size {size} q {q} price {i}"
                    );
                }
            }
        }
    }

    #[test]
    fn one_bad_print_does_not_outlast_its_stay_in_the_window() {
        // Quiet noise with a single print far off the market, then back.
        for (print, q, window, noise_size) in [
            (0.01, 4, 64, 1e-5),
            (1e6, 4, 64, 1e-5),
            (0.01, 4, 500, 1e-4),
            (0.9, 8, 64, 1e-5),
        ] {
            let mut noise = Noise(0x9E37_79B9_7F4A_7C15);
            let mut price = 100.0f64;
            let mut prices: Vec<f64> = Vec::new();
            for i in 0..6 * window {
                price *= (noise_size * noise.next()).exp();
                prices.push(if i == 2 * window {
                    price * print
                } else {
                    price
                });
            }
            assert_tracks_exact(&prices, q, window, 1e-9, 1e-6);
        }
    }

    #[test]
    fn a_strong_trend_with_little_noise_is_read_correctly_after_resync() {
        // The drift is a thousand times the noise.
        let (q, window) = (4, 200);
        let mut noise = Noise(0x9E37_79B9_7F4A_7C15);
        let mut log_price = 100.0f64.ln();
        let prices: Vec<f64> = (0..3 * window)
            .map(|_| {
                log_price += 1e-3 + 1e-6 * noise.next();
                log_price.exp()
            })
            .collect();

        let mut vr = VarianceRatio::builder()
            .q(q)
            .window(window)
            .build()
            .unwrap();
        for (i, &p) in prices.iter().enumerate() {
            vr.update(p);
            if i == window {
                vr.resync();
            }
            if i > window {
                let (got, want) = (
                    vr.estimate().unwrap(),
                    exact(&prices[i - window..=i], q).unwrap(),
                );
                assert!(
                    (got.ratio - want.ratio).abs() <= 1e-6 * want.ratio
                        && (got.z_statistic - want.z_statistic).abs()
                            <= 1e-4 * want.z_statistic.abs().max(1.0),
                    "price {i}: {got:?} vs {want:?}"
                );
            }
        }
    }

    #[test]
    fn a_long_run_with_bursts_stays_with_the_exact_estimate() {
        let (q, window) = (6, 300);
        let mut noise = Noise(0x9E37_79B9_7F4A_7C15);
        let mut price = 100.0f64;
        let prices: Vec<f64> = (0..200_000u32)
            .map(|i| {
                let size = if i % 20_000 < 30 { 1e-2 } else { 1e-4 };
                price *= (size * noise.next()).exp();
                price
            })
            .collect();
        let mut vr = VarianceRatio::builder()
            .q(q)
            .window(window)
            .build()
            .unwrap();
        for (i, &p) in prices.iter().enumerate() {
            vr.update(p);
            // Checked at intervals: the exact estimate costs the window.
            if i >= window && i % 997 == 0 {
                let (got, want) = (
                    vr.estimate().unwrap(),
                    exact(&prices[i - window..=i], q).unwrap(),
                );
                assert!(
                    (got.ratio - want.ratio).abs() <= 1e-9 * want.ratio
                        && (got.z_statistic - want.z_statistic).abs() <= 1e-6,
                    "price {i}: {got:?} vs {want:?}"
                );
            }
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
        let got = vr.estimate().map(|e| e.ratio).unwrap();
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
        let got = vr.estimate().map(|e| e.ratio).unwrap();
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
            assert_eq!(vr.estimate().map(|e| e.ratio), None);
            assert!(!vr.is_primed());
        }
        vr.update(101.0);
        assert!(vr.is_primed());
        assert!(vr.estimate().map(|e| e.ratio).is_some());

        for _ in 0..5 {
            vr.update(100.0);
        }
        assert_eq!(vr.estimate().map(|e| e.ratio), None);
    }

    #[test]
    fn reset_empties_the_window() {
        let series = prices(40);
        let mut vr = VarianceRatio::builder().q(3).window(20).build().unwrap();
        for &p in &series {
            vr.update(p);
        }
        vr.reset();
        assert_eq!((vr.count(), vr.estimate().map(|e| e.ratio)), (0, None));
        for &p in &series[..21] {
            vr.update(p);
        }
        let (got, want) = (
            vr.estimate().map(|e| e.ratio).unwrap(),
            reference(&series[..21], 3),
        );
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
        let before = (vr.count(), vr.estimate().map(|e| e.ratio));

        assert_eq!(vr.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(vr.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(vr.checked_update(0.0), Err(OutOfRange));
        assert_eq!(vr.checked_update(-1.0), Err(OutOfRange));

        assert_eq!((vr.count(), vr.estimate().map(|e| e.ratio)), before);
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = VarianceRatio::builder().q(3).window(30).build().unwrap();
        let mut unchecked = checked.clone();
        for &p in &prices(60) {
            checked.checked_update(p).unwrap();
            unchecked.update(p);
        }
        assert_eq!(checked.estimate(), unchecked.estimate());
    }

    #[test]
    fn update_does_not_validate() {
        let mut vr = VarianceRatio::builder().q(2).window(4).build().unwrap();
        for p in [100.0, f64::NAN, 101.0, 102.0, 101.0] {
            vr.update(p);
        }
        assert!(vr.estimate().map(|e| e.ratio).is_none_or(f64::is_nan));
    }
}
