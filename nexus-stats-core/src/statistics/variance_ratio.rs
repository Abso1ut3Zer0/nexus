use alloc::boxed::Box;
use alloc::vec;

use crate::math::{MulAdd, RoundingEstimate};
use crate::storage::SliceRing;

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
/// # Deciding
///
/// [`estimate`](Self::estimate) returns the two together. The ratio says
/// which way and how far; the z statistic says whether that distance could
/// be chance:
///
/// - `|z|` below about 2: consistent with a random walk, whatever the
///   ratio. On a short window a ratio of 0.8 or 1.2 is ordinary.
/// - `z` above about 2: trending. Below about -2: mean-reverting. Under a
///   random walk `z` is standard normal, so 1.96 is the usual 5% level and
///   2.58 the 1% level.
/// - Read on every bar, a 5% level raises a false signal on about one bar
///   in twenty. Use a higher level, or require it to hold for several
///   reads, when a signal is costly to act on.
///
/// A longer window makes `z` more sensitive and slower to notice a change;
/// a larger `q` looks for memory over a longer horizon.
///
/// # Cost and rounding
///
/// The sums behind the reading are running totals: `update` adds the
/// newest terms and subtracts the oldest, and both it and
/// [`estimate`](Self::estimate) cost time proportional to `q`, whatever the
/// window. That keeps a reading cheap when many instruments are read on
/// the same bar.
///
/// A running total is rounded at every add, by up to half a unit in the
/// last place of the total as it is then. The errors stay in the total, so
/// they matter once the total has become much smaller than it was: after
/// volatility falls a long way, or after a price far off the market has
/// come and gone. The z statistic sums fourth powers and feels this first;
/// the ratio, which sums squares, is far less affected.
///
/// `update` keeps an estimate of that error (see [`Resync`]) and returns
/// [`Resync::Advised`] once it could reach one part in a thousand of the z
/// statistic, and keeps returning it until [`resync`](Self::resync) is
/// called. The reading stays available in the meantime. `resync` recomputes
/// the totals from the stored prices; it costs the window times `q`, so it
/// is for the caller to schedule when there is time to spare. pandas guards
/// its rolling moments against the same loss, recomputing the window itself
/// when it suspects it.
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
/// let estimate = vr.estimate().unwrap();
/// assert!(estimate.ratio < 0.1);
/// assert!(estimate.z_statistic < -3.0);
/// ```
#[derive(Debug, Clone)]
pub struct VarianceRatio {
    q: usize,
    /// The last `window + 1` log prices.
    log_prices: SliceRing<f64>,
    /// The return every total is measured about: zero, then the window's
    /// drift as of the last `resync`.
    pivot: f64,
    /// Sum of squared one-period returns in the window.
    one_period_squares: f64,
    /// Sum, and sum of squares, of the overlapping `q`-period returns.
    long_sum: f64,
    long_squares: f64,
    /// Totals over pairs of one-period returns `lag` apart, for lag 1 to
    /// `q - 1`.
    lags: Box<[LagTotals]>,
    /// Lo and MacKinlay's weight on each lag's total, `(2 * (1 - lag / q))^2`,
    /// and their sum.
    lag_weights: Box<[f64]>,
    lag_weights_sum: f64,
    /// Their divisor for the `q`-period sum of squares over a full window,
    /// `m = q * (n - q + 1) * (1 - q / n)`.
    long_divisor: f64,
    /// Sum of fourth powers of the one-period returns in the window: no
    /// lag's total of `a^2 * b^2` is larger.
    fourth_powers: f64,
    /// The rounding `fourth_powers` and `one_period_squares` have
    /// accumulated since the last `resync`.
    fourth_powers_rounding: RoundingEstimate,
    squares_rounding: RoundingEstimate,
    /// And `long_squares` and `long_sum`.
    long_squares_rounding: RoundingEstimate,
    long_sum_rounding: RoundingEstimate,
    /// How many prices in a row have equalled the one before.
    unchanged: usize,
    /// What `update` last returned.
    resync: Resync,
    count: u64,
}

/// What [`VarianceRatio::update`] reports about its running totals.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Resync {
    /// The totals hold all the digits the reading needs.
    NotNeeded,
    /// Rounding left in the totals may exceed one part in a thousand of the
    /// z statistic. Volatility has fallen far below what the totals went
    /// through earlier, a price far off the market has passed through, the
    /// trend has moved far from where it was at the last
    /// [`resync`](VarianceRatio::resync), or a price was not a number. The
    /// reading is still produced; call `resync` when there is time.
    ///
    /// It is also returned on a quiet window that has no reading (no two
    /// returns within `q - 1` of each other both moved) when the totals
    /// still carry rounding from busier prices: the sum that should be
    /// exactly zero is not, and whether the reading comes out `None` or a
    /// meaningless number depends on the sign of what is left. A `resync`
    /// leaves that sum exactly zero and the advice does not come back.
    Advised {
        /// An estimate of the error the z statistic may carry, as a share
        /// of the larger of `|z|` and 1, at the update that raised the
        /// advice. It is four standard deviations of the rounding the
        /// totals have accumulated, so the real error is usually several
        /// times smaller. 1 or more means no correct digits are left. The
        /// ratio is far less affected.
        z_error: f64,
    },
}

/// Running totals over the pairs `(a, b)` of one-period returns a fixed lag
/// apart: what the z statistic needs once the drift is taken out.
#[derive(Debug, Clone, Copy, Default)]
struct LagTotals {
    /// Sum of `a^2 * b^2`.
    squares: f64,
    /// Sum of `a^2 * b + a * b^2`.
    mixed: f64,
    /// Sum of `a * b`.
    products: f64,
    /// Sum of `a^2 + b^2`.
    sum_of_squares: f64,
    /// Sum of `a + b`.
    sum: f64,
}

impl LagTotals {
    /// Adds the pair `(a, b)`, or removes it with a `weight` of -1.
    #[inline]
    fn add(&mut self, a: f64, b: f64, weight: f64) {
        let (a_squared, b_squared, product) = (a * a, b * b, a * b);
        self.squares = (weight * a_squared).fma(b_squared, self.squares);
        self.mixed = (weight * product).fma(a + b, self.mixed);
        self.products = weight.fma(product, self.products);
        self.sum_of_squares = weight.fma(a_squared + b_squared, self.sum_of_squares);
        self.sum = weight.fma(a + b, self.sum);
    }

    /// Sum of `(a - shift)^2 * (b - shift)^2` over `pairs` pairs, expanded
    /// in powers of `shift`.
    // Written as the expansion reads; fused forms would hide it.
    #[allow(clippy::suboptimal_flops)]
    fn squares_about(&self, shift: f64, pairs: f64) -> f64 {
        let shift_squared = shift * shift;
        self.squares - 2.0 * shift * self.mixed
            + shift_squared * (self.sum_of_squares + 4.0 * self.products)
            - 2.0 * shift_squared * shift * self.sum
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

/// The window's size, the drift's distance from the pivot, and the sum of
/// squared one-period returns about the drift.
#[derive(Clone, Copy)]
struct Centered {
    n: f64,
    shift: f64,
    one_period: f64,
}

impl VarianceRatio {
    /// The share of the z statistic that rounding in the totals may reach
    /// before [`Resync::Advised`] is returned: one part in a thousand. A
    /// test statistic read against 2 or 2.6 needs no more.
    const ADVISE_ABOVE: f64 = 1e-3;

    /// How many standard deviations of accumulated rounding `z_error`
    /// reports: 4, which a normal error exceeds about once in 16,000.
    const CONFIDENCE: f64 = 4.0;

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
    /// Returns whether a [`resync`](Self::resync) is advised; once it is,
    /// every call says so until one is made.
    ///
    /// Does not validate `price`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, price: f64) -> Resync {
        let log_price = crate::math::ln(price);
        self.count += 1;

        // The terms the oldest price is part of leave the totals.
        if self.log_prices.is_full() {
            self.add_terms_from_the_oldest(-1.0);
        }
        let repeats = self.log_prices.as_slice().last() == Some(&log_price);
        self.unchanged = if repeats { self.unchanged + 1 } else { 0 };
        self.log_prices.push(log_price);
        self.add_terms_to_the_newest(1.0);
        // One term leaves each total and one enters.
        self.fourth_powers_rounding.record_n(self.fourth_powers, 2);
        self.squares_rounding.record_n(self.one_period_squares, 2);
        self.long_squares_rounding.record_n(self.long_squares, 2);
        self.long_sum_rounding.record_n(self.long_sum, 2);

        if self.resync == Resync::NotNeeded {
            self.resync = self.assess();
        }
        self.resync
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
    /// use nexus_stats_core::{DataError, statistics::{Resync, VarianceRatio}};
    ///
    /// let mut vr = VarianceRatio::builder().q(2).window(64).build().unwrap();
    /// assert_eq!(vr.checked_update(100.0), Ok(Resync::NotNeeded));
    /// assert_eq!(vr.checked_update(-1.0), Err(DataError::OutOfRange));
    /// assert_eq!(vr.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(&mut self, price: f64) -> Result<Resync, crate::DataError> {
        // Any positive price is allowed: its logarithm is small.
        crate::math::check_input(price, f64::MAX)?;
        if price <= 0.0 {
            return Err(crate::DataError::OutOfRange);
        }
        Ok(self.update(price))
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
        let centered = self.centered()?;
        let Centered { n, one_period, .. } = centered;

        // A price that never moved leaves only rounding in the totals.
        if self.unchanged >= self.window() {
            return None;
        }
        // SciPy's zero-variance test at the scale of the values subtracted,
        // which are log prices: a variance this small is rounding.
        let newest = *self.log_prices.as_slice().last()?;
        if one_period / (n - 1.0) <= crate::math::rounding_variance(newest) {
            return None;
        }

        let ratio = self.ratio(centered, self.long_squares_about_the_drift(centered));
        let variance = Self::ratio_variance(centered, self.weighted_lag_sum(centered));
        if variance <= 0.0 {
            return None;
        }

        Some(VarianceRatioEstimate {
            ratio,
            z_statistic: crate::math::sqrt(n) * (ratio - 1.0) / crate::math::sqrt(variance),
        })
    }

    /// Recomputes the running totals from the stored prices, measured about
    /// the window's current drift, and clears [`Resync::Advised`].
    ///
    /// If a return far larger than the rest is still in the window, the
    /// advice comes back when it leaves: resync again then.
    ///
    /// For a slow path: it costs time proportional to the window times `q`.
    pub fn resync(&mut self) {
        self.clear_totals();

        let prices = self.log_prices.as_slice();
        if prices.len() < 2 {
            return;
        }
        // Measure about the drift of what is held, so taking the drift out
        // at read time subtracts little.
        self.pivot = (prices[prices.len() - 1] - prices[0]) / (prices.len() - 1) as f64;
        let adds = prices.len() - 1;

        self.sum_one_period_returns();
        self.sum_pairs_at_each_lag();
        self.sum_long_returns();

        // The recomputation is itself one rounded add per term.
        self.fourth_powers_rounding
            .record_n(self.fourth_powers, adds);
        self.squares_rounding
            .record_n(self.one_period_squares, adds);
        let long_adds = (adds + 1).saturating_sub(self.q);
        self.long_squares_rounding
            .record_n(self.long_squares, long_adds);
        self.long_sum_rounding.record_n(self.long_sum, long_adds);
        self.resync = self.assess();
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
        self.log_prices.clear();
        self.clear_totals();
        self.unchanged = 0;
        self.count = 0;
    }

    /// For `resync`: the squares and fourth powers of the one-period
    /// returns held, about the pivot.
    fn sum_one_period_returns(&mut self) {
        for pair in self.log_prices.as_slice().windows(2) {
            let one_period = pair[1] - pair[0] - self.pivot;
            let square = one_period * one_period;
            self.one_period_squares += square;
            self.fourth_powers = square.fma(square, self.fourth_powers);
        }
    }

    /// For `resync`: each lag's totals, over every pair of one-period
    /// returns that far apart.
    fn sum_pairs_at_each_lag(&mut self) {
        let pivot = self.pivot;
        let returns = self
            .log_prices
            .as_slice()
            .windows(2)
            .map(|pair| pair[1] - pair[0] - pivot);
        for (index, totals) in self.lags.iter_mut().enumerate() {
            let pairs = returns.clone().zip(returns.clone().skip(index + 1));
            pairs.for_each(|(earlier, later)| totals.add(earlier, later, 1.0));
        }
    }

    /// For `resync`: the sum and squares of the overlapping `q`-period
    /// returns held, about `q` times the pivot.
    fn sum_long_returns(&mut self) {
        let prices = self.log_prices.as_slice();
        let long_pivot = self.q as f64 * self.pivot;
        for (from, to) in prices.iter().zip(&prices[self.q.min(prices.len())..]) {
            let long = to - from - long_pivot;
            self.long_sum += long;
            self.long_squares = long.fma(long, self.long_squares);
        }
    }

    fn clear_totals(&mut self) {
        self.pivot = 0.0;
        self.one_period_squares = 0.0;
        self.long_sum = 0.0;
        self.long_squares = 0.0;
        self.lags.fill(LagTotals::default());
        self.fourth_powers = 0.0;
        self.fourth_powers_rounding.reset();
        self.squares_rounding.reset();
        self.long_squares_rounding.reset();
        self.long_sum_rounding.reset();
        self.resync = Resync::NotNeeded;
    }

    /// `None` until the window is full.
    #[inline]
    fn centered(&self) -> Option<Centered> {
        if !self.log_prices.is_full() {
            return None;
        }
        let prices = self.log_prices.as_slice();
        let n = (prices.len() - 1) as f64;
        // The drift per period, from the window's two ends, and how far it
        // is from the return the totals are measured about.
        let shift = (prices[prices.len() - 1] - prices[0]) / n - self.pivot;
        Some(Centered {
            n,
            shift,
            // Squares about the drift, from the total about the pivot.
            one_period: (-n * shift).fma(shift, self.one_period_squares),
        })
    }

    /// Lo and MacKinlay's variance ratio: the variance of `q`-period
    /// returns over `q` times the variance of one-period returns.
    ///
    /// The `q`-period returns overlap, and both variances are debiased: the
    /// one-period sum of squares is divided by `n - 1`, and `long_squares`
    /// (the `q`-period one, about the drift) by
    /// `m = q * (n - q + 1) * (1 - q / n)`.
    fn ratio(&self, centered: Centered, long_squares: f64) -> f64 {
        let Centered { n, one_period, .. } = centered;
        (long_squares / self.long_divisor) / (one_period / (n - 1.0))
    }

    /// The sum of squared `q`-period returns, each less the drift over `q`
    /// periods.
    fn long_squares_about_the_drift(&self, centered: Centered) -> f64 {
        let q = self.q as f64;
        let terms = centered.n - q + 1.0;
        crate::math::squares_about(self.long_squares, self.long_sum, terms, q * centered.shift)
    }

    /// Lo and MacKinlay's variance of the ratio when volatility changes
    /// over time: the sum over lags `j` from 1 to `q - 1` of
    /// `(2 * (1 - j / q))^2 * delta_j`.
    ///
    /// `delta_j` is `n` times the sum of `(a - mean)^2 * (b - mean)^2` over
    /// one-period returns `a` and `b` that are `j` apart, over the square
    /// of the one-period sum of squares. `lag_sum` is those sums with their
    /// weights, from [`weighted_lag_sum`](Self::weighted_lag_sum).
    fn ratio_variance(centered: Centered, lag_sum: f64) -> f64 {
        let Centered { n, one_period, .. } = centered;
        let one_period_squared = one_period * one_period;
        n * lag_sum / one_period_squared
    }

    /// The sum over lags `j` of `(2 * (1 - j / q))^2` times that lag's sum
    /// of `(a - mean)^2 * (b - mean)^2`.
    fn weighted_lag_sum(&self, centered: Centered) -> f64 {
        let Centered { n, shift, .. } = centered;
        let mut sum = 0.0;
        for (index, (totals, &weight)) in self.lags.iter().zip(&self.lag_weights).enumerate() {
            let lag = (index + 1) as f64;
            sum = weight.fma(totals.squares_about(shift, n - lag), sum);
        }
        sum
    }

    /// An estimate of the error rounding in the totals may put in the z
    /// statistic, as a share of the larger of `|z|` and 1.
    ///
    /// `z = sqrt(n / variance) * (ratio - 1)`, so it moves with three sums
    /// read from the totals: the weighted lag sums under `variance`, the
    /// one-period squares, and the `q`-period squares in `ratio`. Each
    /// one's error is its accumulated rounding (from [`RoundingEstimate`],
    /// at [`CONFIDENCE`](Self::CONFIDENCE) standard deviations) plus the
    /// rounding in taking the drift out, which is `EPSILON` times the sizes
    /// of the terms subtracted. Each is taken as a share of the sum as it
    /// is now, whatever size that is.
    // Bounds are written as they are derived; fused forms would hide them.
    #[allow(clippy::suboptimal_flops)]
    fn z_error(&self, centered: Centered) -> f64 {
        let Centered { n, one_period, .. } = centered;
        let lag_sum = self.weighted_lag_sum(centered);
        // Exactly nothing: no pair of returns both moved, and there is no
        // reading.
        if lag_sum == 0.0 {
            return 0.0;
        }
        // Only rounding residue, or a NaN. Advised whatever the residue's
        // sign, though below zero the reading comes out `None` (see `Resync`).
        if !(lag_sum > 0.0 && one_period > 0.0) {
            return f64::INFINITY;
        }
        let long = self.long_squares_about_the_drift(centered);

        let of_lag_sums = share(self.lag_sums_error(centered), lag_sum);
        let of_squares = share(self.squares_error(centered), one_period);
        let of_long = share(self.long_squares_error(centered), long);

        // The ratio's own error reaches z through `ratio - 1`, which may be
        // far smaller than the ratio.
        let ratio = self.ratio(centered, long);
        let scale = crate::math::sqrt(n / Self::ratio_variance(centered, lag_sum));
        let z = scale * (ratio - 1.0);
        let through_the_ratio = scale * ratio / z.abs().max(1.0);

        // z goes as the squares over the root of the lag sums.
        0.5 * of_lag_sums + of_squares + through_the_ratio * (of_long + of_squares)
    }

    /// The error in the weighted lag sum.
    #[allow(clippy::suboptimal_flops)]
    fn lag_sums_error(&self, centered: Centered) -> f64 {
        let Centered { n, shift, .. } = centered;
        let (squares, fourth) = (self.one_period_squares, self.fourth_powers);
        let shift_2 = shift * shift;
        let shift_4 = shift_2 * shift_2;

        // Each lag's sum about the drift is built from five totals. With
        // `fourth` and `squares` bounding their sizes, the variance of its
        // accumulated rounding is at most this.
        let adds = self.squares_rounding.adds();
        let variance = 9.0 * self.fourth_powers_rounding.variance()
            + 36.0 * shift_4 * self.squares_rounding.variance()
            + 8.0 * RoundingEstimate::variance_of(shift_4 * n, adds);
        // And evaluating it subtracts terms of these sizes.
        let evaluation =
            f64::EPSILON * (3.0 * fourth + 10.0 * shift_2 * squares + 3.0 * n * shift_4);
        (Self::CONFIDENCE * crate::math::sqrt(variance) + evaluation) * self.lag_weights_sum
    }

    /// The error in the one-period squares about the drift.
    #[allow(clippy::suboptimal_flops)]
    fn squares_error(&self, centered: Centered) -> f64 {
        let Centered { n, shift, .. } = centered;
        let evaluation = f64::EPSILON * (self.one_period_squares + n * shift * shift);
        self.squares_rounding.error(Self::CONFIDENCE) + evaluation
    }

    /// The error in the `q`-period squares about the drift.
    #[allow(clippy::suboptimal_flops)]
    fn long_squares_error(&self, centered: Centered) -> f64 {
        let q = self.q as f64;
        let drift = q * centered.shift;
        let terms = centered.n - q + 1.0;
        // `squares - 2 * drift * sum + terms * drift^2`.
        let variance = self.long_squares_rounding.variance()
            + 4.0 * drift * drift * self.long_sum_rounding.variance();
        let evaluation = f64::EPSILON
            * (self.long_squares + 2.0 * (drift * self.long_sum).abs() + terms * drift * drift);
        Self::CONFIDENCE * crate::math::sqrt(variance) + evaluation
    }

    #[inline]
    fn assess(&self) -> Resync {
        let Some(centered) = self.centered() else {
            return Resync::NotNeeded;
        };
        let z_error = self.z_error(centered);
        // Written so that a NaN, from a price that was not a number, advises.
        if z_error <= Self::ADVISE_ABOVE {
            return Resync::NotNeeded;
        }
        Resync::Advised { z_error }
    }

    /// Adds every term that ends at the newest price (`weight` 1).
    #[inline]
    fn add_terms_to_the_newest(&mut self, weight: f64) {
        let prices = self.log_prices.as_slice();
        let last = prices.len() - 1;
        if last == 0 {
            return;
        }
        let newest_return = prices[last] - prices[last - 1] - self.pivot;
        let square = newest_return * newest_return;
        self.one_period_squares = weight.fma(square, self.one_period_squares);
        self.fourth_powers = (weight * square).fma(square, self.fourth_powers);

        // Each earlier return, paired with the newest at its lag.
        for (index, totals) in self.lags.iter_mut().enumerate() {
            let lag = index + 1;
            if last <= lag {
                break;
            }
            let earlier = prices[last - lag] - prices[last - lag - 1] - self.pivot;
            totals.add(earlier, newest_return, weight);
        }

        if last >= self.q {
            let long_pivot = self.q as f64 * self.pivot;
            let long_return = prices[last] - prices[last - self.q] - long_pivot;
            self.long_sum = weight.fma(long_return, self.long_sum);
            self.long_squares = (weight * long_return).fma(long_return, self.long_squares);
        }
    }

    /// Adds every term that starts at the oldest price (`weight` 1), or
    /// removes them (`weight` -1). The window must be full.
    #[inline]
    fn add_terms_from_the_oldest(&mut self, weight: f64) {
        // Full: `window + 1` prices, and `window > q`.
        let prices = self.log_prices.as_slice();
        let oldest_return = prices[1] - prices[0] - self.pivot;
        let square = oldest_return * oldest_return;
        self.one_period_squares = weight.fma(square, self.one_period_squares);
        self.fourth_powers = (weight * square).fma(square, self.fourth_powers);

        // The oldest return, paired with each later one at its lag.
        for (index, totals) in self.lags.iter_mut().enumerate() {
            let lag = index + 1;
            let later = prices[lag + 1] - prices[lag] - self.pivot;
            totals.add(oldest_return, later, weight);
        }

        let long_pivot = self.q as f64 * self.pivot;
        let long_return = prices[self.q] - prices[0] - long_pivot;
        self.long_sum = weight.fma(long_return, self.long_sum);
        self.long_squares = (weight * long_return).fma(long_return, self.long_squares);
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
        let Some(prices) = window.checked_add(1) else {
            return Err(crate::ConfigError::Invalid("window is too large"));
        };
        // A full window's returns, and the horizon, as the formulas use them.
        let (returns, periods) = (window as f64, q as f64);
        let lag_weights = lag_weights(q);

        Ok(VarianceRatio {
            q,
            log_prices: SliceRing::new(prices, 0.0)?,
            pivot: 0.0,
            one_period_squares: 0.0,
            long_sum: 0.0,
            long_squares: 0.0,
            lags: vec![LagTotals::default(); q - 1].into_boxed_slice(),
            lag_weights_sum: lag_weights.iter().fold(0.0, |sum, weight| sum + weight),
            lag_weights,
            long_divisor: periods * (returns - periods + 1.0) * (1.0 - periods / returns),
            fourth_powers: 0.0,
            fourth_powers_rounding: RoundingEstimate::new(),
            squares_rounding: RoundingEstimate::new(),
            long_squares_rounding: RoundingEstimate::new(),
            long_sum_rounding: RoundingEstimate::new(),
            unchanged: 0,
            resync: Resync::NotNeeded,
            count: 0,
        })
    }
}

/// Lo and MacKinlay's weight on each lag's total, for lag 1 to `q - 1`:
/// `(2 * (1 - lag / q))^2`.
fn lag_weights(q: usize) -> Box<[f64]> {
    (1..q)
        .map(|lag| {
            let weight = 2.0 * (1.0 - lag as f64 / q as f64);
            weight * weight
        })
        .collect()
}

/// `error` as a share of `size`: infinite if there is an error and nothing
/// left for it to be a share of.
fn share(error: f64, size: f64) -> f64 {
    if error == 0.0 {
        return 0.0;
    }
    if size <= 0.0 {
        return f64::INFINITY;
    }
    error / size
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
        // no two neighboring returns both moved.
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

    /// Quiet noise with one print far off the market at `2 * window`, back
    /// on the next price.
    fn with_one_print(print: f64, window: usize, noise_size: f64) -> Vec<f64> {
        let mut noise = Noise(0x9E37_79B9_7F4A_7C15);
        let mut price = 100.0f64;
        (0..6 * window)
            .map(|i| {
                price *= (noise_size * noise.next()).exp();
                if i == 2 * window {
                    price * print
                } else {
                    price
                }
            })
            .collect()
    }

    #[test]
    fn a_bad_print_is_advised_once_it_leaves_and_resync_restores_the_reading() {
        for (print, q, window, noise_size) in [
            (0.01, 4, 64, 1e-5),
            (1e6, 4, 64, 1e-5),
            (0.01, 4, 500, 1e-4),
            (0.9, 8, 64, 1e-5),
        ] {
            let prices = with_one_print(print, window, noise_size);
            let mut vr = VarianceRatio::builder()
                .q(q)
                .window(window)
                .build()
                .unwrap();
            for (i, &p) in prices.iter().enumerate() {
                let state = vr.update(p);
                // Both of the print's returns are out once price 3 * window + 1
                // is in.
                if i <= 3 * window {
                    assert_eq!(state, Resync::NotNeeded, "print {print} price {i}");
                    continue;
                }
                let want = exact(&prices[i - window..=i], q).unwrap();
                if i <= 4 * window {
                    assert!(
                        matches!(state, Resync::Advised { .. }),
                        "print {print} price {i}: {state:?}"
                    );
                    // The ratio loses far less than the z statistic: even a
                    // print a million times off leaves it good to 1 in 1000.
                    if let Some(got) = vr.estimate() {
                        assert!(
                            (got.ratio - want.ratio).abs() <= 1e-3 * want.ratio,
                            "print {print} price {i}: {got:?} vs {want:?}"
                        );
                    }
                }
                if i == 4 * window {
                    vr.resync();
                }
                if i > 4 * window {
                    assert_eq!(state, Resync::NotNeeded, "print {print} price {i}");
                    let got = vr.estimate().unwrap();
                    assert!(
                        (got.ratio - want.ratio).abs() <= 1e-9 * want.ratio
                            && (got.z_statistic - want.z_statistic).abs() <= 1e-6,
                        "print {print} price {i}: {got:?} vs {want:?}"
                    );
                }
            }
        }
    }

    /// One scenario for the error estimate: `busy` returns of size `1e-4`,
    /// then `quiet` more, smaller by `fall` (reached over `gradual` returns,
    /// or at once), with an optional `spike` at the turn, in units of the
    /// typical return.
    struct Scenario {
        window: usize,
        q: usize,
        busy: usize,
        quiet: usize,
        fall: f64,
        gradual: usize,
        spike: f64,
    }

    impl Scenario {
        fn prices(&self, seed: u64) -> Vec<f64> {
            let mut noise = Noise(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut log_price = 100.0f64.ln();
            (0..self.busy + self.quiet)
                .map(|i| {
                    let after = i.saturating_sub(self.busy);
                    let scale = if i < self.busy {
                        1.0
                    } else if self.gradual > 0 {
                        let done = after.min(self.gradual) as f64 / self.gradual as f64;
                        self.fall.powf(-done)
                    } else {
                        1.0 / self.fall
                    };
                    log_price += 1e-4 * scale * noise.next();
                    let typical = 1e-4 / 3f64.sqrt();
                    if self.spike > 0.0 && i == self.busy {
                        log_price += self.spike * typical;
                    }
                    if self.spike > 0.0 && i == self.busy + 1 {
                        log_price -= self.spike * typical;
                    }
                    log_price.exp()
                })
                .collect()
        }
    }

    #[test]
    fn the_error_estimate_is_never_below_the_actual_error() {
        // Spikes, sudden and gradual falls in volatility, and a steady run:
        // wherever it is checked, the z statistic is within the estimate.
        let scenarios = [
            Scenario {
                window: 256,
                q: 4,
                busy: 2000,
                quiet: 1500,
                fall: 1.0,
                gradual: 0,
                spike: 1000.0,
            },
            Scenario {
                window: 1024,
                q: 4,
                busy: 4000,
                quiet: 4000,
                fall: 1.0,
                gradual: 0,
                spike: 3000.0,
            },
            Scenario {
                window: 256,
                q: 4,
                busy: 60_000,
                quiet: 2000,
                fall: 300.0,
                gradual: 0,
                spike: 0.0,
            },
            Scenario {
                window: 1024,
                q: 4,
                busy: 60_000,
                quiet: 12_000,
                fall: 1000.0,
                gradual: 8000,
                spike: 0.0,
            },
            Scenario {
                window: 500,
                q: 8,
                busy: 60_000,
                quiet: 3000,
                fall: 30.0,
                gradual: 0,
                spike: 0.0,
            },
            Scenario {
                window: 300,
                q: 8,
                busy: 80_000,
                quiet: 1000,
                fall: 1.0,
                gradual: 0,
                spike: 0.0,
            },
        ];
        for (index, scenario) in scenarios.iter().enumerate() {
            let prices = scenario.prices(index as u64 + 1);
            let (q, window) = (scenario.q, scenario.window);
            let mut vr = VarianceRatio::builder()
                .q(q)
                .window(window)
                .build()
                .unwrap();
            let mut first_notice = true;
            for (i, &p) in prices.iter().enumerate() {
                let raised = matches!(vr.update(p), Resync::Advised { .. }) && first_notice;
                first_notice &= !raised;
                // The exact estimate costs the window: checked at intervals
                // and at the update that raises the notice.
                if i < scenario.busy || !(i % 97 == 0 || raised) {
                    continue;
                }
                let (Some(got), Some(want)) = (vr.estimate(), exact(&prices[i - window..=i], q))
                else {
                    continue;
                };
                let actual =
                    (got.z_statistic - want.z_statistic).abs() / want.z_statistic.abs().max(1.0);
                let estimate = vr.z_error(vr.centered().unwrap());
                assert!(
                    actual <= estimate,
                    "scenario {index} price {i}: actual {actual} estimate {estimate}"
                );
            }
        }
    }

    /// Feeds `returns` (of the log price) and, from `from` on at every
    /// `every`th update, checks the z statistic against the window computed
    /// directly: its error must be within the estimate. Calls `resync` after
    /// update `resync_at`.
    fn assert_the_estimate_covers(
        q: usize,
        window: usize,
        returns: impl Iterator<Item = f64>,
        from: usize,
        every: usize,
        resync_at: Option<usize>,
    ) {
        let mut vr = VarianceRatio::builder()
            .q(q)
            .window(window)
            .build()
            .unwrap();
        let mut log_price = 100.0f64.ln();
        let mut held = alloc::collections::VecDeque::with_capacity(window + 1);
        let mut checked = 0;
        for (i, r) in returns.enumerate() {
            log_price += r;
            let price = log_price.exp();
            vr.update(price);
            if held.len() == window + 1 {
                held.pop_front();
            }
            held.push_back(price);
            if resync_at == Some(i) {
                vr.resync();
            }
            if i < from || i % every != 0 {
                continue;
            }
            let (Some(got), Some(want)) = (vr.estimate(), exact(held.make_contiguous(), q)) else {
                continue;
            };
            let actual =
                (got.z_statistic - want.z_statistic).abs() / want.z_statistic.abs().max(1.0);
            let estimate = vr.z_error(vr.centered().unwrap());
            assert!(
                actual <= estimate,
                "update {i}: z {} against {}, error {actual}, estimate {estimate}",
                got.z_statistic,
                want.z_statistic
            );
            checked += 1;
        }
        assert!(checked > 100, "{checked}");
    }

    #[test]
    fn the_error_estimate_covers_moves_that_are_seldom_next_to_each_other() {
        // A busy spell, then a price that moves a hundred times less and
        // only on every other update, but for one adjacent pair: the lag-1
        // sum is tiny beside the squares, and all of it is that pair.
        let (q, window, busy) = (2, 1024, 100_000);
        let mut noise = Noise(77);
        let returns = (0..busy + 3 * window).map(move |i| {
            if i < busy {
                return 1e-3 * noise.next();
            }
            let after = i - busy;
            if after % 2 == 0 || after == window + 101 {
                return 1e-5 * noise.next();
            }
            0.0
        });
        assert_the_estimate_covers(q, window, returns, busy + window, 1, None);
    }

    #[test]
    fn the_error_estimate_covers_a_trend_that_turns_after_resync() {
        // A trend far stronger than the noise, a resync, and then the trend
        // reverses: the totals are measured about a drift that no longer
        // holds, and the turn itself is one large return about the new one.
        for (q, window, turned, every) in [(4, 1024, -1e-3, 1), (16, 4096, -2e-3, 13)] {
            let mut noise = Noise(99);
            let returns = (0..6 * window)
                .map(move |i| if i < 3 * window { 1e-3 } else { turned } + 1e-7 * noise.next());
            assert_the_estimate_covers(q, window, returns, window + 1, every, Some(3 * window - 1));
        }
    }

    #[test]
    fn falling_volatility_is_advised_and_a_steady_market_is_not() {
        // A thousandfold fall after a long busy spell loses the z statistic
        // its digits; thirtyfold does not, and nor does a hundredfold burst.
        let collapse = Scenario {
            window: 256,
            q: 4,
            busy: 60_000,
            quiet: 2000,
            fall: 1000.0,
            gradual: 0,
            spike: 0.0,
        };
        let easing = Scenario {
            window: 256,
            q: 4,
            busy: 60_000,
            quiet: 2000,
            fall: 30.0,
            gradual: 0,
            spike: 0.0,
        };
        for (scenario, advised) in [(collapse, true), (easing, false)] {
            let mut vr = VarianceRatio::builder()
                .q(scenario.q)
                .window(scenario.window)
                .build()
                .unwrap();
            let mut last = Resync::NotNeeded;
            for p in scenario.prices(1) {
                last = vr.update(p);
            }
            assert_eq!(matches!(last, Resync::Advised { .. }), advised, "{last:?}");
            vr.resync();
            assert_eq!(vr.update(100.0), Resync::NotNeeded);
        }
    }

    #[test]
    fn a_price_that_is_not_a_number_is_advised_and_resync_recovers() {
        let prices = prices(200);
        let mut vr = VarianceRatio::builder().q(3).window(50).build().unwrap();
        for &p in &prices[..100] {
            vr.update(p);
        }
        assert!(matches!(vr.update(f64::NAN), Resync::Advised { .. }));
        // The reading is not a number until the totals are rebuilt without
        // it: 51 prices on, it has left the window.
        for &p in &prices[100..152] {
            assert!(matches!(vr.update(p), Resync::Advised { .. }));
        }
        vr.resync();
        let got = vr.estimate().unwrap();
        let want = exact(&prices[101..152], 3).unwrap();
        assert!(
            (got.ratio - want.ratio).abs() < 1e-9 * want.ratio,
            "{got:?} {want:?}"
        );
        assert_eq!(vr.update(prices[152]), Resync::NotNeeded);
    }

    #[test]
    fn resync_before_the_window_is_full_changes_nothing_that_is_read() {
        let prices = prices(120);
        let mut vr = VarianceRatio::builder().q(3).window(50).build().unwrap();
        let mut plain = vr.clone();
        // With no price, with one, and part way through filling.
        vr.resync();
        for (i, &p) in prices.iter().enumerate() {
            vr.update(p);
            plain.update(p);
            if i == 0 || i == 20 {
                vr.resync();
            }
            match (vr.estimate(), plain.estimate()) {
                (Some(a), Some(b)) => assert!(
                    (a.ratio - b.ratio).abs() < 1e-9 * b.ratio
                        && (a.z_statistic - b.z_statistic).abs() < 1e-6,
                    "price {i}: {a:?} {b:?}"
                ),
                (a, b) => assert_eq!(a, b, "price {i}"),
            }
        }
    }

    #[test]
    fn the_advice_stays_until_resync() {
        let prices = with_one_print(0.01, 64, 1e-5);
        let mut vr = VarianceRatio::builder().q(4).window(64).build().unwrap();
        let mut first = None;
        for &p in &prices {
            let state = vr.update(p);
            if let Some(first) = first {
                // The same notice, value included, on every later update.
                assert_eq!(state, first);
            } else if matches!(state, Resync::Advised { .. }) {
                first = Some(state);
            }
        }
        assert!(first.is_some());
        vr.resync();
        assert_eq!(vr.update(prices[prices.len() - 1]), Resync::NotNeeded);
    }

    #[test]
    fn a_resync_with_the_print_still_in_the_window_is_advised_again_when_it_leaves() {
        let (q, window) = (4, 64);
        let prices = with_one_print(1e6, window, 1e-5);
        let mut vr = VarianceRatio::builder()
            .q(q)
            .window(window)
            .build()
            .unwrap();
        let mut advised_again = false;
        for (i, &p) in prices.iter().enumerate() {
            let state = vr.update(p);
            if i == 2 * window + 10 {
                // The print is in the window: a resync cannot keep the
                // digits of the terms beside it.
                vr.resync();
            }
            if i > 3 * window && i < 4 * window {
                advised_again |= matches!(state, Resync::Advised { .. });
            }
            if i == 4 * window {
                vr.resync();
            }
            if i > 4 * window {
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
        assert!(advised_again);
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
            let state = vr.update(p);
            // Measured about zero, a trend this strong is advised as soon
            // as the window fills; one resync settles it.
            if i == window {
                assert!(matches!(state, Resync::Advised { .. }), "{state:?}");
                vr.resync();
            }
            if i > window {
                assert_eq!(state, Resync::NotNeeded, "price {i}");
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
            // A hundredfold burst is well within what the totals hold.
            assert_eq!(vr.update(p), Resync::NotNeeded, "price {i}");
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
        assert_eq!(
            b().q(5).window(usize::MAX).build().unwrap_err(),
            Invalid("window is too large")
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
