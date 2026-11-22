use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

use crate::math::MulAdd;

mod kernel;

/// Hurst exponent of a price series, by rescaled-range analysis.
///
/// `H` measures memory in the returns: 0.5 for independent returns (a random
/// walk), below 0.5 for mean reversion, above 0.5 for persistence.
///
/// The rescaled range `R/S` of a stretch of returns is the range of their
/// running sum about the mean, divided by their standard deviation. It grows
/// like `n^H` with the length `n` of the stretch, so `H` is the slope of
/// `ln(R/S)` against `ln(n)`. This type measures `R/S` at the whole window,
/// at each half, each quarter and so on, and fits that slope, after
/// dividing each `R/S` by the value expected of independent returns (Anis
/// and Lloyd, 1976, with Peters' term for the `n - 1` standard deviation).
/// It is the procedure Weron (2002, "Estimating long-range dependence",
/// *Physica A*) describes, and gives the value `nolds.hurst_rs` reports
/// with `fit="poly"` on the same window sizes.
///
/// `update` stores the price; the exponent is computed when read, in time
/// proportional to the window times the number of sizes. Read it per bar,
/// not per tick. No update to the rescaled range exists as the window
/// slides, because the mean it is measured about moves.
///
/// # Reading it
///
/// On independent returns the estimate has a spread of about 0.04 at a
/// window of 1024 and 0.03 at 4096; a difference from 0.5 smaller than that
/// is noise. Short-lived correlation also moves it: raise
/// `smallest_window` to look past that, at the cost of a wider spread.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::Hurst;
///
/// let mut hurst = Hurst::builder().window(256).build().unwrap();
/// // A price that reverses every step is strongly mean-reverting.
/// for i in 0..300 {
///     hurst.update(if i % 2 == 0 { 100.0 } else { 100.5 });
/// }
/// assert!(hurst.exponent().unwrap() < 0.3);
/// ```
#[derive(Debug, Clone)]
pub struct Hurst {
    /// Log prices, each stored twice, half the buffer apart.
    log_prices: Box<[f64]>,
    /// Where the next price goes, in the first half.
    head: usize,
    count: u64,
    /// The stretch lengths, longest first.
    scales: Box<[Scale]>,
}

/// One stretch length the rescaled range is measured at.
#[derive(Debug, Clone, Copy)]
struct Scale {
    /// Length in returns.
    size: usize,
    /// `ln` of the rescaled range expected of independent returns.
    ln_expected: f64,
    /// This length's weight in the least-squares slope:
    /// `(x - mean(x)) / sum((x - mean(x))^2)` for `x = ln(size)`.
    slope_weight: f64,
}

/// Builder for [`Hurst`].
#[derive(Debug, Clone)]
pub struct HurstBuilder {
    window: Option<usize>,
    smallest_window: usize,
}

impl Hurst {
    /// Creates a builder.
    #[must_use]
    pub fn builder() -> HurstBuilder {
        HurstBuilder {
            window: None,
            smallest_window: 8,
        }
    }

    /// Feeds a price. The logarithm is taken here.
    ///
    /// Does not validate `price`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, price: f64) {
        let log_price = crate::math::ln(price);
        let capacity = self.log_prices.len() / 2;
        self.count += 1;

        // PERF: written twice, so the newest prices are always one slice.
        self.log_prices[self.head] = log_price;
        self.log_prices[self.head + capacity] = log_price;
        self.head += 1;
        if self.head == capacity {
            self.head = 0;
        }
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
    /// use nexus_stats_core::{DataError, statistics::Hurst};
    ///
    /// let mut hurst = Hurst::builder().window(256).build().unwrap();
    /// assert_eq!(hurst.checked_update(100.0), Ok(()));
    /// assert_eq!(hurst.checked_update(0.0), Err(DataError::OutOfRange));
    /// assert_eq!(hurst.count(), 1);
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

    /// The Hurst exponent over the window, or `None` until the window is
    /// full, or if no stretch of some length had returns that differ.
    ///
    /// A stretch whose returns are all equal has no rescaled range and is
    /// left out of its length's average. `nolds` leaves out a stretch whose
    /// range is exactly zero; here "equal" allows for rounding, by the test
    /// SciPy applies to a variance (`skew`, `kurtosis`): returns are
    /// differences of log prices, so a variance at or below
    /// `(EPSILON * log_price)^2` is rounding.
    ///
    /// Costs time proportional to the window times the number of lengths.
    #[must_use]
    pub fn exponent(&self) -> Option<f64> {
        /// `R/S` of the returns between consecutive `log_prices`, or `None`
        /// if they are equal to within rounding.
        fn rescaled_range(log_prices: &[f64]) -> Option<f64> {
            let returns = log_prices.len() - 1;
            let n = returns as f64;
            // The running sum of returns is a difference of log prices.
            let mean = (log_prices[returns] - log_prices[0]) / n;
            let sums = kernel::stretch_sums(log_prices, mean);

            // SciPy's zero-variance test (`skew`, `kurtosis`): a variance at
            // or below `(EPSILON * x)^2` is rounding, where `x` is the size
            // of the values subtracted. Here those are log prices.
            let variance = sums.squares / (n - 1.0);
            if variance <= crate::math::rounding_variance(log_prices[0]) {
                return None;
            }
            Some((sums.highest - sums.lowest) / crate::math::sqrt(variance))
        }

        let capacity = self.log_prices.len() / 2;
        if self.count < capacity as u64 {
            return None;
        }
        // Oldest first.
        let log_prices = &self.log_prices[self.head..self.head + capacity];
        let returns = capacity - 1;

        // Least-squares slope of `ln(R/S) - ln(expected)` on `ln(size)`.
        let mut slope = 0.0;
        for scale in &self.scales {
            let stretches = returns / scale.size;
            // Stretches end at the newest price; older leftovers are unused.
            let unused = returns - stretches * scale.size;

            let (mut total, mut moved) = (0.0, 0u32);
            for stretch in 0..stretches {
                let start = unused + stretch * scale.size;
                if let Some(ratio) = rescaled_range(&log_prices[start..=start + scale.size]) {
                    total += ratio;
                    moved += 1;
                }
            }
            if moved == 0 {
                return None;
            }

            let excess = crate::math::ln(total / f64::from(moved)) - scale.ln_expected;
            slope = scale.slope_weight.fma(excess, slope);
        }

        // The expected values grow like sqrt(n): dividing by them took 0.5
        // off the slope.
        Some(0.5 + slope)
    }

    /// The window, in returns.
    #[must_use]
    pub fn window(&self) -> usize {
        self.log_prices.len() / 2 - 1
    }

    /// Number of prices fed since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the window is full.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= (self.log_prices.len() / 2) as u64
    }

    /// Empties the window. Parameters and allocation unchanged.
    pub fn reset(&mut self) {
        self.head = 0;
        self.count = 0;
    }
}

impl HurstBuilder {
    /// The window, in returns. Required. The window holds one more price
    /// than this.
    #[must_use]
    pub fn window(mut self, returns: usize) -> Self {
        self.window = Some(returns);
        self
    }

    /// The shortest stretch measured, in returns. Default 8, at least 4.
    ///
    /// The window is halved until it would fall below this. A larger value
    /// looks past short-lived correlation and widens the estimate's spread.
    #[must_use]
    pub fn smallest_window(mut self, returns: usize) -> Self {
        self.smallest_window = returns;
        self
    }

    /// Builds the estimator.
    ///
    /// # Errors
    ///
    /// - `Missing("window")` if `window` was not set.
    /// - `Invalid` if `smallest_window` is below 4, or `window` is less than
    ///   four times `smallest_window` (three lengths are needed for the
    ///   fit).
    pub fn build(self) -> Result<Hurst, crate::ConfigError> {
        let window = self.window.ok_or(crate::ConfigError::Missing("window"))?;
        if self.smallest_window < 4 {
            return Err(crate::ConfigError::Invalid("smallest_window must be >= 4"));
        }
        if window / 4 < self.smallest_window {
            return Err(crate::ConfigError::Invalid(
                "window must be at least 4 times smallest_window",
            ));
        }

        let mut sizes = Vec::new();
        let mut size = window;
        while size >= self.smallest_window {
            sizes.push(size);
            size /= 2;
        }

        // The slope's weights depend only on the lengths.
        let ln_size = |size: usize| crate::math::ln(size as f64);
        let mean = sizes.iter().map(|&s| ln_size(s)).sum::<f64>() / sizes.len() as f64;
        let spread: f64 = sizes
            .iter()
            .map(|&s| (ln_size(s) - mean) * (ln_size(s) - mean))
            .sum();
        let scales: Vec<Scale> = sizes
            .iter()
            .map(|&size| Scale {
                size,
                ln_expected: crate::math::ln(expected_rescaled_range(size)),
                slope_weight: (ln_size(size) - mean) / spread,
            })
            .collect();

        Ok(Hurst {
            log_prices: vec![0.0; 2 * (window + 1)].into_boxed_slice(),
            head: 0,
            count: 0,
            scales: scales.into_boxed_slice(),
        })
    }
}

/// The rescaled range expected of `n` independent returns: Anis and Lloyd
/// (1976), with Peters' `(n - 1/2) / n` term, which goes with the `n - 1`
/// standard deviation. Above 340 the gamma ratio is replaced by its limit,
/// as in Weron (2002).
fn expected_rescaled_range(n: usize) -> f64 {
    let size = n as f64;
    let sum: f64 = (1..n)
        .map(|i| crate::math::sqrt((n - i) as f64 / i as f64))
        .sum();
    let gamma_ratio = if n <= 340 {
        let ln_ratio =
            crate::math::ln_gamma((size - 1.0) / 2.0) - crate::math::ln_gamma(size / 2.0);
        crate::math::exp(ln_ratio) / crate::math::sqrt(core::f64::consts::PI)
    } else {
        1.0 / crate::math::sqrt(size * core::f64::consts::FRAC_PI_2)
    };
    (size - 0.5) / size * gamma_ratio * sum
}

#[cfg(test)]
// Test series are written as plain arithmetic.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;

    /// Prices whose log returns are `returns`.
    fn prices_from(returns: &[f64]) -> Vec<f64> {
        let mut log_price = 100.0f64.ln();
        let mut prices = vec![log_price.exp()];
        for r in returns {
            log_price += r;
            prices.push(log_price.exp());
        }
        prices
    }

    fn exponent(prices: &[f64], smallest: usize) -> Option<f64> {
        let mut hurst = Hurst::builder()
            .window(prices.len() - 1)
            .smallest_window(smallest)
            .build()
            .unwrap();
        for &p in prices {
            hurst.update(p);
        }
        hurst.exponent()
    }

    /// Returns driven by the logistic map: deterministic and rough.
    fn logistic_returns(len: usize) -> Vec<f64> {
        let mut x = 0.3f64;
        (0..len)
            .map(|_| {
                x = 3.99 * x * (1.0 - x);
                0.01 * (x - 0.5)
            })
            .collect()
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

    /// Returns `x_t = phi * x_{t-1} + noise`.
    fn autoregressive(len: usize, phi: f64) -> Vec<f64> {
        let mut noise = Noise(0x9E37_79B9_7F4A_7C15);
        let mut previous = 0.0;
        (0..len)
            .map(|_| {
                previous = phi * previous + 0.001 * noise.next();
                previous
            })
            .collect()
    }

    #[test]
    fn expected_rescaled_range_matches_nolds() {
        // nolds.expected_rs(n)
        for (n, expected) in [
            (8, 2.460_558_978_166_877_5),
            (16, 3.909_420_347_501_904),
            (340, 21.960_745_554_092_167),
            (512, 27.167_348_739_755_273),
        ] {
            let got = expected_rescaled_range(n);
            assert!((got - expected).abs() < 1e-9 * expected, "{n}: {got}");
        }
    }

    #[test]
    fn matches_nolds_reference_values() {
        // nolds.hurst_rs(returns[:window], nvals=<window halved down to
        // smallest>, fit="poly", corrected=True, unbiased=True)
        let returns = logistic_returns(2048);
        for (window, smallest, expected) in [
            (256, 8, 0.386_537_374_788_814),
            (1024, 8, 0.518_481_755_216_171_2),
            (1024, 32, 0.571_211_269_432_928_4),
        ] {
            let got = exponent(&prices_from(&returns[..window]), smallest).unwrap();
            assert!(
                (got - expected).abs() < 1e-6,
                "window {window} smallest {smallest}: {got} vs {expected}"
            );
        }
    }

    #[test]
    fn independent_returns_read_near_one_half() {
        let got = exponent(&prices_from(&autoregressive(4096, 0.0)), 8).unwrap();
        assert!((got - 0.5).abs() < 0.08, "{got}");
    }

    #[test]
    fn mean_reverting_reads_below_and_persistent_above() {
        let reverting = exponent(&prices_from(&autoregressive(4096, -0.5)), 8).unwrap();
        let persistent = exponent(&prices_from(&autoregressive(4096, 0.5)), 8).unwrap();
        assert!(reverting < 0.47, "{reverting}");
        assert!(persistent > 0.53, "{persistent}");
    }

    #[test]
    fn the_window_slides() {
        let prices = prices_from(&logistic_returns(700));
        let mut hurst = Hurst::builder().window(256).build().unwrap();
        for &p in &prices {
            hurst.update(p);
        }
        // The same as a fresh estimator fed only the newest 257 prices.
        let newest = &prices[prices.len() - 257..];
        assert_eq!(hurst.exponent(), exponent(newest, 8));
        assert!(hurst.exponent().is_some());
    }

    #[test]
    fn a_window_that_does_not_halve_evenly_uses_the_newest_prices() {
        // 100 returns: lengths 100, 50, 25, 12. The length-12 stretches
        // cover the newest 96 returns.
        let prices = prices_from(&logistic_returns(100));
        let got = exponent(&prices, 8).unwrap();
        assert!(got.is_finite() && (0.0..1.0).contains(&got), "{got}");

        // Changing the four oldest returns, which only the two longest
        // lengths use, must change the reading; so must changing the
        // newest, which every length uses.
        let mut older = logistic_returns(100);
        older[1] += 0.004;
        assert_ne!(exponent(&prices_from(&older), 8), Some(got));
        let mut newer = logistic_returns(100);
        newer[98] += 0.004;
        assert_ne!(exponent(&prices_from(&newer), 8), Some(got));
    }

    #[test]
    fn scaling_every_price_changes_nothing() {
        let prices = prices_from(&logistic_returns(256));
        let scaled: Vec<f64> = prices.iter().map(|p| p * 1000.0).collect();
        let (a, b) = (exponent(&prices, 8).unwrap(), exponent(&scaled, 8).unwrap());
        assert!((a - b).abs() < 1e-9, "{a} {b}");
    }

    #[test]
    fn flat_stretches_are_left_out() {
        // A flat first eighth: some short stretches have no range.
        let mut returns = logistic_returns(256);
        for r in &mut returns[..32] {
            *r = 0.0;
        }
        assert!(exponent(&prices_from(&returns), 8).is_some());
        // A price that never moves has no exponent.
        assert_eq!(exponent(&[100.0; 257], 8), None);
    }

    #[test]
    fn returns_equal_to_within_rounding_are_left_out() {
        // A price that grows by the same factor every tick: the log returns
        // differ only in their last digits.
        let steady: Vec<f64> = (0..257)
            .map(|i| 100.0 * (0.001 * f64::from(i)).exp())
            .collect();
        assert_eq!(exponent(&steady, 8), None);

        // The same steady growth for the oldest eighth of a moving series:
        // those stretches are left out, and the rest still give a reading
        // within the usual range.
        let mut returns = logistic_returns(256);
        for r in &mut returns[..32] {
            *r = 0.001;
        }
        let got = exponent(&prices_from(&returns), 8).unwrap();
        assert!((0.0..1.0).contains(&got), "{got}");
    }

    #[test]
    fn none_until_the_window_is_full() {
        let prices = prices_from(&logistic_returns(64));
        let mut hurst = Hurst::builder().window(64).build().unwrap();
        for &p in &prices[..64] {
            hurst.update(p);
            assert_eq!(hurst.exponent(), None);
            assert!(!hurst.is_primed());
        }
        hurst.update(prices[64]);
        assert!(hurst.is_primed());
        assert!(hurst.exponent().is_some());
    }

    #[test]
    fn reset_empties_the_window() {
        let prices = prices_from(&logistic_returns(300));
        let mut hurst = Hurst::builder().window(64).build().unwrap();
        for &p in &prices {
            hurst.update(p);
        }
        hurst.reset();
        assert_eq!((hurst.count(), hurst.exponent()), (0, None));
        for &p in &prices[..65] {
            hurst.update(p);
        }
        assert_eq!(hurst.exponent(), exponent(&prices[..65], 8));
    }

    #[test]
    fn builder_validation() {
        use crate::ConfigError::{Invalid, Missing};
        let b = Hurst::builder;
        assert_eq!(b().build().unwrap_err(), Missing("window"));
        assert_eq!(
            b().window(64).smallest_window(3).build().unwrap_err(),
            Invalid("smallest_window must be >= 4")
        );
        assert_eq!(
            b().window(31).build().unwrap_err(),
            Invalid("window must be at least 4 times smallest_window")
        );
        assert_eq!(b().window(32).build().unwrap().window(), 32);
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let prices = prices_from(&logistic_returns(64));
        let mut hurst = Hurst::builder().window(64).build().unwrap();
        for &p in &prices {
            hurst.checked_update(p).unwrap();
        }
        let before = (hurst.count(), hurst.exponent());

        assert_eq!(hurst.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(hurst.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(hurst.checked_update(0.0), Err(OutOfRange));
        assert_eq!(hurst.checked_update(-1.0), Err(OutOfRange));

        assert_eq!((hurst.count(), hurst.exponent()), before);
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = Hurst::builder().window(64).build().unwrap();
        let mut unchecked = checked.clone();
        for &p in &prices_from(&logistic_returns(100)) {
            checked.checked_update(p).unwrap();
            unchecked.update(p);
        }
        assert_eq!(checked.exponent(), unchecked.exponent());
    }

    #[test]
    fn update_does_not_validate() {
        let mut prices = prices_from(&logistic_returns(64));
        prices[10] = f64::NAN;
        let mut hurst = Hurst::builder().window(64).build().unwrap();
        for &p in &prices {
            hurst.update(p);
        }
        assert!(hurst.exponent().is_none_or(f64::is_nan));
    }
}
