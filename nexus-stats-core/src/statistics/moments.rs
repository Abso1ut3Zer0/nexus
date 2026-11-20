use crate::math::MulAdd;
use crate::statistics::running_mean::step_mean;

/// Online skewness and kurtosis via Pébay's higher-moment extension
/// of Welford's algorithm (Pébay, 2008).
///
/// Numerically stable single-pass computation of mean, variance,
/// skewness, and excess kurtosis. Supports merging partial results
/// via Pébay's parallel aggregation formulas.
///
/// # Use Cases
/// - Distribution shape monitoring (is latency becoming skewed?)
/// - Fat-tail detection (kurtosis spike → regime change)
/// - Quality control (symmetric vs asymmetric error distributions)
///
/// Computes population (not sample-corrected) skewness and kurtosis.
/// For streaming use cases with n > 100, population and sample estimators
/// are indistinguishable. For small-sample inference (n < 30), use a
/// batch estimator with Bessel's correction instead.
///
/// # Complexity
/// - O(1) per update, 40 bytes state, zero allocation.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::Moments;
///
/// let mut m = Moments::new();
/// for i in 1..=1000u64 { m.update(i as f64); }
/// // Uniform distribution: skewness ≈ 0, kurtosis ≈ -1.2
/// let skew = m.shape().unwrap().skewness;
/// assert!(skew.abs() < 0.1);
/// ```
#[derive(Debug, Clone)]
pub struct Moments {
    count: u64,
    mean: f64,
    m2: f64,
    m3: f64,
    m4: f64,
}

/// The shape of a distribution, from [`Moments::shape`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Shape {
    /// Skewness. Zero for a symmetric distribution, positive when the
    /// longer tail is on the right.
    pub skewness: f64,
    /// Excess kurtosis. Zero for a normal distribution, positive for
    /// heavier tails.
    pub excess_kurtosis: f64,
}

impl Shape {
    /// Kurtosis: [`excess_kurtosis`](Self::excess_kurtosis) plus 3.
    #[inline]
    #[must_use]
    pub fn kurtosis(&self) -> f64 {
        self.excess_kurtosis + 3.0
    }
}

/// Below this a divisor has lost precision to underflow.
#[cfg(any(feature = "std", feature = "libm"))]
const SMALLEST_DIVISOR: f64 = f64::MIN_POSITIVE / f64::EPSILON;

impl Moments {
    /// Creates a new empty accumulator.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            count: 0,
            mean: 0.0,
            m2: 0.0,
            m3: 0.0,
            m4: 0.0,
        }
    }

    /// The largest magnitude [`checked_update`](Self::checked_update)
    /// accepts: `1e60`.
    ///
    /// Within it, a sum of fourth powers of differences cannot overflow for
    /// any stream length: `2^64 * (2e60)^4 < 1e261`.
    pub const INPUT_LIMIT: f64 = 1e60;

    /// Feeds a sample.
    ///
    /// Does not validate `sample`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::statistics::Moments;
    ///
    /// let mut m = Moments::new();
    /// m.update(1.0);
    /// m.update(3.0);
    /// assert_eq!(m.mean(), Some(2.0));
    /// ```
    #[inline]
    pub fn update(&mut self, sample: f64) {
        self.count += 1;
        let n = self.count as f64;
        let weight = 1.0 / n;
        let deviation = step_mean(&mut self.mean, sample, weight);
        // How far the mean moved, and what the sample adds to `m2`.
        let step = deviation.before * weight;
        let spread = deviation.before * deviation.after;
        let step_sq = step * step;

        // Higher moments first: each uses the lower ones from before this
        // sample. Written with fused multiply-adds, `a.fma(b, c) = a * b + c`:
        //
        //   m4 += spread * (step² * (n² - 3n + 3)) + 6 * step² * m2 - 4 * step * m3
        //   m3 += spread * step * (n - 2) - 3 * step * m2
        //   m2 += spread
        let poly = n.fma(n - 3.0, 3.0);
        // `step_sq * poly` first: `spread * step_sq` can underflow.
        let m4_from_m2 = spread.fma(step_sq * poly, 6.0 * step_sq * self.m2);
        self.m4 += (-4.0 * step).fma(self.m3, m4_from_m2);
        self.m3 += (spread * step).fma(n - 2.0, -3.0 * step * self.m2);
        self.m2 += spread;
    }

    /// Checked update. Feeds `sample`, or returns an error and leaves the
    /// accumulator unchanged if `sample` is NaN, infinite, or larger in
    /// magnitude than [`Moments::INPUT_LIMIT`].
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `sample`
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if `sample` is
    ///   infinite.
    /// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if `sample`
    ///   is finite and larger in magnitude than `Moments::INPUT_LIMIT`.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::{DataError, statistics::Moments};
    ///
    /// let mut m = Moments::new();
    /// assert_eq!(m.checked_update(1.0), Ok(()));
    /// assert_eq!(m.checked_update(1e61), Err(DataError::OutOfRange));
    /// assert_eq!(m.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(&mut self, sample: f64) -> Result<(), crate::DataError> {
        crate::math::check_input(sample, Self::INPUT_LIMIT)?;
        self.update(sample);
        Ok(())
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Running mean, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn mean(&self) -> Option<f64> {
        if self.count == 0 {
            return None;
        }

        Some(self.mean)
    }

    /// Sample variance (N-1 denominator), or `None` if < 2 samples.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> Option<f64> {
        if self.count < 2 {
            return None;
        }

        Some(self.m2 / (self.count - 1) as f64)
    }

    /// Population variance (N denominator), or `None` if empty.
    #[inline]
    #[must_use]
    pub fn population_variance(&self) -> Option<f64> {
        if self.count == 0 {
            return None;
        }

        Some(self.m2 / self.count as f64)
    }

    /// Sample standard deviation, or `None` if < 2 samples.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn std_dev(&self) -> Option<f64> {
        self.variance().map(crate::math::sqrt)
    }

    /// Skewness and excess kurtosis (population definitions).
    ///
    /// `None` with fewer than four samples, or when the data is too close
    /// to constant for a shape to be resolved:
    ///
    /// - the variance is at or below `(f64::EPSILON * mean)^2`. This is the
    ///   test SciPy's `skew` and `kurtosis` use for "all values are equal"
    ///   once rounding is allowed for. Just above it a one-pass estimate
    ///   keeps only a few digits;
    /// - the squared variance underflows, which that test misses for tiny
    ///   data centred on zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::statistics::Moments;
    ///
    /// let mut m = Moments::new();
    /// for x in [1.0, 2.0, 3.0, 4.0, 5.0] {
    ///     m.update(x);
    /// }
    /// let shape = m.shape().unwrap();
    /// assert_eq!(shape.skewness, 0.0);
    /// assert!((shape.excess_kurtosis + 1.3).abs() < 1e-12);
    /// ```
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn shape(&self) -> Option<Shape> {
        if self.count < 4 {
            return None;
        }
        let n = self.count as f64;
        let variance = self.m2 / n;
        let rounding = f64::EPSILON * self.mean;
        if variance <= rounding * rounding {
            return None;
        }
        let variance_sq = variance * variance;
        if variance_sq < SMALLEST_DIVISOR {
            return None;
        }

        Some(Shape {
            skewness: (self.m3 / n) / (variance * crate::math::sqrt(variance)),
            excess_kurtosis: (self.m4 / n) / variance_sq - 3.0,
        })
    }

    /// Whether enough data has been collected for all queries (>= 4).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= 4
    }

    /// Merges another accumulator into this one (Pébay's parallel algorithm).
    ///
    /// After merging, `self` contains the statistics of the combined
    /// dataset. The other accumulator is unchanged.
    #[inline]
    #[allow(clippy::suspicious_operation_groupings)]
    pub fn merge(&mut self, other: &Self) {
        if other.count == 0 {
            return;
        }
        if self.count == 0 {
            *self = other.clone();
            return;
        }

        let n_a = self.count as f64;
        let n_b = other.count as f64;
        let n = n_a + n_b;
        let delta = other.mean - self.mean;
        let delta2 = delta * delta;
        let delta3 = delta2 * delta;
        let delta4 = delta2 * delta2;

        let new_m4 = self.m4
            + other.m4
            + delta4 * n_a * n_b * n_b.fma(n_b, n_a.fma(n_a, -(n_a * n_b))) / (n * n * n)
            + 6.0 * delta2 * (n_a * n_a).fma(other.m2, n_b * n_b * self.m2) / (n * n)
            + 4.0 * delta * n_a.fma(other.m3, -(n_b * self.m3)) / n;

        let new_m3 = self.m3
            + other.m3
            + delta3 * n_a * n_b * (n_a - n_b) / (n * n)
            + 3.0 * delta * n_a.fma(other.m2, -(n_b * self.m2)) / n;

        let new_m2 = self.m2 + other.m2 + delta2 * n_a * n_b / n;

        self.mean += delta * n_b / n;
        self.count += other.count;
        self.m2 = new_m2;
        self.m3 = new_m3;
        self.m4 = new_m4;
    }

    /// Resets to empty state.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new();
    }
}

impl Default for Moments {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    #[test]
    fn uniform_1_to_100() {
        let mut m = Moments::new();
        for i in 1..=100u64 {
            m.update(i as f64);
        }

        assert_eq!(m.count(), 100);

        let mean = m.mean().unwrap();
        assert!((mean - 50.5).abs() < 1e-10, "mean = {mean}");

        let pop_var = m.population_variance().unwrap();
        assert!((pop_var - 833.25).abs() < 1e-6, "pop variance = {pop_var}");

        let var = m.variance().unwrap();
        assert!((var - 841.6667).abs() < 0.01, "variance = {var}");
    }

    #[test]
    fn uniform_skewness_near_zero() {
        let mut m = Moments::new();
        for i in 1..=10000u64 {
            m.update(i as f64);
        }
        let skew = m.shape().unwrap().skewness;
        assert!(skew.abs() < 0.01, "skewness = {skew}, expected ≈ 0");
    }

    #[test]
    fn uniform_kurtosis() {
        let mut m = Moments::new();
        for i in 1..=10000u64 {
            m.update(i as f64);
        }
        let kurt = m.shape().unwrap().excess_kurtosis;
        assert!(
            (kurt - (-1.2)).abs() < 0.01,
            "kurtosis = {kurt}, expected ≈ -1.2"
        );
    }

    #[test]
    fn empty() {
        let m = Moments::new();
        assert_eq!(m.count(), 0);
        assert!(m.mean().is_none());
        assert!(m.variance().is_none());
        assert!(m.shape().is_none());
        assert!(!m.is_primed());
    }

    #[test]
    fn single_sample() {
        let mut m = Moments::new();
        m.update(42.0);
        assert_eq!(m.count(), 1);
        assert_eq!(m.mean(), Some(42.0));
        assert!(m.variance().is_none());
        assert!(m.shape().is_none());
    }

    #[test]
    fn priming_thresholds() {
        let mut m = Moments::new();
        m.update(1.0);
        assert!(m.mean().is_some());
        m.update(2.0);
        assert!(m.variance().is_some());
        m.update(3.0);
        assert!(m.shape().is_none());
        m.update(4.0);
        assert!(m.shape().is_some());
        assert!(m.is_primed());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn constant_input() {
        let mut m = Moments::new();
        for _ in 0..100 {
            m.update(42.0);
        }
        assert_eq!(m.mean(), Some(42.0));
        assert_eq!(m.variance(), Some(0.0));
        assert!(m.shape().is_none());
    }

    #[test]
    fn right_skewed_distribution() {
        let mut m = Moments::new();
        for _ in 0..900 {
            m.update(1.0);
        }
        for _ in 0..100 {
            m.update(10.0);
        }
        let skew = m.shape().unwrap().skewness;
        assert!(skew > 0.0, "right-skewed should be positive, got {skew}");
    }

    #[test]
    fn reset_clears_state() {
        let mut m = Moments::new();
        for i in 0..100 {
            m.update(i as f64);
        }
        m.reset();
        assert_eq!(m.count(), 0);
        assert!(m.mean().is_none());
        assert!(m.shape().is_none());
    }

    #[test]
    fn merge_empty_into_empty() {
        let mut a = Moments::new();
        let b = Moments::new();
        a.merge(&b);
        assert_eq!(a.count(), 0);
    }

    #[test]
    fn merge_into_empty() {
        let mut a = Moments::new();
        let mut b = Moments::new();
        for i in 1..=50u64 {
            b.update(i as f64);
        }
        a.merge(&b);
        assert_eq!(a.count(), 50);
        assert!((a.mean().unwrap() - 25.5).abs() < 1e-10);
    }

    #[test]
    fn merge_matches_single_pass() {
        let data: Vec<f64> = (1..=200).map(|i| i as f64).collect();

        let mut single = Moments::new();
        for &x in &data {
            single.update(x);
        }

        let mut first = Moments::new();
        let mut second = Moments::new();
        for &x in &data[..80] {
            first.update(x);
        }
        for &x in &data[80..] {
            second.update(x);
        }
        first.merge(&second);

        assert_eq!(first.count(), single.count());
        assert!((first.mean().unwrap() - single.mean().unwrap()).abs() < 1e-10);
        assert!((first.variance().unwrap() - single.variance().unwrap()).abs() < 1e-6);
        assert!((first.shape().unwrap().skewness - single.shape().unwrap().skewness).abs() < 1e-6);
        assert!(
            (first.shape().unwrap().kurtosis() - single.shape().unwrap().kurtosis()).abs() < 1e-4
        );
    }

    #[test]
    fn default_is_empty() {
        let m = Moments::default();
        assert_eq!(m.count(), 0);
    }

    #[test]
    fn checked_update_refuses_bad_input_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let readings = |m: &Moments| (m.count(), m.mean(), m.variance(), m.shape());
        let mut m = Moments::new();
        for x in [1.0, 2.0, 3.0, 10.0] {
            m.checked_update(x).unwrap();
        }
        let before = readings(&m);

        assert_eq!(m.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(m.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(m.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(m.checked_update(1e61), Err(OutOfRange));
        assert_eq!(m.checked_update(-1e61), Err(OutOfRange));

        assert_eq!(readings(&m), before);
        assert_eq!(m.count(), 4);
    }

    #[test]
    fn checked_update_accepts_the_limit_without_overflow() {
        let mut m = Moments::new();
        for i in 0..100_000 {
            let sign = if i % 2 == 0 { 1.0 } else { -1.0 };
            m.checked_update(sign * Moments::INPUT_LIMIT).unwrap();
        }
        assert!(m.mean().unwrap().is_finite());
        assert!(m.variance().unwrap().is_finite());
        assert!(m.shape().unwrap().skewness.is_finite());
        // Two values, equally often: the flattest distribution there is.
        assert!((m.shape().unwrap().excess_kurtosis + 2.0).abs() < 1e-6);
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = Moments::new();
        let mut unchecked = Moments::new();
        for x in [2.0, -7.5, 1e9, 0.0, 3.25, 11.0] {
            checked.checked_update(x).unwrap();
            unchecked.update(x);
        }
        assert_eq!(checked.count(), unchecked.count());
        assert_eq!(checked.mean(), unchecked.mean());
        assert_eq!(checked.variance(), unchecked.variance());
        assert_eq!(checked.shape(), unchecked.shape());
    }

    #[test]
    fn update_does_not_validate() {
        let mut m = Moments::new();
        m.update(1e200);
        m.update(-1e200);
        assert_eq!(m.variance(), Some(f64::INFINITY));
    }

    #[test]
    fn matches_the_moments_computed_in_two_passes() {
        let xs = [3.0, -1.5, 8.0, 0.25, 4.0, 4.0, -6.0, 12.5, 1.0];
        let n = xs.len() as f64;
        let mean = xs.iter().sum::<f64>() / n;
        let central = |power: i32| xs.iter().map(|x| (x - mean).powi(power)).sum::<f64>() / n;
        let (m2, m3, m4) = (central(2), central(3), central(4));

        let mut m = Moments::new();
        for x in xs {
            m.update(x);
        }
        assert!((m.mean().unwrap() - mean).abs() < 1e-12);
        assert!((m.population_variance().unwrap() - m2).abs() < 1e-12);
        assert!((m.shape().unwrap().skewness - m3 / m2.powf(1.5)).abs() < 1e-12);
        assert!((m.shape().unwrap().excess_kurtosis - (m4 / (m2 * m2) - 3.0)).abs() < 1e-12);
    }

    #[test]
    fn the_shape_does_not_depend_on_scale_until_it_cannot_be_resolved() {
        let fed = |scale: f64| {
            let mut m = Moments::new();
            for x in [-2.0, -1.0, 0.0, 0.0, 1.0, 5.0] {
                m.update(x * scale);
            }
            m.shape()
        };
        let reference = fed(1.0).unwrap();
        for scale in [1e60, 1e-30, 1e-60] {
            let shape = fed(scale).unwrap();
            assert!((shape.skewness - reference.skewness).abs() < 1e-9);
            assert!((shape.excess_kurtosis - reference.excess_kurtosis).abs() < 1e-9);
        }
        // Here the divisors underflow: main returned NaN.
        for scale in [1e-100, 1e-110, 1e-150] {
            assert_eq!(fed(scale), None, "scale {scale}");
        }
    }

    #[test]
    fn a_spread_lost_to_rounding_against_the_mean_has_no_shape() {
        // One rounding step of spread on a mean of 1: SciPy's "all values
        // are equal". Only that test catches it; the variance is not tiny.
        let step = f64::EPSILON;
        let mut m = Moments::new();
        for x in [1.0, 1.0 + step, 1.0, 1.0, 1.0 + step, 1.0] {
            m.update(x);
        }
        assert!(m.variance().unwrap() > 1e-40);
        assert_eq!(m.shape(), None);

        // The same spread on a mean near zero is resolved.
        let mut m = Moments::new();
        for x in [0.0, step, 0.0, 0.0, step, 0.0] {
            m.update(x);
        }
        assert!(m.shape().is_some());
    }

    #[test]
    fn the_fourth_moment_keeps_growing_on_a_long_stream_of_tiny_values() {
        // The state after 1e17 samples of +-s, with `m4` zeroed so that its
        // growth can be read directly.
        let s = 1e-73_f64;
        let count = 100_000_000_000_000_000_u64;
        let mut m = Moments {
            count,
            mean: 0.0,
            m2: count as f64 * s * s,
            m3: 0.0,
            m4: 0.0,
        };
        for i in 0..1000 {
            m.update(if i % 2 == 0 { s } else { -s });
        }
        // Each sample adds s^4.
        let expected = 1000.0 * s.powi(4);
        assert!((m.m4 - expected).abs() < 1e-6 * expected, "m4 = {}", m.m4);
    }

    #[test]
    fn kurtosis_is_excess_plus_three() {
        let shape = Shape {
            skewness: 0.0,
            excess_kurtosis: -1.2,
        };
        assert_eq!(shape.kurtosis(), 1.8);
    }
}
