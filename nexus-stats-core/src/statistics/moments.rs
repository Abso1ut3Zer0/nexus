// We intentionally avoid mul_add/FMA in the moment formulas — the update
// order (M4 before M3 before M2) is critical and FMA rewriting could
// change numerical behavior. Additionally, moments must compile on
// no_std without libm.
#![allow(clippy::suboptimal_flops, clippy::float_cmp)]

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
/// for i in 1..=1000u64 { m.update(i as f64).unwrap(); }
/// // Uniform distribution: skewness ≈ 0, kurtosis ≈ -1.2
/// let skew = m.skewness().unwrap();
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

    /// Feeds a sample.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<(), crate::DataError> {
        check_finite!(sample);
        self.count += 1;
        let n = self.count as f64;
        let delta = sample - self.mean;
        let delta_n = delta / n;
        let delta_n2 = delta_n * delta_n;
        let term1 = delta * delta_n * (n - 1.0);

        // M4 before M3 before M2 — each uses previous iteration's lower moments
        self.m4 += term1 * delta_n2 * (n * n - 3.0 * n + 3.0) + 6.0 * delta_n2 * self.m2
            - 4.0 * delta_n * self.m3;
        self.m3 += term1 * delta_n * (n - 2.0) - 3.0 * delta_n * self.m2;
        self.m2 += term1;
        self.mean += delta_n;
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
            None
        } else {
            Some(self.mean)
        }
    }

    /// Sample variance (N-1 denominator), or `None` if < 2 samples.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> Option<f64> {
        if self.count < 2 {
            None
        } else {
            Some(self.m2 / (self.count - 1) as f64)
        }
    }

    /// Population variance (N denominator), or `None` if empty.
    #[inline]
    #[must_use]
    pub fn population_variance(&self) -> Option<f64> {
        if self.count == 0 {
            None
        } else {
            Some(self.m2 / self.count as f64)
        }
    }

    /// Sample standard deviation, or `None` if < 2 samples.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn std_dev(&self) -> Option<f64> {
        self.variance().map(crate::math::sqrt)
    }

    /// Population skewness (Fisher's definition), or `None` if < 3
    /// samples or variance is zero.
    ///
    /// Positive = right-skewed (tail extends right).
    /// Negative = left-skewed (tail extends left).
    /// Zero = symmetric.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn skewness(&self) -> Option<f64> {
        if self.count < 3 {
            return None;
        }
        if self.m2 == 0.0 {
            return None;
        }
        let n = self.count as f64;
        Some(crate::math::sqrt(n) * self.m3 / (self.m2 * crate::math::sqrt(self.m2)))
    }

    /// Population excess kurtosis, or `None` if < 4 samples or
    /// variance is zero.
    ///
    /// Normal distribution = 0. Positive = heavy tails (leptokurtic).
    /// Negative = light tails (platykurtic). This is the most common
    /// convention (numpy, scipy, most finance).
    #[inline]
    #[must_use]
    pub fn excess_kurtosis(&self) -> Option<f64> {
        if self.count < 4 {
            return None;
        }
        if self.m2 == 0.0 {
            return None;
        }
        let n = self.count as f64;
        Some(n * self.m4 / (self.m2 * self.m2) - 3.0)
    }

    /// Population kurtosis (non-excess), or `None` if < 4 samples or
    /// variance is zero.
    ///
    /// Normal distribution = 3. This is `excess_kurtosis() + 3`.
    #[inline]
    #[must_use]
    pub fn kurtosis(&self) -> Option<f64> {
        self.excess_kurtosis().map(|k| k + 3.0)
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
            + delta4 * n_a * n_b * (n_a * n_a - n_a * n_b + n_b * n_b) / (n * n * n)
            + 6.0 * delta2 * (n_a * n_a * other.m2 + n_b * n_b * self.m2) / (n * n)
            + 4.0 * delta * (n_a * other.m3 - n_b * self.m3) / n;

        let new_m3 = self.m3
            + other.m3
            + delta3 * n_a * n_b * (n_a - n_b) / (n * n)
            + 3.0 * delta * (n_a * other.m2 - n_b * self.m2) / n;

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
mod tests {
    use super::*;

    #[test]
    fn uniform_1_to_100() {
        let mut m = Moments::new();
        for i in 1..=100u64 {
            m.update(i as f64).unwrap();
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
            m.update(i as f64).unwrap();
        }
        let skew = m.skewness().unwrap();
        assert!(skew.abs() < 0.01, "skewness = {skew}, expected ≈ 0");
    }

    #[test]
    fn uniform_kurtosis() {
        let mut m = Moments::new();
        for i in 1..=10000u64 {
            m.update(i as f64).unwrap();
        }
        let kurt = m.excess_kurtosis().unwrap();
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
        assert!(m.skewness().is_none());
        assert!(m.excess_kurtosis().is_none());
        assert!(!m.is_primed());
    }

    #[test]
    fn single_sample() {
        let mut m = Moments::new();
        m.update(42.0).unwrap();
        assert_eq!(m.count(), 1);
        assert_eq!(m.mean(), Some(42.0));
        assert!(m.variance().is_none());
        assert!(m.skewness().is_none());
        assert!(m.excess_kurtosis().is_none());
    }

    #[test]
    fn priming_thresholds() {
        let mut m = Moments::new();
        m.update(1.0).unwrap();
        assert!(m.mean().is_some());
        m.update(2.0).unwrap();
        assert!(m.variance().is_some());
        m.update(3.0).unwrap();
        assert!(m.skewness().is_some());
        m.update(4.0).unwrap();
        assert!(m.excess_kurtosis().is_some());
        assert!(m.is_primed());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn constant_input() {
        let mut m = Moments::new();
        for _ in 0..100 {
            m.update(42.0).unwrap();
        }
        assert_eq!(m.mean(), Some(42.0));
        assert_eq!(m.variance(), Some(0.0));
        assert!(m.skewness().is_none());
        assert!(m.excess_kurtosis().is_none());
    }

    #[test]
    fn right_skewed_distribution() {
        let mut m = Moments::new();
        for _ in 0..900 {
            m.update(1.0).unwrap();
        }
        for _ in 0..100 {
            m.update(10.0).unwrap();
        }
        let skew = m.skewness().unwrap();
        assert!(skew > 0.0, "right-skewed should be positive, got {skew}");
    }

    #[test]
    fn reset_clears_state() {
        let mut m = Moments::new();
        for i in 0..100 {
            m.update(i as f64).unwrap();
        }
        m.reset();
        assert_eq!(m.count(), 0);
        assert!(m.mean().is_none());
        assert!(m.excess_kurtosis().is_none());
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
            b.update(i as f64).unwrap();
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
            single.update(x).unwrap();
        }

        let mut first = Moments::new();
        let mut second = Moments::new();
        for &x in &data[..80] {
            first.update(x).unwrap();
        }
        for &x in &data[80..] {
            second.update(x).unwrap();
        }
        first.merge(&second);

        assert_eq!(first.count(), single.count());
        assert!((first.mean().unwrap() - single.mean().unwrap()).abs() < 1e-10);
        assert!((first.variance().unwrap() - single.variance().unwrap()).abs() < 1e-6);
        assert!((first.skewness().unwrap() - single.skewness().unwrap()).abs() < 1e-6);
        assert!((first.kurtosis().unwrap() - single.kurtosis().unwrap()).abs() < 1e-4);
    }

    #[test]
    fn default_is_empty() {
        let m = Moments::default();
        assert_eq!(m.count(), 0);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut m = Moments::new();
        assert_eq!(m.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(m.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(m.update(f64::NEG_INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(m.count(), 0);
    }
}
