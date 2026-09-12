use crate::math::MulAdd;

/// Welford — Online mean, variance, and standard deviation.
///
/// Numerically stable single-pass computation using Welford's algorithm.
/// No catastrophic cancellation. Supports merging partial results via
/// Chan's algorithm for parallel aggregation.
///
/// # Use Cases
/// - Running statistics on latency, throughput, PnL
/// - Z-score computation (combine with EMA for baseline)
/// - Input to adaptive thresholds
#[derive(Debug, Clone)]
pub struct WelfordF64 {
    count: u64,
    mean: f64,
    m2: f64,
}

impl WelfordF64 {
    /// Creates a new empty accumulator.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            count: 0,
            mean: 0.0,
            m2: 0.0,
        }
    }

    /// Creates an accumulator pre-loaded from known statistics.
    ///
    /// `m2` is the sum of squared deviations from the mean
    /// (`variance * (count - 1)` for sample variance).
    #[inline]
    #[must_use]
    pub const fn from_parts(count: u64, mean: f64, m2: f64) -> Self {
        Self { count, mean, m2 }
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
        let delta = sample - self.mean;
        self.mean += delta / self.count as f64;
        let delta2 = sample - self.mean;
        self.m2 += delta * delta2;
        Ok(())
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether enough data for variance/std_dev queries (>= 2 samples).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= 2
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
    #[inline]
    #[must_use]
    #[cfg(any(feature = "std", feature = "libm"))]
    pub fn std_dev(&self) -> Option<f64> {
        self.variance().map(crate::math::sqrt)
    }

    /// Merges another accumulator into this one (Chan's algorithm).
    ///
    /// After merging, `self` contains the statistics of the combined
    /// dataset. The other accumulator is unchanged.
    #[inline]
    pub fn merge(&mut self, other: &Self) {
        if other.count == 0 {
            return;
        }
        if self.count == 0 {
            self.count = other.count;
            self.mean = other.mean;
            self.m2 = other.m2;
            return;
        }

        let combined_count = self.count + other.count;
        let delta = other.mean - self.mean;
        let weight = other.count as f64 / combined_count as f64;
        let new_mean = delta.fma(weight, self.mean);
        let cross = self.count as f64 * other.count as f64 / combined_count as f64;
        let new_m2 = delta.fma(delta * cross, self.m2 + other.m2);

        self.count = combined_count;
        self.mean = new_mean;
        self.m2 = new_m2;
    }

    /// Resets to empty state.
    #[inline]
    pub fn reset(&mut self) {
        self.count = 0;
        self.mean = 0.0;
        self.m2 = 0.0;
    }
}

impl Default for WelfordF64 {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_returns_none() {
        let w = WelfordF64::new();
        assert_eq!(w.count(), 0);
        assert!(w.mean().is_none());
        assert!(w.variance().is_none());
        assert!(w.population_variance().is_none());
        assert!(w.std_dev().is_none());
    }

    #[test]
    fn single_sample() {
        let mut w = WelfordF64::new();
        w.update(42.0).unwrap();

        assert_eq!(w.count(), 1);
        assert_eq!(w.mean(), Some(42.0));
        assert!(w.variance().is_none());
        assert_eq!(w.population_variance(), Some(0.0));
    }

    #[test]
    fn known_values() {
        let mut w = WelfordF64::new();

        for &x in &[2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0] {
            w.update(x).unwrap();
        }

        assert_eq!(w.count(), 8);

        let mean = w.mean().unwrap();
        assert!((mean - 5.0).abs() < 1e-10, "mean should be 5.0, got {mean}");

        let pop_var = w.population_variance().unwrap();
        assert!(
            (pop_var - 4.0).abs() < 1e-10,
            "pop variance should be 4.0, got {pop_var}"
        );

        let var = w.variance().unwrap();
        assert!(
            (var - 32.0 / 7.0).abs() < 1e-10,
            "sample variance should be 32/7, got {var}"
        );

        let sd = w.std_dev().unwrap();
        assert!(
            (sd - (32.0_f64 / 7.0).sqrt()).abs() < 1e-6,
            "std dev got {sd}"
        );
    }

    #[test]
    fn two_samples() {
        let mut w = WelfordF64::new();
        w.update(10.0).unwrap();
        w.update(20.0).unwrap();

        assert_eq!(w.count(), 2);
        assert!((w.mean().unwrap() - 15.0).abs() < 1e-10);
        assert!((w.variance().unwrap() - 50.0).abs() < 1e-10);
        assert!((w.population_variance().unwrap() - 25.0).abs() < 1e-10);
    }

    #[test]
    fn numerical_stability_large_offset() {
        let mut w = WelfordF64::new();
        let base = 1e8;

        for i in 0..1000 {
            w.update((i as f64).fma(0.001, base)).unwrap();
        }

        let var = w.variance().unwrap();
        assert!(var > 0.0, "variance should be positive, got {var}");
        assert!(var < 1.0, "variance should be small, got {var}");
    }

    #[test]
    fn merge_empty_into_empty() {
        let mut a = WelfordF64::new();
        let b = WelfordF64::new();
        a.merge(&b);
        assert_eq!(a.count(), 0);
        assert!(a.mean().is_none());
    }

    #[test]
    fn merge_into_empty() {
        let mut a = WelfordF64::new();
        let mut b = WelfordF64::new();
        b.update(10.0).unwrap();
        b.update(20.0).unwrap();

        a.merge(&b);
        assert_eq!(a.count(), 2);
        assert!((a.mean().unwrap() - 15.0).abs() < 1e-10);
    }

    #[test]
    fn merge_empty_into_existing() {
        let mut a = WelfordF64::new();
        a.update(10.0).unwrap();
        a.update(20.0).unwrap();
        let b = WelfordF64::new();

        a.merge(&b);
        assert_eq!(a.count(), 2);
        assert!((a.mean().unwrap() - 15.0).abs() < 1e-10);
    }

    #[test]
    fn merge_matches_single_accumulator() {
        let data = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0];

        let mut single = WelfordF64::new();
        for &x in &data {
            single.update(x).unwrap();
        }

        let mut first = WelfordF64::new();
        let mut second = WelfordF64::new();
        for &x in &data[..4] {
            first.update(x).unwrap();
        }
        for &x in &data[4..] {
            second.update(x).unwrap();
        }
        first.merge(&second);

        assert_eq!(first.count(), single.count());
        assert!((first.mean().unwrap() - single.mean().unwrap()).abs() < 1e-10);
        assert!((first.variance().unwrap() - single.variance().unwrap()).abs() < 1e-10);
    }

    #[test]
    fn merge_uneven_split() {
        let mut single = WelfordF64::new();
        let mut a = WelfordF64::new();
        let mut b = WelfordF64::new();

        for i in 0..100 {
            let x = i as f64;
            single.update(x).unwrap();
            if i < 7 {
                a.update(x).unwrap();
            } else {
                b.update(x).unwrap();
            }
        }
        a.merge(&b);

        assert_eq!(a.count(), 100);
        assert!((a.mean().unwrap() - single.mean().unwrap()).abs() < 1e-10);
        assert!((a.variance().unwrap() - single.variance().unwrap()).abs() < 1e-6);
    }

    #[test]
    fn reset_clears_state() {
        let mut w = WelfordF64::new();
        for i in 0..100 {
            w.update(i as f64).unwrap();
        }

        w.reset();
        assert_eq!(w.count(), 0);
        assert!(w.mean().is_none());
        assert!(w.variance().is_none());
    }

    #[test]
    fn default_is_empty() {
        let w = WelfordF64::default();
        assert_eq!(w.count(), 0);
    }

    #[test]
    fn from_parts_round_trip() {
        let mut w = WelfordF64::new();
        for &x in &[2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0] {
            w.update(x).unwrap();
        }

        let count = w.count();
        let mean = w.mean().unwrap();
        let m2 = w.variance().unwrap() * (count - 1) as f64;

        let w2 = WelfordF64::from_parts(count, mean, m2);
        assert_eq!(w2.count(), count);
        assert!((w2.mean().unwrap() - mean).abs() < 1e-10);
        assert!((w2.variance().unwrap() - w.variance().unwrap()).abs() < 1e-10);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut w = WelfordF64::new();
        assert_eq!(w.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(w.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(w.update(f64::NEG_INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(w.count(), 0);
    }
}

// =============================================================================
// Proptests
// =============================================================================

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// Variance must never go negative, and must match an independent
        /// two-pass reference computation within a tight tolerance -- the
        /// numerical-stability invariant Welford's algorithm exists for
        /// (avoiding the catastrophic cancellation of the naive
        /// sum-of-squares-minus-square-of-sum approach).
        #[test]
        fn fuzz_variance_matches_two_pass_reference(
            samples in proptest::collection::vec(-1e6f64..1e6, 2..200),
        ) {
            let mut w = WelfordF64::new();
            for &s in &samples {
                w.update(s).unwrap();
            }

            prop_assert_eq!(w.count(), samples.len() as u64);

            let var = w.variance().unwrap();
            prop_assert!(var >= 0.0, "variance went negative: {var}");

            // Independent two-pass reference: mean, then sum of squared
            // deviations from that mean, then divide by (n-1).
            let n = samples.len() as f64;
            let ref_mean = samples.iter().sum::<f64>() / n;
            let ref_var =
                samples.iter().map(|s| (s - ref_mean).powi(2)).sum::<f64>() / (n - 1.0);

            let mean = w.mean().unwrap();
            let mean_scale = ref_mean.abs().max(1.0);
            prop_assert!(
                (mean - ref_mean).abs() <= 1e-6 * mean_scale,
                "mean diverged from reference: welford={mean}, reference={ref_mean}"
            );

            let var_scale = ref_var.abs().max(1.0);
            prop_assert!(
                (var - ref_var).abs() <= 1e-6 * var_scale,
                "variance diverged from reference: welford={var}, reference={ref_var}"
            );
        }

        /// Splitting a sequence across two accumulators and merging them
        /// (Chan's algorithm) must match feeding the whole sequence into a
        /// single accumulator.
        #[test]
        fn fuzz_merge_matches_single_pass(
            samples in proptest::collection::vec(-1e6f64..1e6, 2..200),
            split in 1usize..199,
        ) {
            let split = split.min(samples.len() - 1).max(1);

            let mut whole = WelfordF64::new();
            for &s in &samples {
                whole.update(s).unwrap();
            }

            let mut left = WelfordF64::new();
            for &s in &samples[..split] {
                left.update(s).unwrap();
            }
            let mut right = WelfordF64::new();
            for &s in &samples[split..] {
                right.update(s).unwrap();
            }
            left.merge(&right);

            prop_assert_eq!(left.count(), whole.count());

            let mean_scale = whole.mean().unwrap().abs().max(1.0);
            prop_assert!(
                (left.mean().unwrap() - whole.mean().unwrap()).abs() <= 1e-6 * mean_scale
            );

            let whole_var = whole.variance().unwrap();
            let merged_var = left.variance().unwrap();
            let var_scale = whole_var.abs().max(1.0);
            prop_assert!((merged_var - whole_var).abs() <= 1e-6 * var_scale);
        }
    }
}
