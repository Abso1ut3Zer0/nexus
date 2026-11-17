use crate::math::MulAdd;

// P² Algorithm — Streaming Percentile Estimation
//
// Jain & Chlamtac, "The P-Square Algorithm for Dynamic Calculation of
// Quantiles and Histograms Without Storing Observations"
// (Communications of the ACM, 1985).
//
// Tracks 5 markers that converge to the target quantile. O(1) per update,
// 176 bytes state, zero allocation, no_std.

// We intentionally avoid mul_add/FMA — it requires std or libm.
// P² only needs +, -, *, / and must compile on no_std without libm.

/// P² streaming percentile estimator.
///
/// Tracks a single percentile using 5 markers that converge via
/// parabolic interpolation. O(1) per update, fixed memory.
///
/// # Use Cases
/// - p99 latency monitoring on the hot path
/// - Streaming median estimation
/// - Tail latency tracking without histograms
#[derive(Debug, Clone)]
pub struct Percentile {
    /// Marker heights (value estimates).
    q: [f64; 5],
    /// Marker positions (observation count, f64 for interpolation math).
    n: [f64; 5],
    /// Desired marker positions.
    dn: [f64; 5],
    /// Desired position increments (fixed after construction).
    dn_inc: [f64; 5],
    /// Target percentile in (0, 1).
    p: f64,
    /// Precomputed minimum samples for `is_primed()`.
    min_samples: u64,
    /// Total observations processed.
    count: u64,
}
/// Builder for [`
#[doc = stringify!(Percentile)]
/// `].
#[derive(Debug, Clone)]
pub struct PercentileBuilder {
    p: Option<f64>,
}
impl Percentile {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> PercentileBuilder {
        PercentileBuilder { p: None }
    }
    /// Convenience constructor for a single percentile.
    ///
    /// `p` is the target quantile in (0.0, 1.0).
    /// For p99: `new(0.99)`. For p50: `new(0.50)`.
    #[inline]
    pub fn new(p: f64) -> Result<Self, crate::ConfigError> {
        Self::builder().percentile(p).build()
    }
    /// Feeds an observation.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<(), crate::DataError> {
        check_finite!(sample);
        self.count += 1;
        // Initialization: collect first 5 observations
        if self.count <= 5 {
            self.q[self.count as usize - 1] = sample;
            if self.count == 5 {
                // Sort to initialize markers
                // total_cmp for NaN safety (NaN sorts last)
                self.q.sort_unstable_by(f64::total_cmp);
                for i in 0..5 {
                    self.n[i] = (i + 1) as f64;
                }
                let p = self.p;
                self.dn = [
                    1.0,
                    2.0f64.fma(p, 1.0),
                    4.0f64.fma(p, 1.0),
                    2.0f64.fma(p, 3.0),
                    5.0,
                ];
            }
            return Ok(());
        }
        // Find cell k where q[k-1] <= sample < q[k]
        let k;
        if sample < self.q[0] {
            self.q[0] = sample;
            k = 0;
        } else if sample < self.q[1] {
            k = 0;
        } else if sample < self.q[2] {
            k = 1;
        } else if sample < self.q[3] {
            k = 2;
        } else if sample <= self.q[4] {
            k = 3;
        } else {
            self.q[4] = sample;
            k = 3;
        }
        // Increment positions for markers above insertion point
        for i in (k + 1)..5 {
            self.n[i] += 1.0;
        }
        // Update desired positions
        for i in 0..5 {
            self.dn[i] += self.dn_inc[i];
        }
        // Adjust markers 1, 2, 3
        for i in 1..4 {
            let d = self.dn[i] - self.n[i];
            if (d >= 1.0 && self.n[i + 1] - self.n[i] > 1.0)
                || (d <= -(1.0) && self.n[i - 1] - self.n[i] < -(1.0))
            {
                let sign = if d > 0.0 { 1.0 } else { -(1.0) };
                // Try parabolic (P²) adjustment
                let q_new = self.parabolic(i, sign);
                if self.q[i - 1] < q_new && q_new < self.q[i + 1] {
                    self.q[i] = q_new;
                } else {
                    // Linear fallback
                    self.q[i] = self.linear(i, sign);
                }
                self.n[i] += sign;
            }
        }
        Ok(())
    }
    /// Parabolic (P²) interpolation.
    #[inline]
    fn parabolic(&self, i: usize, d: f64) -> f64 {
        let ni = self.n[i];
        let nim1 = self.n[i - 1];
        let nip1 = self.n[i + 1];
        let qi = self.q[i];
        let qim1 = self.q[i - 1];
        let qip1 = self.q[i + 1];
        let term1 = (ni - nim1 + d) * (qip1 - qi) / (nip1 - ni);
        let term2 = (nip1 - ni - d) * (qi - qim1) / (ni - nim1);
        (d / (nip1 - nim1)).fma(term1 + term2, qi)
    }
    /// Linear interpolation fallback.
    #[inline]
    fn linear(&self, i: usize, d: f64) -> f64 {
        let j = if d > 0.0 { i + 1 } else { i - 1 };
        self.q[i] + d * (self.q[j] - self.q[i]) / (self.n[j] - self.n[i])
    }
    /// Current percentile estimate, or `None` if < 5 observations.
    #[inline]
    #[must_use]
    pub fn percentile(&self) -> Option<f64> {
        if self.is_primed() {
            Some(self.q[2])
        } else {
            None
        }
    }
    /// Target percentile (the `p` value).
    #[inline]
    #[must_use]
    pub fn target(&self) -> f64 {
        self.p
    }
    /// Number of observations processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }
    /// Whether enough data has been collected for reliable estimates.
    ///
    /// More observations are needed for extreme percentiles.
    /// `1 / (p (1 - p))`, floored at 5: p=0.50 requires 5, p=0.99 requires
    /// 101, p=0.999 requires 1001.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }
    /// Observations needed before the estimate is reported: 5, or
    /// `1 / (p (1 - p))` for extreme percentiles (101 for p = 0.99).
    #[inline]
    #[must_use]
    pub fn min_samples(&self) -> u64 {
        self.min_samples
    }
    /// Current minimum observed value, or `None` if empty.
    ///
    /// Before priming (< 5 observations), scans the buffered samples.
    /// After priming, marker 0 tracks the minimum.
    #[inline]
    #[must_use]
    pub fn min(&self) -> Option<f64> {
        if self.count == 0 {
            return None;
        }
        if self.count >= 5 {
            return Some(self.q[0]);
        }
        // Warmup: q[..count] is unsorted, scan for min
        let len = self.count as usize;
        let mut min = self.q[0];
        for i in 1..len {
            if self.q[i] < min {
                min = self.q[i];
            }
        }
        Some(min)
    }
    /// Current maximum observed value, or `None` if empty.
    ///
    /// Before priming (< 5 observations), scans the buffered samples.
    /// After priming, marker 4 tracks the maximum.
    #[inline]
    #[must_use]
    pub fn max(&self) -> Option<f64> {
        if self.count == 0 {
            return None;
        }
        if self.count >= 5 {
            return Some(self.q[4]);
        }
        // Warmup: q[..count] is unsorted, scan for max
        let len = self.count as usize;
        let mut max = self.q[0];
        for i in 1..len {
            if self.q[i] > max {
                max = self.q[i];
            }
        }
        Some(max)
    }
    /// Resets to empty state. Target percentile unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.q = [0.0; 5];
        self.n = [0.0; 5];
        self.dn = [0.0; 5];
        // dn_inc is fixed, keep it
        self.count = 0;
    }
}
impl PercentileBuilder {
    /// Target percentile in (0.0, 1.0). Required.
    #[inline]
    #[must_use]
    pub fn percentile(mut self, p: f64) -> Self {
        self.p = Some(p);
        self
    }
    /// Builds the percentile tracker.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Missing` if percentile not set.
    /// Returns `ConfigError::Invalid` if percentile not in (0, 1).
    #[inline]
    pub fn build(self) -> Result<Percentile, crate::ConfigError> {
        let p = self.p.ok_or(crate::ConfigError::Missing("percentile"))?;
        if !(p > 0.0 && p < 1.0) {
            return Err(crate::ConfigError::Invalid(
                "percentile must be in (0, 1) exclusive",
            ));
        }
        // Precompute min_samples: more observations for extreme percentiles.
        // p=0.50 → 5, p=0.99 → 100, p=0.999 → 1000.
        let min_samples = ((1.0 / (p * (1.0 - p))) as u64).max(5);
        Ok(Percentile {
            q: [0.0; 5],
            n: [0.0; 5],
            dn: [0.0; 5],
            dn_inc: [0.0, p / 2.0, p, f64::midpoint(1.0, p), 1.0],
            p,
            min_samples,
            count: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn p50_converges_to_median() {
        let mut p = Percentile::new(0.50).unwrap();
        for i in 1..=1000u64 {
            p.update(i as f64).unwrap();
        }
        let est = p.percentile().unwrap();
        assert!((est - 500.0).abs() < 50.0, "p50 = {est}, expected ~500");
    }

    #[test]
    fn p99_converges() {
        let mut p = Percentile::new(0.99).unwrap();
        for i in 1..=10000u64 {
            p.update(i as f64).unwrap();
        }
        let est = p.percentile().unwrap();
        assert!((est - 9900.0).abs() < 200.0, "p99 = {est}, expected ~9900");
    }

    #[test]
    fn not_primed_until_5_observations() {
        let mut p = Percentile::new(0.50).unwrap();
        for i in 0..4 {
            p.update(i as f64).unwrap();
            assert!(p.percentile().is_none());
        }
        p.update(4.0).unwrap();
        assert!(p.percentile().is_some());
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn tracks_min_max() {
        let mut p = Percentile::new(0.50).unwrap();
        for v in [5.0, 1.0, 9.0, 3.0, 7.0] {
            p.update(v).unwrap();
        }
        assert_eq!(p.min(), Some(1.0));
        assert_eq!(p.max(), Some(9.0));
    }

    #[test]
    fn reset_clears_state() {
        let mut p = Percentile::new(0.50).unwrap();
        for i in 0..100 {
            p.update(i as f64).unwrap();
        }
        p.reset();
        assert_eq!(p.count(), 0);
        assert!(p.percentile().is_none());
        assert!((p.target() - 0.50).abs() < f64::EPSILON);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn constant_input() {
        let mut p = Percentile::new(0.50).unwrap();
        for _ in 0..100 {
            p.update(42.0).unwrap();
        }
        assert_eq!(p.percentile(), Some(42.0));
    }

    #[test]
    fn rejects_invalid_percentile() {
        assert!(Percentile::new(0.0).is_err());
        assert!(Percentile::new(1.0).is_err());
        assert!(Percentile::new(-0.5).is_err());
        assert!(Percentile::new(1.5).is_err());
    }

    #[test]
    fn p90_reasonable() {
        let mut p = Percentile::new(0.90).unwrap();
        for i in 1..=1000u64 {
            p.update(i as f64).unwrap();
        }
        let est = p.percentile().unwrap();
        assert!((est - 900.0).abs() < 50.0, "p90 = {est}, expected ~900");
    }

    #[test]
    fn skewed_distribution() {
        let mut p = Percentile::new(0.99).unwrap();
        for i in 0..10000u64 {
            if i % 100 == 99 {
                p.update(1000.0).unwrap();
            } else {
                p.update(10.0).unwrap();
            }
        }
        let est = p.percentile().unwrap();
        assert!(est < 500.0, "p99 = {est}, expected well below 1000");
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut p = Percentile::new(0.50).unwrap();
        assert_eq!(p.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(p.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(p.update(f64::NEG_INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(p.count(), 0);
    }
}
