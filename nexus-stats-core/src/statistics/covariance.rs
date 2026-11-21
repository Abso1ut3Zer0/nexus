use crate::math::MulAdd;
use crate::statistics::running_mean::step_mean;

/// Online covariance and Pearson correlation between two signals.
///
/// Uses Welford-style numerically stable single-pass computation.
/// Supports Chan's merge for parallel aggregation.
///
/// # Use Cases
/// - "Are these two signals moving together?"
/// - Latency correlation across venues
/// - Co-movement detection
#[derive(Debug, Clone)]
pub struct Covariance {
    count: u64,
    mean_x: f64,
    mean_y: f64,
    m2_x: f64,
    m2_y: f64,
    co_moment: f64,
}

impl Covariance {
    /// Creates a new empty accumulator.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            count: 0,
            mean_x: 0.0,
            mean_y: 0.0,
            m2_x: 0.0,
            m2_y: 0.0,
            co_moment: 0.0,
        }
    }

    /// Feeds a paired sample.
    ///
    /// Does not validate `x` or `y`; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::statistics::Covariance;
    ///
    /// let mut c = Covariance::new();
    /// for x in [1.0, 2.0, 3.0] {
    ///     c.update(x, 2.0 * x);
    /// }
    /// assert_eq!(c.covariance(), Some(2.0));
    /// ```
    #[inline]
    pub fn update(&mut self, x: f64, y: f64) {
        self.count += 1;
        let weight = 1.0 / self.count as f64;
        let dx = step_mean(&mut self.mean_x, x, weight);
        let dy = step_mean(&mut self.mean_y, y, weight);

        self.m2_x += dx.before * dx.after;
        self.m2_y += dy.before * dy.after;
        self.co_moment += dx.before * dy.after;
    }

    /// Checked update. Feeds the pair, or returns an error and leaves the
    /// accumulator unchanged if `x` or `y` is NaN, infinite, or larger in
    /// magnitude than `1e120` (see [input limits](crate#input-limits)).
    ///
    /// # Errors
    ///
    /// `x` is checked first, so its error is the one returned if both are
    /// refused.
    ///
    /// - [`DataError::NotANumber`](crate::DataError::NotANumber) if either
    ///   is NaN.
    /// - [`DataError::Infinite`](crate::DataError::Infinite) if either is
    ///   infinite.
    /// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if either
    ///   is finite and larger in magnitude than `1e120`.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::{DataError, statistics::Covariance};
    ///
    /// let mut c = Covariance::new();
    /// assert_eq!(c.checked_update(1.0, 2.0), Ok(()));
    /// assert_eq!(c.checked_update(1.0, f64::NAN), Err(DataError::NotANumber));
    /// assert_eq!(c.count(), 1);
    /// ```
    #[inline]
    pub fn checked_update(&mut self, x: f64, y: f64) -> Result<(), crate::DataError> {
        crate::math::check_input(x, crate::math::LIMIT_FOR_SQUARES)?;
        crate::math::check_input(y, crate::math::LIMIT_FOR_SQUARES)?;
        self.update(x, y);
        Ok(())
    }

    /// Number of paired samples processed.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Mean of X, or `None` if empty.
    #[must_use]
    pub fn mean_x(&self) -> Option<f64> {
        if self.count == 0 {
            return None;
        }

        Some(self.mean_x)
    }

    /// Mean of Y, or `None` if empty.
    #[must_use]
    pub fn mean_y(&self) -> Option<f64> {
        if self.count == 0 {
            return None;
        }

        Some(self.mean_y)
    }

    /// Sample variance of X (N-1 denominator), or `None` if < 2 samples.
    #[must_use]
    pub fn variance_x(&self) -> Option<f64> {
        if self.count < 2 {
            return None;
        }

        Some(self.m2_x / (self.count - 1) as f64)
    }

    /// Sample variance of Y (N-1 denominator), or `None` if < 2 samples.
    #[must_use]
    pub fn variance_y(&self) -> Option<f64> {
        if self.count < 2 {
            return None;
        }

        Some(self.m2_y / (self.count - 1) as f64)
    }

    /// Sample covariance (N-1 denominator), or `None` if < 2 samples.
    #[must_use]
    pub fn covariance(&self) -> Option<f64> {
        if self.count < 2 {
            return None;
        }

        Some(self.co_moment / (self.count - 1) as f64)
    }

    /// Pearson correlation coefficient, in `[-1, 1]`.
    ///
    /// `None` with fewer than two samples, or if either variable has zero
    /// variance, which leaves the correlation undefined.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[must_use]
    pub fn correlation(&self) -> Option<f64> {
        if self.count < 2 {
            return None;
        }
        if self.m2_x <= 0.0 || self.m2_y <= 0.0 {
            return None;
        }

        // Two roots: the product of the sums can overflow or underflow.
        let scale = crate::math::sqrt(self.m2_x) * crate::math::sqrt(self.m2_y);
        // Rounding can leave the quotient just outside [-1, 1].
        Some((self.co_moment / scale).clamp(-1.0, 1.0))
    }

    /// Merges another accumulator into this one (Chan's algorithm).
    pub fn merge(&mut self, other: &Self) {
        if other.count == 0 {
            return;
        }
        if self.count == 0 {
            *self = other.clone();
            return;
        }

        let combined = self.count + other.count;
        let dx = other.mean_x - self.mean_x;
        let dy = other.mean_y - self.mean_y;
        let weight = self.count as f64 * other.count as f64 / combined as f64;

        let new_mean_x = (dx * other.count as f64).fma(1.0 / combined as f64, self.mean_x);
        let new_mean_y = (dy * other.count as f64).fma(1.0 / combined as f64, self.mean_y);

        self.co_moment += (dx * dy).fma(weight, other.co_moment);
        self.m2_x += (dx * dx).fma(weight, other.m2_x);
        self.m2_y += (dy * dy).fma(weight, other.m2_y);
        self.mean_x = new_mean_x;
        self.mean_y = new_mean_y;
        self.count = combined;
    }

    /// Whether the covariance is defined (two samples seen).
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= 2
    }

    /// Resets to empty state.
    pub fn reset(&mut self) {
        *self = Self::new();
    }
}

impl Default for Covariance {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let c = Covariance::new();
        assert_eq!(c.count(), 0);
        assert!(c.covariance().is_none());
        assert!(c.correlation().is_none());
    }

    #[test]
    fn perfect_positive_correlation() {
        let mut c = Covariance::new();
        for i in 0..100 {
            c.update(i as f64, i as f64 * 2.0);
        }
        let r = c.correlation().unwrap();
        assert!(
            (r - 1.0).abs() < 1e-10,
            "perfect positive should be 1.0, got {r}"
        );
    }

    #[test]
    fn perfect_negative_correlation() {
        let mut c = Covariance::new();
        for i in 0..100 {
            c.update(i as f64, -(i as f64));
        }
        let r = c.correlation().unwrap();
        assert!(
            (r + 1.0).abs() < 1e-10,
            "perfect negative should be -1.0, got {r}"
        );
    }

    #[test]
    fn known_covariance() {
        let mut c = Covariance::new();
        // Simple dataset: (1,2), (2,4), (3,6)
        c.update(1.0, 2.0);
        c.update(2.0, 4.0);
        c.update(3.0, 6.0);

        let cov = c.covariance().unwrap();
        // Cov(X, 2X) = 2 * Var(X). Var([1,2,3]) = 1.0. So cov = 2.0.
        assert!(
            (cov - 2.0).abs() < 1e-10,
            "covariance should be 2.0, got {cov}"
        );
    }

    #[test]
    fn merge_matches_single() {
        let data_x: [f64; 8] = [1.0, 3.0, 5.0, 7.0, 2.0, 4.0, 6.0, 8.0];
        let data_y: [f64; 8] = [2.0, 6.0, 10.0, 14.0, 4.0, 8.0, 12.0, 16.0];

        let mut single = Covariance::new();
        for i in 0..8 {
            single.update(data_x[i], data_y[i]);
        }

        let mut a = Covariance::new();
        let mut b = Covariance::new();
        for i in 0..4 {
            a.update(data_x[i], data_y[i]);
        }
        for i in 4..8 {
            b.update(data_x[i], data_y[i]);
        }
        a.merge(&b);

        assert_eq!(a.count(), single.count());
        assert!((a.covariance().unwrap() - single.covariance().unwrap()).abs() < 1e-10);
        assert!((a.correlation().unwrap() - single.correlation().unwrap()).abs() < 1e-10);
    }

    #[test]
    fn reset_clears() {
        let mut c = Covariance::new();
        c.update(1.0, 2.0);
        c.update(3.0, 4.0);
        c.reset();
        assert_eq!(c.count(), 0);
    }

    #[test]
    fn default_is_empty() {
        let c = Covariance::default();
        assert_eq!(c.count(), 0);
    }

    #[test]
    fn zero_variance_returns_none_correlation() {
        let mut c = Covariance::new();
        c.update(5.0, 1.0);
        c.update(5.0, 2.0); // X has zero variance
        assert!(c.correlation().is_none());
    }

    #[test]
    fn checked_update_refuses_bad_input_in_either_place_and_changes_nothing() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        let mut c = Covariance::new();
        c.checked_update(1.0, 2.0).unwrap();
        c.checked_update(3.0, 6.0).unwrap();
        let readings = |c: &Covariance| {
            (
                c.count(),
                c.mean_x(),
                c.mean_y(),
                c.variance_x(),
                c.variance_y(),
                c.covariance(),
            )
        };
        let before = readings(&c);

        assert_eq!(c.checked_update(f64::NAN, 1.0), Err(NotANumber));
        assert_eq!(c.checked_update(1.0, f64::NAN), Err(NotANumber));
        assert_eq!(c.checked_update(f64::INFINITY, 1.0), Err(Infinite));
        assert_eq!(c.checked_update(1.0, f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(c.checked_update(1e121, 1.0), Err(OutOfRange));
        assert_eq!(c.checked_update(1.0, -1e121), Err(OutOfRange));

        assert_eq!(readings(&c), before);
        assert_eq!(
            before,
            (2, Some(2.0), Some(4.0), Some(2.0), Some(8.0), Some(4.0))
        );
    }

    #[test]
    fn checked_update_accepts_the_limit_without_overflow() {
        let limit = crate::math::LIMIT_FOR_SQUARES;
        let mut c = Covariance::new();
        for i in 0..100_000 {
            let sign = if i % 2 == 0 { 1.0 } else { -1.0 };
            c.checked_update(sign * limit, -sign * limit).unwrap();
        }
        assert!(c.variance_x().unwrap().is_finite());
        assert!(c.variance_y().unwrap().is_finite());
        assert!(c.covariance().unwrap().is_finite());
        assert!((c.correlation().unwrap() + 1.0).abs() < 1e-9);
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let mut checked = Covariance::new();
        let mut unchecked = Covariance::new();
        for (x, y) in [(2.0, 1.0), (-7.5, 3.0), (1e9, -4.0), (0.0, 0.5)] {
            checked.checked_update(x, y).unwrap();
            unchecked.update(x, y);
        }
        assert_eq!(checked.count(), unchecked.count());
        assert_eq!(checked.mean_x(), unchecked.mean_x());
        assert_eq!(checked.mean_y(), unchecked.mean_y());
        assert_eq!(checked.variance_x(), unchecked.variance_x());
        assert_eq!(checked.variance_y(), unchecked.variance_y());
        assert_eq!(checked.covariance(), unchecked.covariance());
        assert_eq!(checked.correlation(), unchecked.correlation());
    }

    #[test]
    fn update_does_not_validate() {
        let mut c = Covariance::new();
        c.update(1e200, 1.0);
        c.update(-1e200, 2.0);
        assert_eq!(c.variance_x(), Some(f64::INFINITY));
    }

    #[test]
    fn correlation_holds_where_the_product_of_the_sums_would_not() {
        // Sums of squares near 1e240 and 1e-240: their product overflows
        // in the first case and underflows in the second.
        for scale in [1e120, 1e-120] {
            let mut c = Covariance::new();
            for i in 0..10 {
                let x = f64::from(i) * scale;
                c.update(x, 2.0 * x);
            }
            let r = c.correlation().unwrap();
            assert!((r - 1.0).abs() < 1e-12, "scale {scale}: r = {r}");
        }
    }

    #[test]
    fn correlation_never_leaves_minus_one_to_one() {
        let mut state = 7u64;
        let mut noise = || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 11) as f64 / (1u64 << 53) as f64
        };
        for _ in 0..2_000 {
            let mut c = Covariance::new();
            let slope = noise() - 0.5;
            for _ in 0..5 {
                let x = noise();
                c.update(x, slope * x);
            }
            if let Some(r) = c.correlation() {
                assert!((-1.0..=1.0).contains(&r), "r = {r}");
            }
        }
    }
}
