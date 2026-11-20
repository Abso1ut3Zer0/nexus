use crate::math::MulAdd;

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
    #[inline]
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
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in. A
    /// NaN or an infinity makes the readings NaN from then on, until
    /// [`reset`](Self::reset); a finite value above
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT) in magnitude can overflow them. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, x: f64, y: f64) {
        self.count += 1;
        // One reciprocal and two multiplies, not two divisions: measured 2
        // ticks faster here and 5 faster in `HalfLife`, which runs this per
        // sample. (A consumer that chains more arithmetic onto the new means
        // pays for the multiply instead; `CrossCorrelation` keeps its own
        // lag-0 accumulators for that reason.)
        let inv_n = 1.0 / self.count as f64;

        let dx = x - self.mean_x;
        let dy = y - self.mean_y;

        self.mean_x += dx * inv_n;
        self.mean_y += dy * inv_n;

        // Use the NEW mean_x but OLD mean_y for the co-moment update
        let dx2 = x - self.mean_x;
        self.co_moment += dx * (y - self.mean_y);

        // Welford M2 updates
        self.m2_x += dx * dx2;
        let dy2 = y - self.mean_y;
        self.m2_y += dy * dy2;
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
    pub fn checked_update(&mut self, x: f64, y: f64) -> Result<(), crate::DataError> {
        check_magnitude!(x, crate::INPUT_LIMIT);
        check_magnitude!(y, crate::INPUT_LIMIT);
        self.update(x, y);
        Ok(())
    }

    /// Number of paired samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Mean of X, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn mean_x(&self) -> Option<f64> {
        if self.count == 0 {
            None
        } else {
            Some(self.mean_x)
        }
    }

    /// Mean of Y, or `None` if empty.
    #[inline]
    #[must_use]
    pub fn mean_y(&self) -> Option<f64> {
        if self.count == 0 {
            None
        } else {
            Some(self.mean_y)
        }
    }

    /// Sample variance of X (N-1 denominator), or `None` if < 2 samples.
    #[inline]
    #[must_use]
    pub fn variance_x(&self) -> Option<f64> {
        if self.count < 2 {
            None
        } else {
            Some(self.m2_x / (self.count - 1) as f64)
        }
    }

    /// Sample variance of Y (N-1 denominator), or `None` if < 2 samples.
    #[inline]
    #[must_use]
    pub fn variance_y(&self) -> Option<f64> {
        if self.count < 2 {
            None
        } else {
            Some(self.m2_y / (self.count - 1) as f64)
        }
    }

    /// Sample covariance (N-1 denominator), or `None` if < 2 samples.
    #[inline]
    #[must_use]
    pub fn covariance(&self) -> Option<f64> {
        if self.count < 2 {
            None
        } else {
            Some(self.co_moment / (self.count - 1) as f64)
        }
    }

    /// Pearson correlation coefficient, or `None` if < 2 samples.
    ///
    /// Returns a value in [-1, 1]. Returns `None` if either variable
    /// has zero variance (undefined correlation).
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn correlation(&self) -> Option<f64> {
        if self.count < 2 {
            return None;
        }
        if self.m2_x <= 0.0 || self.m2_y <= 0.0 {
            return None;
        }
        // Two square roots: the product of the two sums of squares can
        // overflow or underflow where neither sum does. Rounding can leave
        // the quotient a hair outside [-1, 1].
        let scale = crate::math::sqrt(self.m2_x) * crate::math::sqrt(self.m2_y);
        Some((self.co_moment / scale).clamp(-1.0, 1.0))
    }

    /// Merges another accumulator into this one (Chan's algorithm).
    #[inline]
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
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= 2
    }

    /// Resets to empty state.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new();
    }
}

impl Default for Covariance {
    #[inline]
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
    fn rejects_nan_and_inf() {
        let mut c = Covariance::new();
        // NaN in x
        assert_eq!(
            c.checked_update(f64::NAN, 1.0),
            Err(crate::DataError::NotANumber)
        );
        // NaN in y
        assert_eq!(
            c.checked_update(1.0, f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        // Inf in x
        assert_eq!(
            c.checked_update(f64::INFINITY, 1.0),
            Err(crate::DataError::Infinite)
        );
        // Neg inf in y
        assert_eq!(
            c.checked_update(1.0, f64::NEG_INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(c.count(), 0);
    }
}
