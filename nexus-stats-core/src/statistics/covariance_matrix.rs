//! Streaming d×d covariance matrix with exponential weighting.

use crate::math::MulAdd;
use alloc::vec;
use alloc::vec::Vec;

/// Streaming d×d covariance matrix with exponential weighting.
///
/// Tracks means and an EW covariance matrix from observation vectors.
/// All updates are O(d²) per sample. Memory: O(d²) for the matrix.
///
/// # Use Cases
///
/// - Natural gradient optimizer (Fisher information approximation)
/// - Portfolio risk decomposition
/// - Feature correlation monitoring
#[derive(Debug, Clone)]
pub struct OnlineCovariance {
    cov: Vec<f64>,
    means: Vec<f64>,
    dim: usize,
    alpha: f64,
    count: u64,
}

/// Builder for [`OnlineCovariance`].
#[derive(Debug, Clone)]
pub struct OnlineCovarianceBuilder {
    dim: Option<usize>,
    alpha: Option<f64>,
}

impl OnlineCovariance {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> OnlineCovarianceBuilder {
        OnlineCovarianceBuilder {
            dim: None,
            alpha: None,
        }
    }

    /// Feed an observation vector.
    ///
    /// # Panics
    ///
    /// Panics if `observation.len() != dim`.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` or `DataError::Infinite` if any
    /// element is not finite.
    pub fn update(&mut self, observation: &[f64]) -> Result<(), crate::DataError> {
        assert_eq!(
            observation.len(),
            self.dim,
            "observation dimension ({}) != configured dim ({})",
            observation.len(),
            self.dim,
        );
        for &v in observation {
            check_finite!(v);
        }

        self.count += 1;
        let d = self.dim;

        if self.count == 1 {
            self.means.copy_from_slice(observation);
            // Covariance stays at zero — need 2+ samples.
            return Ok(());
        }

        // Compute all deltas from current (pre-update) means BEFORE modifying
        // anything. This ensures the covariance update uses consistent deltas —
        // mixing old and new means would introduce bias in cov[i,i].
        let alpha = self.alpha;
        let one_minus_alpha = 1.0 - alpha;

        // Temporarily repurpose means as deltas: means[i] = obs[i] - old_mean[i].
        // Then update covariance, then restore means to new_mean.
        // This avoids any allocation.
        for i in 0..d {
            self.means[i] = observation[i] - self.means[i]; // means[i] is now delta_i
        }

        // Update covariance using the stable EW recurrence.
        // The (1 - alpha) factor on the increment matches the scalar EwmaVar
        // recurrence: cov = (1-α) * cov + α * (1-α) * δ_i * δ_j.
        // Without it, covariance would be biased upward by ~1/(1-α).
        let alpha_times_one_minus = alpha * one_minus_alpha;
        for i in 0..d {
            for j in i..d {
                let idx = i * d + j;
                self.cov[idx] = one_minus_alpha * self.cov[idx]
                    + alpha_times_one_minus * self.means[i] * self.means[j];
                if i != j {
                    self.cov[j * d + i] = self.cov[idx];
                }
            }
        }

        // Restore means: new_mean = old_mean + alpha * delta = (obs - delta) + alpha * delta
        //                         = obs - delta * (1 - alpha)
        for i in 0..d {
            self.means[i] = (-self.means[i]).fma(one_minus_alpha, observation[i]);
        }

        Ok(())
    }

    /// Covariance between dimensions `i` and `j`.
    ///
    /// Returns `None` if fewer than 2 observations have been fed
    /// (covariance is undefined with fewer than 2 data points).
    #[inline]
    #[must_use]
    pub fn covariance(&self, i: usize, j: usize) -> Option<f64> {
        if !self.is_primed() {
            return None;
        }
        debug_assert!(i < self.dim && j < self.dim);
        Some(self.cov[i * self.dim + j])
    }

    /// Pearson correlation between dimensions `i` and `j`.
    ///
    /// Returns `None` if not primed or if either variance is zero.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn correlation(&self, i: usize, j: usize) -> Option<f64> {
        let var_i = self.variance(i)?;
        let var_j = self.variance(j)?;
        if var_i < f64::EPSILON || var_j < f64::EPSILON {
            return None;
        }
        Some(self.covariance(i, j)? / (crate::math::sqrt(var_i) * crate::math::sqrt(var_j)))
    }

    /// Variance of dimension `i`.
    ///
    /// Returns `None` if not primed.
    #[inline]
    #[must_use]
    pub fn variance(&self, i: usize) -> Option<f64> {
        self.covariance(i, i)
    }

    /// Mean of dimension `i`.
    ///
    /// Returns `None` if no observations have been fed.
    #[inline]
    #[must_use]
    pub fn mean(&self, i: usize) -> Option<f64> {
        if self.count == 0 {
            return None;
        }
        Some(self.means[i])
    }

    /// The full covariance matrix as a flat row-major slice.
    ///
    /// Returns zeroes if not primed — check [`is_primed()`](Self::is_primed)
    /// before interpreting values.
    #[inline]
    #[must_use]
    pub fn as_matrix(&self) -> &[f64] {
        &self.cov
    }

    /// Dimensionality.
    #[inline]
    #[must_use]
    pub fn dim(&self) -> usize {
        self.dim
    }

    /// Whether at least 2 observations have been fed.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= 2
    }

    /// Number of observations processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Reset to initial state.
    pub fn reset(&mut self) {
        self.cov.iter_mut().for_each(|v| *v = 0.0);
        self.means.iter_mut().for_each(|v| *v = 0.0);
        self.count = 0;
    }
}

impl OnlineCovarianceBuilder {
    /// Number of dimensions (required).
    #[inline]
    #[must_use]
    pub fn dim(mut self, d: usize) -> Self {
        self.dim = Some(d);
        self
    }

    /// Halflife for exponential weighting (required).
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn halflife(mut self, h: f64) -> Self {
        let alpha = 1.0 - crate::math::exp(-core::f64::consts::LN_2 / h);
        self.alpha = Some(alpha);
        self
    }

    /// Direct smoothing factor.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Build.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError` if dim or alpha are missing/invalid.
    pub fn build(self) -> Result<OnlineCovariance, crate::ConfigError> {
        let dim = self.dim.ok_or(crate::ConfigError::Missing("dim"))?;
        if dim == 0 {
            return Err(crate::ConfigError::Invalid("dim must be > 0"));
        }
        let alpha = self
            .alpha
            .ok_or(crate::ConfigError::Missing("halflife or alpha"))?;
        if !(alpha > 0.0 && alpha < 1.0) {
            return Err(crate::ConfigError::Invalid("alpha must be in (0, 1)"));
        }

        Ok(OnlineCovariance {
            cov: vec![0.0; dim * dim],
            means: vec![0.0; dim],
            dim,
            alpha,
            count: 0,
        })
    }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    fn basic_cov(dim: usize) -> OnlineCovariance {
        OnlineCovariance::builder()
            .dim(dim)
            .halflife(50.0)
            .build()
            .unwrap()
    }

    #[test]
    fn uncorrelated_2d() {
        let mut cov = basic_cov(2);
        // Feed independent signals
        for i in 0..200 {
            let x = (i % 10) as f64;
            let y = ((i * 7) % 13) as f64;
            cov.update(&[x, y]).unwrap();
        }
        // Variances should be positive
        assert!(cov.variance(0).unwrap() > 0.0);
        assert!(cov.variance(1).unwrap() > 0.0);
        // Correlation should be near zero (not perfectly, small sample)
        let corr = cov.correlation(0, 1).unwrap().abs();
        assert!(corr < 0.5, "expected low correlation, got {corr}");
    }

    #[test]
    fn perfectly_correlated_2d() {
        let mut cov = basic_cov(2);
        for i in 0..200 {
            let x = i as f64;
            cov.update(&[x, x.mul_add(2.0, 1.0)]).unwrap();
        }
        let corr = cov.correlation(0, 1).unwrap();
        assert!(corr > 0.95, "expected high correlation, got {corr}");
    }

    #[test]
    fn symmetry() {
        let mut cov = basic_cov(3);
        for i in 0..100 {
            let v = [i as f64, (i * 2) as f64, (i * 3) as f64];
            cov.update(&v).unwrap();
        }
        for i in 0..3 {
            for j in 0..3 {
                assert!(
                    (cov.covariance(i, j).unwrap() - cov.covariance(j, i).unwrap()).abs() < 1e-10,
                    "cov({i},{j}) != cov({j},{i})"
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "observation dimension")]
    fn wrong_dimension_panics() {
        let mut cov = basic_cov(3);
        let _ = cov.update(&[1.0, 2.0]);
    }

    #[test]
    fn priming() {
        let mut cov = basic_cov(2);
        assert!(!cov.is_primed());
        assert!(cov.covariance(0, 1).is_none());
        assert!(cov.correlation(0, 1).is_none());
        assert!(cov.variance(0).is_none());
        assert!(cov.mean(0).is_none());

        cov.update(&[1.0, 2.0]).unwrap();
        assert!(!cov.is_primed());
        assert!(cov.covariance(0, 1).is_none());
        assert!(cov.mean(0).is_some()); // mean available after 1 sample

        cov.update(&[3.0, 4.0]).unwrap();
        assert!(cov.is_primed());
        assert!(cov.covariance(0, 1).is_some());
    }

    #[test]
    fn reset_clears() {
        let mut cov = basic_cov(2);
        for i in 0..50 {
            cov.update(&[i as f64, i as f64]).unwrap();
        }
        cov.reset();
        assert_eq!(cov.count(), 0);
        assert!(!cov.is_primed());
    }

    #[test]
    fn invalid_config() {
        assert!(OnlineCovariance::builder().alpha(0.1).build().is_err()); // missing dim
        assert!(OnlineCovariance::builder().dim(2).build().is_err()); // missing alpha
        assert!(
            OnlineCovariance::builder()
                .dim(0)
                .alpha(0.1)
                .build()
                .is_err()
        ); // dim = 0
    }
}
