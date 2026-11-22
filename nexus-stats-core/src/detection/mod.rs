//! Change detection: has the behavior of a stream shifted?
//!
//! # Which type do I use?
//!
//! - [`Cusum`]: a lasting shift in the mean. One stray sample does not
//!   trip it.
//! - [`DistributionShift`]: a change in shape (skewness, kurtosis), even
//!   with the mean where it was.
//!
//! Detectors for a passing spike, a single outlier, a trend toward a limit
//! and more are in the `nexus-stats-detection` crate.

mod cusum;
#[cfg(any(feature = "std", feature = "libm"))]
mod distribution_shift;

pub use cusum::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use distribution_shift::*;
