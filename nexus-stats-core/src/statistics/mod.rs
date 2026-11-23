//! Descriptive statistics: summaries of the samples seen, each fed one
//! sample at a time in fixed memory. These are what the other nexus-stats
//! crates build on.
//!
//! # Which type do I use?
//!
//! ## The spread and shape of a stream
//!
//! - [`Welford`]: mean, variance and standard deviation of everything seen.
//!   The default choice.
//! - [`Moments`]: those, plus skewness and kurtosis.
//! - [`EwmVar`]: a mean and variance that follow recent samples and forget
//!   old ones.
//! - [`HarmonicMean`]: the right average for rates.
//! - [`Percentile`]: one quantile, without storing the samples.
//!
//! ## Two streams together
//!
//! - [`Covariance`]: covariance and correlation of a pair.
//! - [`CovarianceMatrix`]: the same for many streams at once.
//!
//! ## Change from one sample to the next
//!
//! - [`FirstDiff`] and [`SecondDiff`]: the change between samples, and the
//!   change in that.
//!
//! ## Bars
//!
//! - [`BucketAccumulator`]: open, high, low, close and volume-weighted
//!   price over a bucket.
//!
//! Measures of whether a series trends or reverts are in the detection
//! crate's `signal` module, and trading measures in `nexus-stats-trading`.

mod bucket;
mod covariance;
#[cfg(feature = "alloc")]
mod covariance_matrix;
mod diff;
mod ewm_var;
mod harmonic_mean;
mod moments;
mod percentile;
mod running_mean;
mod welford;

pub use bucket::*;
pub use covariance::*;
#[cfg(feature = "alloc")]
pub use covariance_matrix::*;
pub use diff::*;
pub use ewm_var::*;
pub use harmonic_mean::*;
pub use moments::*;
pub use percentile::*;
pub use welford::*;
