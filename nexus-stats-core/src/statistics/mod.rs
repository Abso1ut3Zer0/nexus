//! Streaming statistics: each type takes one sample at a time, in fixed
//! memory.
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
//! ## Is a price trending or reverting?
//!
//! - [`VarianceRatio`]: a ratio with a test statistic, over a sliding
//!   window. Cheap on every update.
//! - [`Hurst`]: one exponent over a long window. Cheap to feed, costly to
//!   read.
//! - [`HalfLife`]: how fast it reverts, if it does.
//!
//! ## Volatility from prices
//!
//! - [`TwoScaleRv`]: realized variance with tick noise taken out.
//! - [`BipowerVariation`]: realized variance with jumps taken out.
//!
//! ## Liquidity
//!
//! - [`Amihud`]: how far the price moves per unit traded.
//! - [`RollSpread`]: the effective spread, from trade prices alone.
//!
//! ## Risk, and how good a forecast is
//!
//! - [`Lpm`]: downside moments, such as semivariance.
//! - [`Cvar`]: expected shortfall.
//! - [`HitRate`]: how often a forecast has the direction right.
//!
//! ## Bars
//!
//! - [`BucketAccumulator`]: open, high, low, close and volume-weighted
//!   price over a bucket.

mod amihud;
#[cfg(any(feature = "std", feature = "libm"))]
mod bipower;
mod bucket;
mod covariance;
#[cfg(feature = "alloc")]
mod covariance_matrix;
mod cvar;
mod ewm_var;
#[cfg(any(feature = "std", feature = "libm"))]
mod half_life;
mod harmonic_mean;
mod hit_rate;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod hurst;
mod lpm;
mod moments;
mod percentile;
#[cfg(any(feature = "std", feature = "libm"))]
mod roll_spread;
mod running_mean;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod two_scale_rv;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod variance_ratio;
mod welford;

pub use amihud::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use bipower::*;
pub use bucket::*;
pub use covariance::*;
#[cfg(feature = "alloc")]
pub use covariance_matrix::*;
pub use cvar::*;
pub use ewm_var::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use half_life::*;
pub use harmonic_mean::*;
pub use hit_rate::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use hurst::*;
pub use lpm::*;
pub use moments::*;
pub use percentile::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use roll_spread::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use two_scale_rv::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use variance_ratio::*;
pub use welford::*;
