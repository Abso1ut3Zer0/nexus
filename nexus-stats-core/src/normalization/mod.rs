//! Normalizers: each puts a stream on a common scale, one sample at a time.
//!
//! # Which type do I use?
//!
//! - [`ZScoreNorm`]: how many standard deviations a sample is from the
//!   recent mean. Not bounded, so it also serves as an outlier score.
//! - [`MinMaxNorm`]: where a sample sits between the recent minimum and
//!   maximum, from 0 to 1.
//! - [`QuantileNorm`]: a sample's rank among those seen, from 0 to 1,
//!   whatever the shape of the distribution.

#[cfg(any(feature = "std", feature = "libm"))]
mod zscore;
#[cfg(any(feature = "std", feature = "libm"))]
pub use zscore::*;

mod minmax;
pub use minmax::*;

#[cfg(feature = "alloc")]
mod quantile;
#[cfg(feature = "alloc")]
pub use quantile::*;
