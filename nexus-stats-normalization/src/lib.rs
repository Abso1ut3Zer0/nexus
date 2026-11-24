#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Normalizers for [`nexus-stats`](https://docs.rs/nexus-stats): each puts a
//! stream on a common scale, one sample at a time.
//!
//! # Which type do I use?
//!
//! - [`ZScoreNorm`]: how many standard deviations a sample is from the
//!   recent mean. Not bounded, so it also serves as an outlier score.
//! - [`MinMaxNorm`]: where a sample sits between the recent minimum and
//!   maximum, from 0 to 1.
//! - [`QuantileNorm`]: a sample's rank among those seen, from 0 to 1,
//!   whatever the shape of the distribution.

#[cfg(feature = "alloc")]
extern crate alloc;
#[macro_use]
extern crate nexus_stats_core;

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

// What appears in this crate's signatures, so it can be used on its own.
pub use nexus_stats_core::{
    ConfigError, DataError, Float, Micros, Millis, Nanos, Seconds, Tick, Timestamp,
};

/// The README's examples, compiled and run as doc tests.
#[cfg(all(doctest, feature = "std"))]
#[doc = include_str!("../README.md")]
struct Readme;
