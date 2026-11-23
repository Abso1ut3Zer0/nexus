#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Trading and market-microstructure statistics for
//! [`nexus-stats`](https://docs.rs/nexus-stats).
//!
//! Streaming measures of how a market is behaving, each fed one price,
//! return or trade at a time in fixed memory. Every type follows its
//! published definition, and is checked against a reference implementation
//! where one exists.
//!
//! This is not a technical-analysis library: there are no chart indicators
//! here. It covers what a trading system needs to measure, market
//! microstructure included.
//!
//! # Which type do I use?
//!
//! ## Is the price trending or reverting?
//!
//! - [`VarianceRatio`]: Lo and MacKinlay's ratio, with a test statistic
//!   that says whether the departure from a random walk could be chance.
//!
//! ## How volatile is it?
//!
//! - [`TwoScaleRv`]: realized variance from tick data, with the noise of
//!   bid-ask bounce taken out.
//! - [`BipowerVariation`]: realized variance split into a continuous part
//!   and a jump part.
//!
//! ## What does it cost to trade?
//!
//! - [`Amihud`]: illiquidity, the price move per unit traded.
//! - [`RollSpread`]: the effective spread, from trade prices alone.
//! - [`KyleLambda`]: price impact per unit of signed volume.
//!
//! ## How much risk is in the tail?
//!
//! - [`Lpm`]: lower partial moments, such as semivariance.
//! - [`Cvar`]: conditional value at risk, the expected loss beyond a
//!   quantile.
//!
//! # Features
//!
//! `std` (default), `alloc` and `libm` as in the other nexus-stats crates.
//! `regression` (default) adds [`KyleLambda`], which is built on
//! `nexus-stats-regression`; turn it off to leave that crate out.

#[cfg(feature = "alloc")]
extern crate alloc;
#[macro_use]
extern crate nexus_stats_core;

mod amihud;
#[cfg(any(feature = "std", feature = "libm"))]
mod bipower;
mod cvar;
#[cfg(feature = "regression")]
mod kyle_lambda;
mod lpm;
#[cfg(any(feature = "std", feature = "libm"))]
mod roll_spread;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod two_scale_rv;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod variance_ratio;

pub use amihud::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use bipower::*;
pub use cvar::*;
#[cfg(feature = "regression")]
pub use kyle_lambda::*;
pub use lpm::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use roll_spread::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use two_scale_rv::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use variance_ratio::*;

// What appears in this crate's signatures, so it can be used on its own.
pub use nexus_stats_core::{Accuracy, ConfigError, DataError};

/// The README's examples, compiled and run as doc tests.
#[cfg(all(doctest, feature = "std"))]
#[doc = include_str!("../README.md")]
struct Readme;
