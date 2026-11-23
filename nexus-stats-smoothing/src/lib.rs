#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Smoothers for [`nexus-stats`](https://docs.rs/nexus-stats): each takes a
//! sample and returns the smoothed value, in fixed memory. The exponentially
//! weighted types cost the same for every update; the windowed ones
//! ([`WindowedMedian`], [`Kama`], [`Hampel`]) cost the window.
//!
//! # Which smoother?
//!
//! Start with [`Ema`]: an exponential moving average, in which recent
//! samples count more and old ones fade. It is usually the right answer.
//! Move off it for a reason:
//!
//! - The spread around the average is wanted too: [`EwmVar`], the
//!   exponentially weighted mean and variance.
//! - It should rise and fall at different speeds: [`AsymEma`].
//! - It may move only so far per sample: [`Slew`].
//! - The signal has a trend, and an average lags it: [`Holt`].
//! - It swings between trending and ranging: [`Kama`], which smooths more
//!   when the signal is choppy.
//! - A moving target is to be chased without overshoot: [`Spring`].
//! - Some samples are outliers. In order of how hard they are discounted:
//!   [`HuberEma`] bounds each step, [`Hampel`] shrinks or rejects them, and
//!   [`WindowedMedian`] ignores up to half the window.
//!
//! A filter with a noise model, for position and velocity, is `Kalman1d`
//! in the regression crate's `estimation` module.
//!
//! # Re-export
//!
//! When the `smoothing` feature is enabled on `nexus-stats`, these types are
//! available via `nexus_stats::smoothing::*`. Or depend on this crate directly
//! for `nexus_stats_smoothing::*`.

#[cfg(feature = "alloc")]
extern crate alloc;
// The old validation macro: only the unconverted `alloc` types still use it.
#[cfg_attr(feature = "alloc", macro_use)]
extern crate nexus_stats_core;

mod asym_ema;
mod ema;
mod ewm_var;
mod holt;
mod slew;
mod spring;

mod huber_ema;

#[cfg(feature = "alloc")]
mod hampel;
#[cfg(feature = "alloc")]
mod kama;
#[cfg(feature = "alloc")]
mod windowed_median;

pub use asym_ema::*;
pub use ema::*;
pub use ewm_var::*;
pub use holt::*;
pub use huber_ema::*;
pub use slew::*;
pub use spring::*;

#[cfg(feature = "alloc")]
pub use hampel::*;
#[cfg(feature = "alloc")]
pub use kama::*;
#[cfg(feature = "alloc")]
pub use windowed_median::*;

// What appears in this crate's signatures, so it can be used on its own.
pub use nexus_stats_core::{ConfigError, DataError, Sample};

/// The README's examples, compiled and run as doc tests.
#[cfg(all(doctest, feature = "std"))]
#[doc = include_str!("../README.md")]
struct Readme;
