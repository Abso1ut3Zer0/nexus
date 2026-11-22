#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Advanced smoothing algorithms for [`nexus-stats`](https://docs.rs/nexus-stats).
//!
//! This crate provides smoothing types that are separated from the core
//! `nexus-stats` crate to keep the base dependency lightweight. All types
//! stream with fixed memory after construction; the EMA family is O(1) per
//! update, the windowed types (`WindowedMedian`, `Kama`, `Hampel`) O(window).
//!
//! # Types
//!
//! | Type | Description | Feature |
//! |------|-------------|---------|
//! | [`Holt`] | Double exponential smoothing (level + trend) | — |
//! | [`Spring`] | Critically damped spring (chase without overshoot) | — |
//! | [`Kalman1d`] | 1D Kalman filter (position + velocity) | — |
//! | [`HuberEma`] | Outlier-robust EMA (bounded step per observation) | — |
//! | [`Kama`] | Kaufman Adaptive Moving Average | `alloc` |
//! | [`Hampel`] | Three-zone outlier filter (pass / Winsorize / reject) | `alloc` |
//! | [`WindowedMedian<f64>`] | Running median over a sliding window (f64) | `alloc` |
//! | [`WindowedMedian<i64>`] | Running median over a sliding window (i64) | `alloc` |
//!
//! # Re-export
//!
//! When the `smoothing` feature is enabled on `nexus-stats`, these types are
//! available via `nexus_stats::smoothing::*`. Or depend on this crate directly
//! for `nexus_stats_smoothing::*`.

#[cfg(feature = "alloc")]
extern crate alloc;
#[macro_use]
extern crate nexus_stats_core;

mod holt;
mod kalman1d;
mod spring;

mod huber_ema;

#[cfg(feature = "alloc")]
mod hampel;
#[cfg(feature = "alloc")]
mod kama;
#[cfg(feature = "alloc")]
mod windowed_median;

pub use holt::*;
pub use huber_ema::*;
pub use kalman1d::*;
pub use spring::*;

#[cfg(feature = "alloc")]
pub use hampel::*;
#[cfg(feature = "alloc")]
pub use kama::*;
#[cfg(feature = "alloc")]
pub use windowed_median::*;
