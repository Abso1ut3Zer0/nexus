#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Core types shared across the nexus-stats ecosystem.
//!
//! This crate provides the fundamental streaming statistics types used by
//! `nexus-stats` and all its subcrates. Not intended for direct use —
//! import from `nexus-stats` instead.
//!
//! Includes: error types, math utilities, core smoothing (EMA, AsymEma, Slew),
//! statistics (Welford, Moments, EwmaVar, Covariance, HarmonicMean, Percentile),
//! monitoring, core detection (CUSUM), and core control types.
//!
//! # `update` and `checked_update`
//!
//! Like `+` and `checked_add` in the standard library:
//!
//! - `update` does not validate its input; arithmetic follows IEEE 754.
//! - `checked_update` returns a [`DataError`] and leaves the state unchanged
//!   if the input is NaN, infinite, or outside the bound the type
//!   documents. For most types that bound is [`INPUT_LIMIT`].
//!
//! A type fed only through `checked_update` never returns NaN.
//!
//! Types are moving to this pair one at a time. Until a type has a
//! `checked_update`, its `update` validates and returns a `Result`.

#[cfg(feature = "alloc")]
extern crate alloc;

mod enums;
#[macro_use]
#[doc(hidden)]
pub mod math;
mod feature_vector;

/// Clock trait and implementations.
pub mod clock;

/// Fixed-capacity storage shared by the windowed types (`alloc`).
#[cfg(feature = "alloc")]
pub mod storage;

pub use enums::{Condition, ConfigError, DataError, Direction};

/// The largest magnitude `checked_update` accepts, on a type that does not
/// document its own bound: `1e120`.
///
/// Within it, a sum of squared differences cannot overflow for any stream
/// length: `2^64 * (2e120)^2 < 1e260`.
pub const INPUT_LIMIT: f64 = 1e120;

/// The numeric types the generic monitors accept. Sealed: named as bounds,
/// implemented only here.
pub mod sample;
#[doc(hidden)]
pub use sample::{AlphaEma, EmaKernel, ShiftEma};
pub use sample::{Float, Sample};

/// Control, thresholding, and differencing.
pub mod control;
/// Change detection.
pub mod detection;
/// Monitoring and health tracking.
pub mod monitoring;
/// Online feature normalization.
pub mod normalization;
/// Smoothing and filtering primitives.
pub mod smoothing;
/// Core streaming statistics.
pub mod statistics;

/// The doc pages under `docs/` whose examples are compiled and run as
/// doctests, so a page cannot drift from the API it describes.
#[cfg(all(doctest, feature = "std"))]
mod doc_pages {
    #[doc = include_str!("../docs/control.md")]
    struct Control;
    #[doc = include_str!("../docs/detection.md")]
    struct Detection;
    #[doc = include_str!("../docs/normalization.md")]
    struct Normalization;
    #[doc = include_str!("../docs/smoothing.md")]
    struct Smoothing;
}
