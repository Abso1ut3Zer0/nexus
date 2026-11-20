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
//! Modelled on the standard library's `+` and `checked_add`.
//!
//! - `update` does the arithmetic and nothing else. It does not validate
//!   its input and follows IEEE 754, as `f64` arithmetic does.
//! - `checked_update` validates first and returns a `Result`. It refuses
//!   NaN, infinity, and a value large enough to overflow the type (see
//!   [`INPUT_LIMIT`]), with a [`DataError`], and leaves the state
//!   unchanged. Fed only through `checked_update`, a type never returns
//!   NaN.
//!
//! `reset()` returns a type to its starting state.
//!
//! Types are being moved to this pair one at a time. A type without a
//! `checked_update` still validates inside `update` and returns a `Result`
//! from it.

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

/// The largest input magnitude `checked_update` accepts on types that
/// square their input: `1e120`.
///
/// The difference of two such inputs is at most `2e120` and its square at
/// most `4e240`, so a sum of `2^64` of them stays under `1e260`: a variance
/// cannot overflow, whatever the stream or its length.
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
