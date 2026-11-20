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
//! Every type has two ways in, after the standard library's `+` and
//! `checked_add`:
//!
//! - **`update`** is unchecked. It does no validation, returns its reading
//!   directly, and follows IEEE 754: a NaN or an infinity passed in makes
//!   the readings NaN from then on, and a value large enough for its square
//!   (or fourth power) to overflow makes them infinite or NaN.
//! - **`checked_update`** validates first and returns a `Result`. It
//!   refuses NaN, infinity, a magnitude above the type's input limit, and
//!   anything outside the type's domain (a non-positive sample for a
//!   harmonic mean), with a [`DataError`], and changes nothing.
//!
//! A query that takes a value has the same pair (`normalize` and
//! `checked_normalize`).
//!
//! A type that has taken bad input through `update` is put right with
//! `reset()`, which every type has. When to call it is the application's
//! decision.
//!
//! # The number contract
//!
//! For a type fed only through `checked_update` (equivalently: `update`
//! given finite input within [`INPUT_LIMIT`] in magnitude, or
//! [`INPUT_LIMIT_FOURTH_MOMENT`] for the types that say so), every `f64` a
//! method returns is a number:
//!
//! - **Never NaN.**
//! - **Finite**, except where a method documents that it can return
//!   infinity (a z-score against zero scale, for example).
//! - A result that exists as a limit is that limit. A result that is
//!   undefined for the data (a correlation with a constant series) is
//!   `None` or a named variant, never NaN and never a sentinel value.
//!   `None` otherwise means only "no reading yet".
//!
//! Types are being brought under this split and this contract cluster by
//! cluster; a type that has a `checked_update` is under both. The others
//! still validate in `update` and return a `Result` from it.

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

/// Input magnitude within which types that square their input (variances,
/// covariances, realized variances) cannot overflow: `1e120`.
///
/// Differences of two such inputs are at most `2e120`, their squares at
/// most `4e240`, and a sum of `2^64` of those is under `1e260`, so no
/// accumulator can reach infinity whatever the stream or its length.
/// `update` takes larger values and follows IEEE 754 for them;
/// `checked_update` refuses them with [`DataError::OutOfRange`].
pub const INPUT_LIMIT: f64 = 1e120;

/// Input magnitude within which the fourth-moment types cannot overflow:
/// `1e60`.
///
/// For types that raise their input to the fourth power (skewness and
/// kurtosis). The same argument as [`INPUT_LIMIT`], with fourth powers at
/// most `1.6e241`.
pub const INPUT_LIMIT_FOURTH_MOMENT: f64 = 1e60;

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
    #[doc = include_str!("../docs/statistics.md")]
    struct Statistics;
}
