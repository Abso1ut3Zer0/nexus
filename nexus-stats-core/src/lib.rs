#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Core types shared across the nexus-stats ecosystem.
//!
//! This crate provides the fundamental streaming statistics types used by
//! `nexus-stats` and all its subcrates. Not intended for direct use —
//! import from `nexus-stats` instead.
//!
//! Includes: error types, math utilities, core smoothing (EMA, AsymEma, Slew),
//! statistics (Welford, Moments, EwmVar, Covariance, HarmonicMean, Percentile),
//! monitoring, core detection (CUSUM), and core control types.
//!
//! # `update` and `checked_update`
//!
//! Like `+` and `checked_add` in the standard library:
//!
//! - `update` does not validate its input; arithmetic follows IEEE 754.
//! - `checked_update` returns a [`DataError`] and leaves the state unchanged
//!   if the input is NaN, infinite, or outside the bound the type
//!   documents (see [input limits](#input-limits)).
//!
//! A type fed only through `checked_update` never returns NaN.
//!
//! Types are moving to this pair one at a time. Until a type has a
//! `checked_update`, its `update` validates and returns a `Result`.
//!
//! # Input limits
//!
//! `checked_update` bounds its input so that the type's sums cannot
//! overflow, however long the stream:
//!
//! - `1e120` for a type that squares its input, such as a variance or a
//!   covariance: `2^64 * (2e120)^2 < 1e260`.
//! - `1e60` for `Moments`, which raises it to the fourth power:
//!   `2^64 * (2e60)^4 < 1e261`.
//! - `[1e-120, 1e120]` for `HarmonicMean`, which sums reciprocals.
//! - A type that takes a logarithm of its input, or tests its own running
//!   sum, has no magnitude limit and says so.
//!
//! These are our own bounds, chosen with a wide margin under the largest
//! `f64`: the first two keep the powered term within `1e240`. No convention
//! sets them.

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

pub use enums::{Accuracy, Condition, ConfigError, DataError, Direction};

/// The numeric types the generic monitors accept. Sealed: named as bounds,
/// implemented only here.
pub mod sample;
#[doc(hidden)]
pub use sample::{AlphaEma, EmaKernel, ShiftEma};
pub use sample::{Float, Sample};

pub mod control;
pub mod detection;
pub mod monitoring;
pub mod normalization;
pub mod smoothing;
pub mod statistics;
