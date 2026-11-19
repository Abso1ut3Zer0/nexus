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
    #[doc = include_str!("../docs/smoothing.md")]
    struct Smoothing;
}
