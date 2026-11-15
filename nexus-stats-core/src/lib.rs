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

pub use enums::{Condition, ConfigError, DataError, Direction};

/// The numeric types the generic monitors accept (sealed).
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
