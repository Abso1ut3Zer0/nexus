#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Advanced control and frequency primitives for [`nexus-stats`](https://docs.rs/nexus-stats).
//!
//! This crate provides control and frequency types separated from the core
//! `nexus-stats` crate.
//!
//! Types are organized into submodules:
//! - [`control`] — PeakDetector, BoolWindow
//! - [`frequency`] — TopK, FlexProportion, DecayAccum

#[cfg(feature = "alloc")]
extern crate alloc;
#[macro_use]
extern crate nexus_stats_core;

// Internal modules
mod peak_detector;

#[cfg(feature = "alloc")]
mod bool_window;

/// Advanced control types.
pub mod control {
    pub use super::peak_detector::*;

    #[cfg(feature = "alloc")]
    pub use super::bool_window::*;
}

/// Frequency counting and scoring.
pub mod frequency;
