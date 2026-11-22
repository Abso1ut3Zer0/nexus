#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Advanced control and frequency primitives for [`nexus-stats`](https://docs.rs/nexus-stats).
//!
//! This crate provides control and frequency types separated from the core
//! `nexus-stats` crate.
//!
//! # Which type do I use?
//!
//! - `PeakDetector`: local highs and lows that stand out by a set margin.
//! - `BoolWindow`: the share of passes over the last so many events.
//! - `TopK`: the most frequent items in a stream, in fixed memory.
//! - `FlexProportion`: each key's share of an event count that decays.
//! - `DecayAccum`: a score that builds with events and decays with time.
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
