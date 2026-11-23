#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Control and frequency primitives for
//! [`nexus-stats`](https://docs.rs/nexus-stats): thresholds, switches, peak
//! detection, and counting what is frequent.
//!
//! # Which type do I use?
//!
//! ## Acting on a stream ([`control`])
//!
//! - `DeadBand`: passes a value on only once it has changed by more than a
//!   threshold.
//! - `Hysteresis`: an on/off decision with one threshold to turn on and
//!   another to turn off, so it does not chatter.
//! - `Debounce`: triggers only after a number of events in a row.
//! - `LevelCrossing`: detects crossings of a level, with their direction,
//!   and counts them.
//! - `PeakDetector`: local highs and lows that stand out by a set margin.
//! - `BoolWindow`: the share of passes over the last so many events.
//!
//! ## Counting ([`frequency`])
//!
//! - `TopK`: the most frequent items in a stream, in fixed memory.
//! - `FlexProportion`: each key's share of an event count that decays.
//! - `DecayAccum`: a score that builds with events and decays with time.

#[cfg(feature = "alloc")]
extern crate alloc;
#[macro_use]
extern crate nexus_stats_core;

// Internal modules
mod dead_band;
mod debounce;
mod hysteresis;
mod level_crossing;
mod peak_detector;

#[cfg(feature = "alloc")]
mod bool_window;

/// Thresholds, switches and peak detection.
pub mod control {
    pub use super::dead_band::*;
    pub use super::debounce::*;
    pub use super::hysteresis::*;
    pub use super::level_crossing::*;
    pub use super::peak_detector::*;

    #[cfg(feature = "alloc")]
    pub use super::bool_window::*;
}

/// Frequency counting and scoring.
pub mod frequency;
