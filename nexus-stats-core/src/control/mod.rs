//! Thresholds, switches and differences: small parts for acting on a
//! stream.
//!
//! # Which type do I use?
//!
//! - [`DeadBand`]: passes a value on only once it has changed by more than
//!   a threshold.
//! - [`Hysteresis`]: an on/off decision with one threshold to turn on and
//!   another to turn off, so it does not chatter.
//! - [`Debounce`]: triggers only after a number of events in a row.
//! - [`LevelCrossing`]: detects crossings of a level, with their direction,
//!   and counts them.

mod dead_band;
mod debounce;
mod hysteresis;
mod level_crossing;

pub use dead_band::*;
pub use debounce::*;
pub use hysteresis::*;
pub use level_crossing::*;
