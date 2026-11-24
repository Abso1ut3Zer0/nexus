#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Monitors for a running system, for
//! [`nexus-stats`](https://docs.rs/nexus-stats): extremes, rates, liveness and
//! queue health.
//!
//! # Which type do I use?
//!
//! ## Highs and lows
//!
//! - [`WindowedMax`] and [`WindowedMin`]: the extreme over a sliding window
//!   of time.
//! - [`PeakHold`]: the magnitude of a signal, followed up at once, held,
//!   then left to decay.
//! - [`PeakToTrough`]: the fall from the highest value seen.
//!
//! ## Rates and timing
//!
//! - `EventRate`: events in a window, their exact rate, and the load averaged
//!   over one, five and fifteen minutes (requires `std` or `libm`).
//! - [`ErrorRate`]: the share of events that failed.
//! - [`Jitter`]: how much consecutive samples or arrivals vary.
//! - `Liveness`: how long a source has been silent, in typical gaps (requires
//!   `alloc`).
//!
//! ## Queues
//!
//! - [`CoDel`]: a queue that is not draining, from how long each item
//!   waited.
//! - [`PollSaturation`]: how saturated a consumer is, from what its polls
//!   return.
//! - [`SojournSaturation`]: the same, from stamped waiting times.
//!
//! # Weighting clocks
//!
//! Every type here states what one `update` is worth in a `# Weighting
//! clock` section of its docs: per call, per event with its own timestamp,
//! the caller's timestamps, or none. The one rule that follows: never update
//! a per-call type from a loop whose iteration time depends on the quantity
//! being measured. Sampling queue fill once per spin iteration into an EMA is
//! the classic failure: under load the loop iterates less often, so the
//! smoother sees fewer samples exactly when it matters, and a published value
//! can read healthy while most messages are late. Use a per-event type with
//! timestamps, or `PollSaturation`, which is weighted per message by
//! construction.

#[cfg(feature = "alloc")]
extern crate alloc;
mod codel;
mod error_rate;
#[cfg(any(feature = "std", feature = "libm"))]
mod event_rate;
mod jitter;
#[cfg(feature = "alloc")]
mod liveness;
mod peak_hold;
mod peak_to_trough;
mod poll_saturation;
mod sojourn_saturation;
mod windowed;
pub use codel::*;
pub use error_rate::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use event_rate::*;
pub use jitter::*;
#[cfg(feature = "alloc")]
pub use liveness::*;
pub use peak_hold::*;
pub use peak_to_trough::*;
pub use poll_saturation::*;
pub use sojourn_saturation::*;
pub use windowed::*;

// What appears in this crate's signatures, so it can be used on its own.
pub use nexus_stats_core::{Condition, ConfigError, DataError, Sample, Timestamp};

/// The README's examples, compiled and run as doc tests.
#[cfg(all(doctest, feature = "std"))]
#[doc = include_str!("../README.md")]
struct Readme;
