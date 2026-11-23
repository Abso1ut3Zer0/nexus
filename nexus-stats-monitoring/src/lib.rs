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
//! - [`RunningMax`] and [`RunningMin`]: the extreme since the last reset.
//! - [`WindowedMax`] and [`WindowedMin`]: the extreme over a sliding window
//!   of time.
//! - [`PeakHold`]: a peak that decays.
//! - [`MaxGauge`]: the maximum since it was last read.
//! - [`Drawdown`]: the fall from the highest value seen.
//!
//! ## Rates and timing
//!
//! - [`EventRate`]: events per unit of time, smoothed.
//! - [`ErrorRate`]: the share of events that failed.
//! - [`Jitter`]: how much consecutive samples or arrivals vary.
//! - [`Liveness`]: whether anything has happened recently.
//! - [`HawkesIntensity`]: the rate of events that come in clusters.
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
#[macro_use]
extern crate nexus_stats_core;

mod codel;
mod drawdown;
mod error_rate;
mod event_rate;
#[cfg(any(feature = "std", feature = "libm"))]
mod hawkes;
mod jitter;
mod liveness;
mod max_gauge;
mod peak_hold;
mod poll_saturation;
mod running;
mod sojourn_saturation;
mod windowed;
pub use codel::*;
pub use drawdown::*;
pub use error_rate::*;
pub use event_rate::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use hawkes::*;
pub use jitter::*;
pub use liveness::*;
pub use max_gauge::*;
pub use peak_hold::*;
pub use poll_saturation::*;
pub use running::*;
pub use sojourn_saturation::*;
pub use windowed::*;

// What appears in this crate's signatures, so it can be used on its own.
pub use nexus_stats_core::{Condition, ConfigError, DataError, Sample};

/// The README's examples, compiled and run as doc tests.
#[cfg(all(doctest, feature = "std"))]
#[doc = include_str!("../README.md")]
struct Readme;
