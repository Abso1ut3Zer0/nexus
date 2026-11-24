#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! The foundation of the nexus-stats crates, and the descriptive statistics
//! they build on.
//!
//! - The shared pieces: the error types, [`Accuracy`], the [`Sample`] and
//!   [`Float`] traits, [`math`], `storage` and [`clock`].
//! - [`statistics`]: summaries of the samples seen (Welford, Moments,
//!   Covariance, HarmonicMean, Percentile, ...).
//!
//! Every other concept has its own crate. Most users import from
//! [`nexus-stats`](https://docs.rs/nexus-stats), which re-exports them all.

#[cfg(feature = "alloc")]
extern crate alloc;

mod enums;
#[macro_use]
#[doc(hidden)]
pub mod math;
mod feature_vector;
#[doc(hidden)]
pub mod parts;

/// Clock trait and implementations.
pub mod clock;
pub use clock::Timestamp;

/// Fixed-capacity storage shared by the windowed types (`alloc`).
#[cfg(feature = "alloc")]
pub mod storage;

pub use enums::{Accuracy, Condition, ConfigError, DataError, Direction};

/// The numeric types the generic monitors accept. Sealed: named as bounds,
/// implemented only here.
pub mod sample;
#[doc(hidden)]
pub use sample::{Float, Sample};

pub mod statistics;
