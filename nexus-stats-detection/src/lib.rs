#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Change detection and signal analysis for
//! [`nexus-stats`](https://docs.rs/nexus-stats): detectors that say when a
//! stream's behavior has shifted, measures of how a series behaves over
//! time, and sequential tests.
//!
//! # Which detector?
//!
//! Each tests a different question:
//!
//! - Has the mean shifted for good? `Cusum`, or `ShiryaevRoberts` when the
//!   size of the shift is known in advance.
//! - Has the shape changed, with the mean where it was?
//!   `DistributionShift`.
//! - Was there a spike that has since passed? `Mosum`.
//! - Is this one sample an outlier? `AdaptiveThreshold` for roughly normal
//!   data, `RobustZScore` for heavy tails.
//! - Is the trend heading for a limit? `TrendAlert`.
//! - Normal, warning or critical? `MultiGate`.
//! - Is the stream trending or reverting? `Autocorrelation` at one lag,
//!   `Hurst` for an exponent over a window, `HalfLife` for how fast it
//!   reverts.
//! - Which of two streams leads? `CrossCorrelation`. Does one drive the
//!   other? `TransferEntropy`, at a much higher cost.
//! - A decision as soon as the evidence allows? `SprtBernoulli` for rates,
//!   `SprtGaussian` for means.
//!
//! Types are organized into submodules:
//! - [`detection`] — Cusum, DistributionShift, MOSUM, Shiryaev-Roberts, AdaptiveThreshold, RobustZ, TrendAlert, MultiGate, PageHinkley, ADWIN, DistDrift, BOCPD
//! - [`signal`] — Autocorrelation, CrossCorrelation, Hurst, HalfLife, Entropy, TransferEntropy, PredictiveInfoBound
//! - [`estimation`] — SPRT (Bernoulli, Gaussian)

#[cfg(feature = "alloc")]
extern crate alloc;
#[macro_use]
extern crate nexus_stats_core;

// Internal modules
mod cusum;
mod multi_gate;
mod page_hinkley;
mod robust_z;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod simd_math;
mod trend_alert;

#[cfg(any(feature = "std", feature = "libm"))]
mod adaptive_threshold;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod adwin;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod bocpd;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod dist_drift;
#[cfg(any(feature = "std", feature = "libm"))]
mod distribution_shift;
#[cfg(feature = "alloc")]
mod mosum;
#[cfg(any(feature = "std", feature = "libm"))]
mod shiryaev_roberts;
#[cfg(any(feature = "std", feature = "libm"))]
mod sprt;

/// Change detectors.
pub mod detection {
    pub use super::cusum::*;
    pub use super::multi_gate::*;
    pub use super::page_hinkley::*;
    pub use super::robust_z::*;
    pub use super::trend_alert::*;

    #[cfg(any(feature = "std", feature = "libm"))]
    pub use super::adaptive_threshold::*;
    #[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
    pub use super::adwin::*;
    #[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
    pub use super::bocpd::*;
    #[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
    pub use super::dist_drift::*;
    #[cfg(any(feature = "std", feature = "libm"))]
    pub use super::distribution_shift::*;
    #[cfg(feature = "alloc")]
    pub use super::mosum::*;
    #[cfg(any(feature = "std", feature = "libm"))]
    pub use super::shiryaev_roberts::*;
}

/// Signal analysis and information theory.
pub mod signal;

/// Hypothesis testing.
pub mod estimation {
    #[cfg(any(feature = "std", feature = "libm"))]
    pub use super::sprt::*;
}
