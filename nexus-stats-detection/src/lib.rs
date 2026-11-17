#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Advanced change detection and signal analysis for [`nexus-stats`](https://docs.rs/nexus-stats).
//!
//! This crate provides change detection, anomaly detection, signal analysis,
//! and hypothesis testing types separated from the core `nexus-stats` crate.
//!
//! Types are organized into submodules:
//! - [`detection`] — MOSUM, Shiryaev-Roberts, AdaptiveThreshold, RobustZ, TrendAlert, MultiGate, PageHinkley, ADWIN, DistDrift, BOCPD
//! - [`signal`] — Autocorrelation, CrossCorrelation, Entropy, TransferEntropy, PredictiveInfoBound
//! - [`estimation`] — SPRT (Bernoulli, Gaussian)

#[cfg(feature = "alloc")]
extern crate alloc;
#[macro_use]
extern crate nexus_stats_core;

// Internal modules
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
#[cfg(feature = "alloc")]
mod mosum;
#[cfg(any(feature = "std", feature = "libm"))]
mod shiryaev_roberts;
#[cfg(any(feature = "std", feature = "libm"))]
mod sprt;

/// Advanced change detection types.
pub mod detection {
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
