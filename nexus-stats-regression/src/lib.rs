#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Online regression, learning, and estimation for [`nexus-stats`](https://docs.rs/nexus-stats).
//!
//! This crate provides regression, adaptive learning, and Bayesian estimation
//! types separated from the core `nexus-stats` crate.
//!
//! # Regression Types
//!
//! | Type | Description | Feature |
//! |------|-------------|---------|
//! | `LinearRegression` | Online linear regression | — |
//! | `PolynomialRegression` | Online polynomial regression | — |
//! | `EwPolynomialRegression` | Exponentially weighted polynomial regression | — |
//! | `ExponentialRegression`, `LogarithmicRegression`, `PowerRegression` (+ `Ew*`) | Linearized exp/log/power fits | `std` or `libm` |
//! | `LogisticRegression` | Online logistic regression | `alloc` + (`std` or `libm`) |
//! | `HitRate` | How often a forecast has the direction right | — |
//!
//! # Learning Types
//!
//! | Type | Description | Feature |
//! |------|-------------|---------|
//! | `LmsFilter` | Least Mean Squares adaptive filter | `alloc` |
//! | `RlsFilter` | Recursive Least Squares adaptive filter | `alloc` |
//! | `OnlineKMeans` | Online K-Means clustering | `alloc` |
//! | `OnlineGd` | Online gradient descent optimizer | `alloc` |
//! | `AdaGrad` | AdaGrad optimizer | `alloc` + (`std` or `libm`) |
//! | `Adam` | Adam optimizer | `alloc` + (`std` or `libm`) |
//!
//! # Estimation Types
//!
//! | Type | Description | Feature |
//! |------|-------------|---------|
//! | `Kalman1d` | 1D Kalman filter (position and velocity) | — |
//! | `Kalman2d` | 2D Kalman filter | — |
//! | `Kalman3d` | 3D Kalman filter | — |
//! | `BernoulliEstimator` | Probability of a yes-or-no outcome, fitted from outcomes | the intervals and p-value need `std` or `libm` |
//! | `BernoulliModel` | What to expect of trials at a known probability | the interval needs `std` or `libm` |
//! | `PoissonEstimator` | Rate of a Poisson process, fitted from counts | the intervals and p-value need `std` or `libm` |
//! | `PoissonModel` | What count to expect at a known rate | the interval needs `std` or `libm` |
//! | `HawkesModel` | Intensity of a self-exciting point process | `std` or `libm` |
//! | `HawkesEstimator` | Fits a Hawkes process from event times | `std` or `libm` |
//!
//! # Re-export
//!
//! When the `regression` feature is enabled on `nexus-stats`, these types are
//! available via `nexus_stats::regression::*`, `nexus_stats::learning::*`,
//! and `nexus_stats::estimation::*`. Or depend on this crate directly.

#[cfg(feature = "alloc")]
extern crate alloc;
#[macro_use]
extern crate nexus_stats_core;

/// State estimation and Bayesian inference.
pub mod estimation;
/// Adaptive filters, online learning, and optimization.
pub mod learning;
#[cfg(any(feature = "std", feature = "libm"))]
mod probability;
/// Regression and classification.
pub mod regression;

/// The clock a `HawkesModel` runs on: any [`Tick`]. A [`Timestamp`] is
/// a tick of physical time.
pub use nexus_stats_core::{Micros, Millis, Nanos, Seconds, Span, Tick, Timestamp};

/// The confidence of an interval, as the summaries' and models' interval
/// methods take it.
pub use nexus_stats_core::Confidence;
/// Why a fit cannot give a model, as an estimator's `model` returns it.
pub use nexus_stats_core::FitError;
/// A probability from 0 to 1, as `BernoulliModel::new` takes it.
pub use nexus_stats_core::Probability;
