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
//! | `Kalman2d` | 2D Kalman filter | — |
//! | `Kalman3d` | 3D Kalman filter | — |
//! | `BetaBinomial` | Beta-Binomial conjugate estimator | `std` or `libm` |
//! | `GammaPoisson` | Gamma-Poisson conjugate estimator | `std` or `libm` |
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
/// Regression and classification.
pub mod regression;
