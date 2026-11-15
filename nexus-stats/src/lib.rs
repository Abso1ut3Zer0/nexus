#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Fixed-memory, zero-allocation streaming statistics for real-time systems.
//!
//! 60+ algorithms, all O(1) per update (or O(d) for d-dimensional filters), fixed memory.
//! Core types are `no_std` compatible; types marked *(std)* require the `std` feature,
//! *(alloc)* require `alloc`, and *(std|libm)* require either `std` or `libm`.
//!
//! # Usage
//!
//! Import from the category module you need:
//!
//! ```rust
//! use nexus_stats::smoothing::Ema;
//! use nexus_stats::detection::Cusum;
//! use nexus_stats::statistics::Welford;
//! use nexus_stats::{DataError, ConfigError, Direction};
//! ```
//!
//! With the `full` feature (or individual subcrate features), advanced types
//! are available through the same module paths:
//!
//! ```rust,ignore
//! // Requires `smoothing` feature
//! use nexus_stats::smoothing::KamaF64;
//! // Requires `regression` feature
//! use nexus_stats::regression::LinearRegressionF64;
//! // Requires `detection` feature
//! use nexus_stats::signal::AutocorrelationF64;
//! ```
//!
//! # Data Quality & Error Policy
//!
//! nexus-stats distinguishes two failure categories:
//!
//! **Data errors** — NaN or Inf values reaching a streaming update.
//! These indicate upstream data quality problems (broken feeds, failed
//! computations, missing values). All update methods that accept float
//! inputs return `Result<_, DataError>`. The library rejects the input
//! and leaves internal state unchanged. The caller declares the policy:
//!
//! - `.unwrap()` to crash on bad data (testing, strict systems)
//! - Log and continue (monitoring, degraded-mode operation)
//! - Increment a counter and trigger a circuit breaker (production)
//!
//! **Programmer errors** — wrong dimensions, out-of-range indices,
//! type misuse. These are bugs in the calling code. The library panics
//! via `assert!`. Fix the code.
//!
//! ## Internal State Invariant
//!
//! Given only finite (non-NaN, non-Inf) inputs, all internal
//! accumulators remain finite for typical workloads. Extreme value
//! ranges (>1e150) or very long-running instances (billions of updates)
//! can cause internal accumulator overflow through summation. For
//! long-running systems: call `reset()` periodically, use
//! exponentially-weighted variants (EW*) which naturally bound growth,
//! or use `.max_covariance()` on RLS filters to auto-reset when the
//! covariance matrix diverges.
//!
//! # Categories
//!
//! ## Core (always available)
//!
//! | Module | Contents |
//! |--------|----------|
//! | [`smoothing`] | EMA, AsymEma, Slew |
//! | [`detection`] | CUSUM |
//! | [`statistics`] | Welford, Moments, EwmaVar, Covariance, HarmonicMean, Percentile, BipowerVariation, RollSpread *(std\|libm)*, TwoScaleRv *(alloc, std\|libm)* |
//! | [`monitoring`] | Drawdown, Windowed Min/Max, CoDel, PollSaturation, SojournSaturation, Liveness, EventRate, Jitter, ErrorRate, HawkesIntensity *(std\|libm)* |
//! | [`control`] | DeadBand, Hysteresis, Debounce, LevelCrossing, Diff |
//!
//! ## Advanced (feature-gated, re-exported from subcrates)
//!
//! | Feature | Module | Contents |
//! |---------|--------|----------|
//! | `smoothing` | `smoothing` | + Holt, KAMA, Spring, Kalman1d, WindowedMedian |
//! | `detection` | `detection` | + MOSUM, Shiryaev-Roberts, AdaptiveThreshold, RobustZ, TrendAlert, MultiGate, PageHinkley, ADWIN |
//! | `detection` | `signal` | Autocorrelation, CrossCorrelation, Entropy, TransferEntropy, PredictiveInfoBound |
//! | `detection` | `estimation` | + SPRT |
//! | `regression` | `regression` | Linear, Polynomial, EW variants, Transformed, LogisticRegression |
//! | `regression` | `learning` | LMS, NLMS, RLS, OnlineKMeans, GD, AdaGrad, Adam, UCB1, ThompsonBeta, ThompsonGamma, EpsilonGreedy, EXP3 |
//! | `regression` | `estimation` | + Kalman 2d/3d, BetaBinomial, GammaPoisson |
//! | `control` | `control` | + PeakDetector, BoolWindow |
//! | `control` | `frequency` | TopK, FlexProportion, DecayAccum |
//! | `full` | all | Everything above |
//!
//! # Features
//!
//! | Feature | Default | Enables |
//! |---------|---------|---------|
//! | `std` | yes | `WallClock`, `sqrt`/`exp` intrinsics |
//! | `alloc` | with `std` | MOSUM, KAMA, WindowedMedian, BoolWindow, adaptive filters, optimizers |
//! | `libm` | no | Pure Rust `sqrt`/`exp` fallback for `no_std` (enables Shiryaev-Roberts, etc.) |
//! | `smoothing` | no | Advanced smoothing types (Holt, KAMA, Spring, Kalman1d, WindowedMedian) |
//! | `detection` | no | Advanced detection + signal analysis (implies `smoothing`) |
//! | `regression` | no | Regression, learning, estimation types |
//! | `control` | no | Advanced control + frequency types |
//! | `full` | no | All subcrates |

// Re-export core types at crate root
pub use nexus_stats_core::{Condition, ConfigError, DataError, Direction};

/// Clock trait and implementations for time-aware stats types.
pub use nexus_stats_core::clock;

// Re-export the math module (doc-hidden, for subcrate use)
#[doc(hidden)]
pub use nexus_stats_core::math;

// Re-export the feature_vector macro
pub use nexus_stats_core::feature_vector;

// ---- Core modules (always available, from nexus-stats-core) ----

/// Smoothing and filtering primitives.
///
/// Core types (EMA, AsymEma, Slew) are always available. Advanced types
/// (Holt, KAMA, Spring, Kalman1d, WindowedMedian) require the `smoothing`
/// feature.
pub mod smoothing {
    pub use nexus_stats_core::smoothing::*;

    #[cfg(feature = "smoothing")]
    pub use nexus_stats_smoothing::*;
}

/// Change detection and anomaly detection.
///
/// CUSUM is always available. Advanced types (MOSUM, Shiryaev-Roberts,
/// AdaptiveThreshold, RobustZ, TrendAlert, MultiGate) require the
/// `detection` feature.
pub mod detection {
    pub use nexus_stats_core::detection::*;

    #[cfg(feature = "detection")]
    pub use nexus_stats_detection::detection::*;
}

/// Online feature normalization.
pub use nexus_stats_core::normalization;

/// Core streaming statistics.
pub use nexus_stats_core::statistics;

/// Monitoring and health tracking.
pub use nexus_stats_core::monitoring;

/// Control, thresholding, and differencing.
///
/// Core types (DeadBand, Hysteresis, Debounce, LevelCrossing, Diff) are
/// always available. PeakDetector and BoolWindow require the `control` feature.
pub mod control {
    pub use nexus_stats_core::control::*;

    #[cfg(feature = "control")]
    pub use nexus_stats_control::control::*;
}

// ---- Advanced modules (from subcrates, feature-gated) ----

/// Signal analysis and information theory.
///
/// Requires the `detection` feature.
#[cfg(feature = "detection")]
pub mod signal {
    pub use nexus_stats_detection::signal::*;
}

/// State estimation, Bayesian inference, and hypothesis testing.
///
/// Kalman1d is available via [`smoothing`] with the `smoothing` feature.
/// Kalman2d/3d, BetaBinomial, GammaPoisson require the `regression` feature.
/// SPRT requires the `detection` feature.
#[cfg(any(feature = "regression", feature = "detection"))]
pub mod estimation {
    #[cfg(feature = "detection")]
    pub use nexus_stats_detection::estimation::*;
    #[cfg(feature = "regression")]
    pub use nexus_stats_regression::estimation::*;
}

/// Regression and classification.
///
/// Requires the `regression` feature.
#[cfg(feature = "regression")]
pub mod regression {
    pub use nexus_stats_regression::regression::*;
}

/// Adaptive filters, online learning, and optimization.
///
/// Requires the `regression` feature.
#[cfg(feature = "regression")]
pub mod learning {
    pub use nexus_stats_regression::learning::*;
}

/// Frequency counting and scoring.
///
/// Requires the `control` feature.
#[cfg(feature = "control")]
pub mod frequency {
    pub use nexus_stats_control::frequency::*;
}
