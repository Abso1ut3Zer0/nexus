#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Fixed-memory, zero-allocation streaming statistics for real-time systems.
//!
//! 60+ algorithms. Scalar types are O(1) per update; window and dimension types
//! (`WindowedMedian`, `Kama`, `Hampel`, `Bocpd`, `RlsFilter`, `CovarianceMatrix`,
//! `OnlineKMeans`, `QuantileNorm`) cost O(window) or O(d²) and say so on their page.
//! Memory is fixed after construction.
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
//! use nexus_stats::smoothing::Kama;
//! // Requires `regression` feature
//! use nexus_stats::regression::LinearRegression;
//! // Requires `detection` feature
//! use nexus_stats::signal::Autocorrelation;
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
//! | [`smoothing`] | Ema, AsymEma, Slew |
//! | [`detection`] | Cusum, DistributionShift *(std\|libm)* |
//! | [`statistics`] | Welford, Moments, EwmVar, Covariance, HarmonicMean, Percentile, BipowerVariation, Cvar, Lpm, HitRate, Amihud, BucketAccumulator, HalfLife *(std\|libm)*, RollSpread *(std\|libm)*, Hurst *(alloc, std\|libm)*, TwoScaleRv *(alloc, std\|libm)*, CovarianceMatrix *(alloc)*, VarianceRatio *(alloc)* |
//! | [`monitoring`] | Drawdown, RunningMax, RunningMin, WindowedMax, WindowedMin, MaxGauge, PeakHold, CoDel, PollSaturation, SojournSaturation, Liveness, EventRate, Jitter, ErrorRate, HawkesIntensity *(std\|libm)* |
//! | [`control`] | DeadBand, Hysteresis, Debounce, LevelCrossing, FirstDiff, SecondDiff |
//! | [`normalization`] | MinMaxNorm, ZScoreNorm *(std\|libm)*, QuantileNorm *(alloc)* |
//! | `storage` *(alloc)* | Ring, the fixed-capacity ring the windowed types share |
//!
//! ## Advanced (feature-gated, re-exported from subcrates)
//!
//! | Feature | Module | Contents |
//! |---------|--------|----------|
//! | `smoothing` | `smoothing` | + Holt, Spring, Kalman1d, HuberEma, Kama *(alloc)*, Hampel *(alloc)*, WindowedMedian *(alloc)* |
//! | `detection` | `detection` | + Mosum, ShiryaevRoberts, AdaptiveThreshold, RobustZScore, TrendAlert, MultiGate, PageHinkley, Adwin, Bocpd, DistDrift |
//! | `detection` + `alloc` | `signal` | Autocorrelation, CrossCorrelation, Entropy *(std\|libm)*, TransferEntropy *(std\|libm)*, PredictiveInfoBound *(std\|libm)* |
//! | `detection` | `estimation` | + SprtBernoulli, SprtGaussian |
//! | `regression` | `regression` | LinearRegression, PolynomialRegression, EwLinearRegression, EwPolynomialRegression, ExponentialRegression, LogarithmicRegression, PowerRegression (+ `Ew*`), LogisticRegression, KyleLambda, LaggedPredictor, SignalDecayCurve |
//! | `regression` + `alloc` | `learning` | LmsFilter, NlmsFilter, RlsFilter, HuberRegression, OnlineKMeans, OnlineGd, AdaGrad, Adam, Ucb1, ThompsonBeta, ThompsonGamma, EpsilonGreedy, Exp3 |
//! | `regression` | `estimation` | + Kalman2d, Kalman3d, BetaBinomial, GammaPoisson |
//! | `control` | `control` | + PeakDetector, BoolWindow *(alloc)* |
//! | `control` | `frequency` | FlexProportionGlobal, FlexProportionLocal, TopK *(alloc)*, DecayAccum *(std\|libm)* |
//! | `full` | all | Everything above |
//!
//! # Features
//!
//! | Feature | Default | Enables |
//! |---------|---------|---------|
//! | `std` | yes | `MonotonicClock`, `sqrt`/`exp` intrinsics; implies `alloc` |
//! | `alloc` | no (implied by `std`) | Mosum, Kama, Hampel, WindowedMedian, BoolWindow, TopK, the correlations and entropies, adaptive filters, optimizers, bandits |
//! | `libm` | no | Pure Rust `sqrt`/`exp` fallback for `no_std` (enables ShiryaevRoberts, AdaptiveThreshold, HalfLife, ...) |
//! | `smoothing` | no | Advanced smoothing types (Holt, Kama, Spring, Kalman1d, WindowedMedian, ...) |
//! | `detection` | no | Advanced detection + signal analysis (implies `smoothing`) |
//! | `regression` | no | Regression, learning, estimation types |
//! | `control` | no | Advanced control + frequency types |
//! | `full` | no | All subcrates |

// Re-export core types at crate root
pub use nexus_stats_core::{Condition, ConfigError, DataError, Direction};

/// Sealed numeric bounds of the generic types: [`Sample`] (`f64`, `i64`) and
/// [`Float`] (`f64`, `f32`). Name them in your own signatures
/// (`fn f<T: Sample>(d: &mut monitoring::Drawdown<T>)`); they cannot be
/// implemented outside `nexus-stats-core`.
pub use nexus_stats_core::{Float, Sample};

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
/// Core types (`Ema`, `AsymEma`, `Slew`) are always available. Advanced types
/// (`Holt`, `Spring`, `Kalman1d`, `HuberEma`, `Kama`, `Hampel`,
/// `WindowedMedian`) require the `smoothing` feature.
pub mod smoothing {
    pub use nexus_stats_core::smoothing::*;

    #[cfg(feature = "smoothing")]
    pub use nexus_stats_smoothing::*;
}

/// Change detection and anomaly detection.
///
/// `Cusum` is always available and `DistributionShift` needs `std` or `libm`
/// (no `detection` feature). Advanced types (`Mosum`, `ShiryaevRoberts`,
/// `AdaptiveThreshold`, `RobustZScore`, `TrendAlert`, `MultiGate`,
/// `PageHinkley`, `Adwin`, `Bocpd`, `DistDrift`) require the `detection`
/// feature.
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
#[cfg(feature = "alloc")]
pub use nexus_stats_core::storage;

/// Control, thresholding, and differencing.
///
/// Core types (`DeadBand`, `Hysteresis`, `Debounce`, `LevelCrossing`, `FirstDiff`,
/// `SecondDiff`) are always available. `PeakDetector` and `BoolWindow` require the
/// `control` feature.
pub mod control {
    pub use nexus_stats_core::control::*;

    #[cfg(feature = "control")]
    pub use nexus_stats_control::control::*;
}

// ---- Advanced modules (from subcrates, feature-gated) ----

/// Signal analysis and information theory.
///
/// Requires the `detection` and `alloc` features: every type here holds a
/// lag window or a frequency table.
#[cfg(all(feature = "detection", feature = "alloc"))]
pub mod signal {
    pub use nexus_stats_detection::signal::*;
}

/// State estimation, Bayesian inference, and hypothesis testing.
///
/// Kalman1d is available via [`smoothing`] with the `smoothing` feature.
/// Kalman2d/3d, BetaBinomial, GammaPoisson require the `regression` feature.
/// `SprtBernoulli` / `SprtGaussian` require the `detection` feature.
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
/// Requires the `regression` and `alloc` features: every type here holds
/// runtime-sized weights or arms.
#[cfg(all(feature = "regression", feature = "alloc"))]
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
