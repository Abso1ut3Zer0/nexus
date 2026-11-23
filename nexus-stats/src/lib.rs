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
//! Every crate is on by default. To compile less, turn the defaults off and
//! name the features you need (`smoothing`, `detection`, `regression`,
//! `control`, `trading`, `monitoring`, `normalization`); their types come
//! through the same module paths:
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
//! ## Always available
//!
//! | Module | Contents |
//! |--------|----------|
//! | [`statistics`] | Welford, Moments, Covariance, HarmonicMean, Percentile, BucketAccumulator, FirstDiff, SecondDiff, CovarianceMatrix *(alloc)* |
//! | `storage` *(alloc)* | Ring, the fixed-capacity ring the windowed types share |
//!
//! ## Behind a feature (all on by default)
//!
//! | Feature | Module | Contents |
//! |---------|--------|----------|
//! | `smoothing` | `smoothing` | Ema, AsymEma, Slew, EwmVar, Holt, Spring, HuberEma, Kama *(alloc)*, Hampel *(alloc)*, WindowedMedian *(alloc)* |
//! | `detection` | `detection` | Cusum, DistributionShift *(std\|libm)*, Mosum, ShiryaevRoberts, AdaptiveThreshold, RobustZScore, TrendAlert, MultiGate, PageHinkley, Adwin, Bocpd, DistDrift |
//! | `detection` | `signal` | HalfLife *(std\|libm)*, Hurst *(alloc, std\|libm)*, Autocorrelation *(alloc)*, CrossCorrelation *(alloc)*, Entropy, TransferEntropy, PredictiveInfoBound *(all three alloc, std\|libm)* |
//! | `detection` | `estimation` | + SprtBernoulli, SprtGaussian |
//! | `regression` | `regression` | LinearRegression, PolynomialRegression, EwLinearRegression, EwPolynomialRegression, ExponentialRegression, LogarithmicRegression, PowerRegression (+ `Ew*`), LogisticRegression, HitRate, LaggedPredictor, SignalDecayCurve |
//! | `regression` + `alloc` | `learning` | LmsFilter, NlmsFilter, RlsFilter, HuberRegression, OnlineKMeans, OnlineGd, AdaGrad, Adam, Ucb1, ThompsonBeta, ThompsonGamma, EpsilonGreedy, Exp3 |
//! | `regression` | `estimation` | + Kalman1d, Kalman2d, Kalman3d, BetaBinomial, GammaPoisson |
//! | `control` | `control` | DeadBand, Hysteresis, Debounce, LevelCrossing, PeakDetector, BoolWindow *(alloc)* |
//! | `control` | `frequency` | FlexProportionGlobal, FlexProportionLocal, TopK *(alloc)*, DecayAccum *(std\|libm)* |
//! | `monitoring` | `monitoring` | Drawdown, RunningMax, RunningMin, WindowedMax, WindowedMin, MaxGauge, PeakHold, CoDel, PollSaturation, SojournSaturation, Liveness, EventRate, Jitter, ErrorRate, HawkesIntensity *(std\|libm)* |
//! | `normalization` | `normalization` | MinMaxNorm, ZScoreNorm *(std\|libm)*, QuantileNorm *(alloc)* |
//! | `trading` | `trading` | Amihud, Lpm, Cvar, BipowerVariation *(std\|libm)*, RollSpread *(std\|libm)*, TwoScaleRv *(alloc, std\|libm)*, VarianceRatio *(alloc, std\|libm)*, KyleLambda *(with `regression`)* |
//! | `full` | all | Everything above |
//!
//! # Features
//!
//! | Feature | Default | Enables |
//! |---------|---------|---------|
//! | `std` | yes | `MonotonicClock`, `sqrt`/`exp` intrinsics; implies `alloc` |
//! | `alloc` | no (implied by `std`) | Mosum, Kama, Hampel, WindowedMedian, BoolWindow, TopK, the correlations and entropies, adaptive filters, optimizers, bandits |
//! | `libm` | no | Pure Rust `sqrt`/`exp` fallback for `no_std` (enables ShiryaevRoberts, AdaptiveThreshold, HalfLife, ...) |
//! | `smoothing` | yes | The smoothers, and `EwmVar` |
//! | `detection` | yes | The detectors, and signal analysis (implies `smoothing`) |
//! | `regression` | yes | Regression, learning and estimation types |
//! | `control` | yes | PeakDetector, BoolWindow, and the frequency types |
//! | `trading` | yes | Trading and market-microstructure statistics |
//! | `monitoring` | yes | Monitors for a running system |
//! | `normalization` | yes | Normalizers (brings in `nexus-stats-monitoring`) |
//! | `full` | yes | All of the seven above |

// Re-export core types at crate root
pub use nexus_stats_core::{Accuracy, Condition, ConfigError, DataError, Direction};

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

// ---- Always available, from nexus-stats-core ----

/// Descriptive statistics: summaries of the samples seen.
pub use nexus_stats_core::statistics;
#[cfg(feature = "alloc")]
pub use nexus_stats_core::storage;

// ---- From the sub-crates, each behind a feature (all on by default) ----

/// Smoothers, and the exponentially weighted mean and variance.
///
/// Requires the `smoothing` feature.
#[cfg(feature = "smoothing")]
pub mod smoothing {
    pub use nexus_stats_smoothing::*;
}

/// Change detection and anomaly detection.
///
/// Requires the `detection` feature.
#[cfg(feature = "detection")]
pub mod detection {
    pub use nexus_stats_detection::detection::*;
}

/// Normalizers: put a stream on a common scale.
///
/// Requires the `normalization` feature.
#[cfg(feature = "normalization")]
pub mod normalization {
    pub use nexus_stats_normalization::*;
}

/// Monitors for a running system: extremes, rates, liveness, queue health.
///
/// Requires the `monitoring` feature.
#[cfg(feature = "monitoring")]
pub mod monitoring {
    pub use nexus_stats_monitoring::*;
}
/// Thresholds, switches and peak detection.
///
/// Requires the `control` feature.
#[cfg(feature = "control")]
pub mod control {
    pub use nexus_stats_control::control::*;
}

/// Signal analysis and information theory.
///
/// Requires the `detection` feature. Most types here hold a lag window or a
/// frequency table and need `alloc` as well.
#[cfg(all(
    feature = "detection",
    any(feature = "alloc", feature = "std", feature = "libm")
))]
pub mod signal {
    pub use nexus_stats_detection::signal::*;
}

/// State estimation, Bayesian inference, and hypothesis testing.
///
/// `Kalman1d`, `Kalman2d`, `Kalman3d`, `BetaBinomial` and `GammaPoisson`
/// require the `regression` feature.
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

/// Trading and market-microstructure statistics.
///
/// Requires the `trading` feature. `KyleLambda` also needs `regression`.
#[cfg(feature = "trading")]
pub mod trading {
    pub use nexus_stats_trading::*;
}
