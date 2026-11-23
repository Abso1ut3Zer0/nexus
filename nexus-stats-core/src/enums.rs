/// Directional change or anomaly direction.
///
/// Used by algorithms that detect shifts, anomalies, or trends in a signal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// No directional change detected.
    Neutral,
    /// Upward: mean shifted up, value is high, trend is rising.
    Rising,
    /// Downward: mean shifted down, value is low, trend is falling.
    Falling,
}

/// System condition state.
///
/// Used by algorithms that monitor health, saturation, or pressure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Condition {
    /// Within acceptable bounds.
    Normal,
    /// Exceeded threshold — degraded performance.
    Degraded,
}

/// Configuration error from building a stats primitive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfigError {
    /// A required parameter was not set.
    Missing(&'static str),
    /// A parameter value is invalid.
    Invalid(&'static str),
}

impl core::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Missing(param) => write!(f, "configuration error: {param} must be set"),
            Self::Invalid(msg) => write!(f, "configuration error: {msg}"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ConfigError {}

/// Whether the reading a windowed type gives is sound, as its `update`
/// reports it.
///
/// A type that keeps running totals over a sliding window adds each new
/// term and takes the oldest away, and every add is rounded. The errors
/// stay in the totals, and matter once the totals have become much smaller
/// than they were. Such a type estimates that error on each `update`. Once
/// it could reach the reading, there is no reading until the type's
/// `resync` method recomputes the totals from the samples it holds.
/// `resync` costs the window, so it is for the caller to schedule.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::Accuracy;
///
/// // What a caller does with the value an `update` returns.
/// fn resync_is_due(accuracy: Accuracy) -> bool {
///     match accuracy {
///         Accuracy::Sound => false,
///         // Call the type's `resync` when there is time; no reading until then.
///         Accuracy::ResyncRequired { .. } => true,
///     }
/// }
/// assert!(!resync_is_due(Accuracy::Sound));
/// assert!(resync_is_due(Accuracy::ResyncRequired { error: 0.01 }));
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Accuracy {
    /// A reading that is given is good: rounding in the totals has not
    /// reached it.
    Sound,
    /// Rounding in the totals may have reached the reading. There is no
    /// reading until the type's `resync` is called; samples are still
    /// stored.
    ResyncRequired {
        /// An estimate of the error, as a share of the reading, when this
        /// was first returned. Each type's `update` says which reading it
        /// is the error of. Never below zero and never NaN; 1 or more
        /// means no correct digits are left, and it is infinite when
        /// nothing can be said.
        error: f64,
    },
}

/// Error returned when a streaming update receives invalid data.
///
/// The library distinguishes three failure categories:
/// - **Construction errors** (a missing or invalid parameter) → `Result<_, ConfigError>`
/// - **Data errors** (NaN, Inf, a value outside the accepted range) → `Result<_, DataError>`
/// - **Programmer errors** (wrong dimensions, index out of range) → panic
///
/// The library makes no assumptions about the caller's policy.
/// Each system has different implications for bad data.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DataError {
    /// Input contained NaN.
    NotANumber,
    /// Input contained positive or negative infinity.
    Infinite,
    /// Input contained a negative value where non-negative was required.
    Negative,
    /// Input was finite but outside the range the method accepts: zero where
    /// strictly positive is required, a probability above one, and the like.
    OutOfRange,
}

impl core::fmt::Display for DataError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NotANumber => write!(f, "input contained NaN"),
            Self::Infinite => write!(f, "input contained infinity"),
            Self::Negative => write!(f, "input contained a negative value"),
            Self::OutOfRange => write!(f, "input outside the accepted range"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for DataError {}
