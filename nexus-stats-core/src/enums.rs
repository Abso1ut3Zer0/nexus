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
///
/// Non-exhaustive: match the variants you handle and end with a wildcard
/// arm, so that a variant added later does not break your build.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
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

/// Error returned when a streaming update receives invalid data.
///
/// The library distinguishes three failure categories:
/// - **Construction errors** (a missing or invalid parameter) → `Result<_, ConfigError>`
/// - **Data errors** (NaN, Inf, a value outside the accepted range) → `Result<_, DataError>`
/// - **Programmer errors** (wrong dimensions, index out of range) → panic
///
/// The library makes no assumptions about the caller's policy.
/// Each system has different implications for bad data.
///
/// One type for every `update`: it says an input value was refused, and the
/// variant says why. A given method produces only the variants its
/// documentation lists. Non-exhaustive: match the reasons you handle and
/// end with a wildcard arm, so that a reason added later does not break
/// your build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DataError {
    /// Input contained NaN.
    NotANumber,
    /// Input contained positive or negative infinity.
    Infinite,
    /// Input contained a negative value where non-negative was required.
    Negative,
    /// Input was finite but outside the range the method accepts: zero where
    /// strictly positive is required, a probability above one, a magnitude
    /// beyond [`INPUT_LIMIT`](crate::INPUT_LIMIT) passed to a
    /// `checked_update`, and the like.
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
