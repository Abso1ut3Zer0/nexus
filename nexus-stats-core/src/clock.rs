use core::time::Duration;

mod sealed {
    pub trait Sealed {}
    impl Sealed for i128 {}
    #[cfg(feature = "std")]
    impl Sealed for std::time::Instant {}
}

/// A point in physical clock time, as the clocked types take it.
///
/// Implemented for `i128` nanoseconds and, with `std`, for
/// [`Instant`](std::time::Instant). `i128` is the deterministic form. The
/// same recorded times replay to the same results, and a wire `i64`
/// widens into it. A type is generic over this trait, so one instance
/// lives on one clock and the two cannot be mixed.
///
/// Sealed: it cannot be implemented outside this crate.
pub trait Timestamp: Copy + PartialOrd + core::fmt::Debug + sealed::Sealed + 'static {
    /// The time from `earlier` to `self`, or zero if `self` is not after
    /// `earlier`.
    fn since(self, earlier: Self) -> Duration;
}

impl Timestamp for i128 {
    #[inline]
    fn since(self, earlier: Self) -> Duration {
        let nanos = self.saturating_sub(earlier);
        // PERF: the common case fits a `u64`, which avoids a 128-bit divide.
        if let Ok(nanos) = u64::try_from(nanos) {
            return Duration::from_nanos(nanos);
        }
        if nanos < 0 {
            return Duration::ZERO;
        }
        long_duration(nanos)
    }
}

#[cfg(feature = "std")]
impl Timestamp for std::time::Instant {
    #[inline]
    fn since(self, earlier: Self) -> Duration {
        self.saturating_duration_since(earlier)
    }
}

/// A span of more than `u64::MAX` nanoseconds (584 years), or the longest
/// `Duration` if it does not fit one.
#[cold]
fn long_duration(nanos: i128) -> Duration {
    const NANOS_PER_SECOND: i128 = 1_000_000_000;
    let Ok(seconds) = u64::try_from(nanos / NANOS_PER_SECOND) else {
        return Duration::MAX;
    };
    Duration::new(seconds, (nanos % NANOS_PER_SECOND) as u32)
}

/// A source of monotonic u64 timestamps.
///
/// The time-aware types not yet moved to [`Timestamp`] accept `u64`
/// timestamps. The `Clock` trait bridges real-time sources to that
/// interface.
///
/// # Contract
///
/// - `stamp()` must return monotonically non-decreasing values.
/// - The unit is caller-defined (nanos, micros, ticks) — the stats
///   types don't care, as long as the window/interval parameters
///   use the same unit.
pub trait Clock {
    /// Returns the current timestamp.
    fn stamp(&self) -> u64;
}

/// Computes elapsed time between two timestamps.
///
/// Returns `to.saturating_sub(from)`. Safe for any pair of u64 values.
#[inline]
pub fn elapsed(from: u64, to: u64) -> u64 {
    to.saturating_sub(from)
}

/// Manual clock for testing or external timestamp sources.
///
/// Caller controls the timestamp via `set()`. Useful for:
/// - Deterministic testing (advance time explicitly)
/// - External timestamp sources (exchange timestamps, NTP)
/// - Replay scenarios
///
/// # Examples
///
/// ```
/// use nexus_stats_core::clock::{EpochClock, Clock};
///
/// let mut clock = EpochClock::new(0);
/// assert_eq!(clock.stamp(), 0);
/// clock.set(1_000_000);
/// assert_eq!(clock.stamp(), 1_000_000);
/// ```
pub struct EpochClock {
    now: u64,
}

impl EpochClock {
    /// Creates an epoch clock starting at the given timestamp.
    pub fn new(initial: u64) -> Self {
        Self { now: initial }
    }

    /// Sets the current timestamp.
    ///
    /// Does NOT enforce monotonicity — caller is responsible.
    #[inline]
    pub fn set(&mut self, stamp: u64) {
        self.now = stamp;
    }

    /// Advances the clock by `delta`.
    #[inline]
    pub fn advance(&mut self, delta: u64) {
        self.now = self.now.saturating_add(delta);
    }
}

impl Clock for EpochClock {
    #[inline]
    fn stamp(&self) -> u64 {
        self.now
    }
}

#[cfg(feature = "std")]
mod monotonic {
    use std::time::Instant;

    /// Wall-clock time source producing nanosecond timestamps.
    ///
    /// Wraps `std::time::Instant` internally. Each `stamp()` call returns
    /// nanoseconds elapsed since construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_stats_core::clock::MonotonicClock;
    /// use nexus_stats_core::clock::Clock;
    ///
    /// let clock = MonotonicClock::new();
    /// let t0 = clock.stamp();
    /// // ... do work ...
    /// let t1 = clock.stamp();
    /// assert!(t1 >= t0);
    /// ```
    pub struct MonotonicClock {
        epoch: Instant,
    }

    impl MonotonicClock {
        /// Creates a new wall clock anchored to `Instant::now()`.
        pub fn new() -> Self {
            Self {
                epoch: Instant::now(),
            }
        }

        /// Creates a wall clock anchored to a specific instant.
        pub fn with_epoch(epoch: Instant) -> Self {
            Self { epoch }
        }
    }

    impl Default for MonotonicClock {
        fn default() -> Self {
            Self::new()
        }
    }

    impl super::Clock for MonotonicClock {
        #[inline]
        fn stamp(&self) -> u64 {
            self.epoch.elapsed().as_nanos() as u64
        }
    }
}

#[cfg(feature = "std")]
pub use monotonic::MonotonicClock;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn epoch_clock_basic() {
        let mut c = EpochClock::new(0);
        assert_eq!(c.stamp(), 0);
        c.set(100);
        assert_eq!(c.stamp(), 100);
    }

    #[test]
    fn epoch_clock_advance() {
        let mut c = EpochClock::new(10);
        c.advance(5);
        assert_eq!(c.stamp(), 15);
    }

    #[test]
    fn epoch_clock_advance_saturates() {
        let mut c = EpochClock::new(u64::MAX - 1);
        c.advance(10);
        assert_eq!(c.stamp(), u64::MAX);
    }

    #[test]
    fn elapsed_basic() {
        assert_eq!(elapsed(10, 20), 10);
        assert_eq!(elapsed(20, 10), 0);
    }

    #[cfg(feature = "std")]
    #[test]
    fn wall_clock_monotonic() {
        let c = MonotonicClock::new();
        let t0 = c.stamp();
        let t1 = c.stamp();
        assert!(t1 >= t0);
    }

    #[cfg(feature = "std")]
    #[test]
    fn wall_clock_default() {
        let c = MonotonicClock::default();
        let _ = c.stamp();
    }

    #[test]
    fn nanoseconds_measure_the_span_between_two_times() {
        use super::Timestamp;
        use core::time::Duration;

        assert_eq!(1_500_i128.since(500), Duration::from_nanos(1_000));
        assert_eq!(7_i128.since(7), Duration::ZERO);
        // Not after: zero, not a negative span.
        assert_eq!(500_i128.since(1_500), Duration::ZERO);
        assert_eq!(i128::MIN.since(i128::MAX), Duration::ZERO);
        // Negative times are fine: only the difference matters.
        assert_eq!((-5_i128).since(-2_000_000_005), Duration::from_secs(2));
        // Past what a `u64` of nanoseconds holds.
        let long = i128::from(u64::MAX) + 1;
        assert_eq!(long.since(0), Duration::new(18_446_744_073, 709_551_616));
        // Past what a `Duration` holds.
        assert_eq!(i128::MAX.since(i128::MIN), Duration::MAX);
        assert_eq!(i128::MAX.since(0), Duration::MAX);
    }

    #[cfg(feature = "std")]
    #[test]
    fn an_instant_measures_the_same_span() {
        use super::Timestamp;
        use core::time::Duration;
        use std::time::Instant;

        let start = Instant::now();
        let later = start + Duration::from_millis(250);
        assert_eq!(later.since(start), Duration::from_millis(250));
        assert_eq!(start.since(later), Duration::ZERO);
        assert_eq!(start.since(start), Duration::ZERO);
    }
}
