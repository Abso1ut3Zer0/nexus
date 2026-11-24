// The old `Clock` items below are deprecated and still refer to each other.
#![allow(deprecated)]

use core::time::Duration;

mod sealed {
    pub trait Sealed {}
    impl Sealed for i128 {}
    #[cfg(feature = "std")]
    impl Sealed for std::time::Instant {}
}

/// A point on a clock, as the clocked types take it.
///
/// A clock is anything that only moves forward: wall time, a count of
/// events or trades, traded volume. A tick can say how far it is from an
/// earlier one, in whatever that clock counts in. The caller brings the
/// clock and keeps it monotonic; a type that takes ticks ignores one that
/// is not at or after the last it took, and its guarded form reports it.
///
/// A type is generic over its tick, so one instance lives on one clock.
///
/// | Tick | [`Span`] | Meaning |
/// |---|---|---|
/// | `i128` | [`Duration`] | nanoseconds of physical time ([`Timestamp`]) |
/// | [`Instant`](std::time::Instant) | [`Duration`] | physical time ([`Timestamp`]) |
/// | `u64`, `u32` | itself | a counter in the caller's unit |
/// | `f64` | `f64` | a running quantity in the caller's unit, such as volume |
///
/// Implement it for your own clock type, a decimal volume for example.
/// `since` must return zero when `self` is not after `earlier`.
pub trait Tick: Copy + PartialOrd + core::fmt::Debug + 'static {
    /// What this clock counts in.
    type Span: Span;

    /// How far `self` is past `earlier`, or zero if it is not after it.
    fn since(self, earlier: Self) -> Self::Span;
}

/// The distance between two [`Tick`]s.
///
/// A statistical model works in `f64`, so a span can report itself as
/// one. A [`Duration`] reports seconds. A span on any other clock reports
/// that clock's own unit.
pub trait Span: Copy + PartialOrd + core::fmt::Debug + 'static {
    /// This span as a number, in the clock's unit.
    fn as_f64(self) -> f64;
}

/// A [`Tick`] of physical clock time. Its span is a [`Duration`].
///
/// Implemented for `i128` nanoseconds and, with `std`, for
/// [`Instant`](std::time::Instant). `i128` is the deterministic form. The
/// same recorded times replay to the same results, and a wire `i64`
/// widens into it. The types whose settings are real time (a window of
/// five seconds, a load over one minute) are bound by this trait.
///
/// Sealed: it cannot be implemented outside this crate.
pub trait Timestamp: Tick<Span = Duration> + sealed::Sealed {}

impl Span for Duration {
    #[inline]
    fn as_f64(self) -> f64 {
        self.as_secs_f64()
    }
}

impl Span for u64 {
    #[inline]
    fn as_f64(self) -> f64 {
        self as f64
    }
}

impl Span for u32 {
    #[inline]
    fn as_f64(self) -> f64 {
        f64::from(self)
    }
}

impl Span for f64 {
    #[inline]
    fn as_f64(self) -> f64 {
        self
    }
}

impl Timestamp for i128 {}

impl Tick for i128 {
    type Span = Duration;

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
impl Timestamp for std::time::Instant {}

#[cfg(feature = "std")]
impl Tick for std::time::Instant {
    type Span = Duration;

    #[inline]
    fn since(self, earlier: Self) -> Duration {
        self.saturating_duration_since(earlier)
    }
}

impl Tick for u64 {
    type Span = Self;

    #[inline]
    fn since(self, earlier: Self) -> Self {
        self.saturating_sub(earlier)
    }
}

impl Tick for u32 {
    type Span = Self;

    #[inline]
    fn since(self, earlier: Self) -> Self {
        self.saturating_sub(earlier)
    }
}

impl Tick for f64 {
    type Span = Self;

    /// Zero if either tick is NaN.
    #[inline]
    fn since(self, earlier: Self) -> Self {
        (self - earlier).max(0.0)
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

#[deprecated(
    note = "the clocked types take a `Tick` or a `Timestamp`; bring your own monotonic clock"
)]
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

#[deprecated(
    note = "the clocked types take a `Tick` or a `Timestamp`; bring your own monotonic clock"
)]
/// Computes elapsed time between two timestamps.
///
/// Returns `to.saturating_sub(from)`. Safe for any pair of u64 values.
#[inline]
pub fn elapsed(from: u64, to: u64) -> u64 {
    to.saturating_sub(from)
}

#[deprecated(
    note = "the clocked types take a `Tick` or a `Timestamp`; bring your own monotonic clock"
)]
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

    #[deprecated(
        note = "the clocked types take a `Tick` or a `Timestamp`; bring your own monotonic clock"
    )]
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
        use core::time::Duration;
        use std::time::Instant;

        let start = Instant::now();
        let later = start + Duration::from_millis(250);
        assert_eq!(later.since(start), Duration::from_millis(250));
        assert_eq!(start.since(later), Duration::ZERO);
        assert_eq!(start.since(start), Duration::ZERO);
    }

    #[test]
    fn a_counter_measures_in_its_own_unit() {
        assert_eq!(1_500_u64.since(500), 1_000);
        assert_eq!(500_u64.since(1_500), 0);
        assert_eq!(u64::MAX.since(0), u64::MAX);
        assert_eq!(9_u32.since(4), 5);
        assert_eq!(4_u32.since(9), 0);
    }

    #[test]
    fn a_float_clock_measures_in_its_own_unit() {
        assert_eq!(12.5_f64.since(2.0), 10.5);
        assert_eq!(2.0_f64.since(12.5), 0.0);
        assert_eq!(f64::INFINITY.since(0.0), f64::INFINITY);
        // A NaN on either side is no distance.
        assert_eq!(f64::NAN.since(1.0), 0.0);
        assert_eq!(1.0_f64.since(f64::NAN), 0.0);
    }

    #[test]
    fn a_span_reports_itself_as_a_number() {
        use core::time::Duration;

        // A duration in seconds, every other span in its own unit.
        assert_eq!(Duration::from_millis(250).as_f64(), 0.25);
        assert_eq!(7_u64.as_f64(), 7.0);
        assert_eq!(7_u32.as_f64(), 7.0);
        assert_eq!(2.5_f64.as_f64(), 2.5);
    }

    /// A clock of the caller's own, in a fixed-point decimal.
    #[test]
    fn a_caller_can_bring_a_clock() {
        #[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
        struct Lots(i64); // hundredths of a lot

        impl Span for Lots {
            fn as_f64(self) -> f64 {
                self.0 as f64 / 100.0
            }
        }

        impl Tick for Lots {
            type Span = Self;
            fn since(self, earlier: Self) -> Self {
                Self((self.0 - earlier.0).max(0))
            }
        }

        assert_eq!(Lots(1_250).since(Lots(1_000)).as_f64(), 2.5);
        assert_eq!(Lots(1_000).since(Lots(1_250)), Lots(0));
    }
}
