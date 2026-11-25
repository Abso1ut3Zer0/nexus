// The old `Clock` items below are deprecated and still refer to each other.
#![allow(deprecated)]

use core::time::Duration;

/// A point on a clock, as the clocked types take it.
///
/// A clock is anything that only moves forward: wall time, a count of
/// events or trades, traded volume. A tick can say how far it is from an
/// earlier one, in whatever that clock counts in. The caller brings the
/// clock and keeps it monotonic. An `update` that takes a tick ignores
/// one that is not at or after the last it took, and its guarded form
/// reports it.
///
/// A type is generic over its tick, so one instance lives on one clock.
///
/// | Tick | [`Span`] | Meaning |
/// |---|---|---|
/// | `i128`, `i64` | [`Duration`] | nanoseconds of physical time |
/// | [`Nanos`], [`Micros`], [`Millis`], [`Seconds`] | [`Duration`] | physical time in the named unit |
/// | [`Instant`](std::time::Instant) | [`Duration`] | physical time |
/// | `u64`, `u32` | itself | a counter in the caller's unit |
/// | `f64` | `f64` | a running quantity in the caller's unit, such as volume |
///
/// A raw signed integer (`i128`, `i64`) is always nanoseconds, and a raw
/// unsigned one (`u64`, `u32`) is always a plain count. For time in another unit use the named type, so
/// the unit is stated where the time enters. Only the difference of two
/// ticks is used, so the epoch does not matter.
///
/// Implement it for your own clock type: a decimal volume, or a newtype
/// over another crate's time type. Subtracting two large values of an
/// `f64` clock loses precision, so keep such a clock small or reset it.
/// `since` must return zero when `self` is not after `earlier`. That
/// covers a tick with no place in the order, such as a NaN on an `f64`
/// clock. The span to or from it is zero.
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
/// The integer forms are deterministic. The same recorded times replay
/// to the same results. The types whose settings are real time (a window
/// of five seconds, a load over one minute) are bound by this trait.
///
/// Every tick whose span is a [`Duration`] is a timestamp. To bring your
/// own time type, a newtype over another crate's instant for example,
/// implement [`Tick`] for it with `Span = Duration`.
pub trait Timestamp: Tick<Span = Duration> {}

impl<T: Tick<Span = Duration>> Timestamp for T {}

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

impl Tick for i64 {
    type Span = Duration;

    #[inline]
    fn since(self, earlier: Self) -> Duration {
        Duration::from_nanos(gap(self, earlier))
    }
}

/// Nanoseconds, as an `i128`. The same as a raw `i128`, with the unit in
/// the name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Nanos(pub i128);

/// Microseconds. As Unix time it reaches the year 294,247.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Micros(pub i64);

/// Milliseconds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Millis(pub i64);

/// Seconds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Seconds(pub i64);

impl Tick for Nanos {
    type Span = Duration;

    #[inline]
    fn since(self, earlier: Self) -> Duration {
        self.0.since(earlier.0)
    }
}

impl Tick for Micros {
    type Span = Duration;

    #[inline]
    fn since(self, earlier: Self) -> Duration {
        Duration::from_micros(gap(self.0, earlier.0))
    }
}

impl Tick for Millis {
    type Span = Duration;

    #[inline]
    fn since(self, earlier: Self) -> Duration {
        Duration::from_millis(gap(self.0, earlier.0))
    }
}

impl Tick for Seconds {
    type Span = Duration;

    #[inline]
    fn since(self, earlier: Self) -> Duration {
        Duration::from_secs(gap(self.0, earlier.0))
    }
}

/// How far `later` is past `earlier`, or zero if it is not after it. The
/// distance between any two `i64`s fits a `u64`.
#[inline]
fn gap(later: i64, earlier: i64) -> u64 {
    if later <= earlier {
        return 0;
    }
    later.wrapping_sub(earlier) as u64
}

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

/// A NaN is not a point on the clock. It is not after any tick and no
/// tick is after it, so the span to or from a NaN is zero, and a type
/// that takes ticks never takes one.
impl Tick for f64 {
    type Span = Self;

    /// Zero if `self` is not after `earlier`, a NaN on either side
    /// included.
    #[inline]
    fn since(self, earlier: Self) -> Self {
        (self - earlier).max(0.0)
    }
}

/// A span of more than `u64::MAX` nanoseconds (584 years).
#[cold]
fn long_duration(nanos: i128) -> Duration {
    duration_from_nanos(nanos.unsigned_abs())
}

/// A count of nanoseconds as a `Duration`, or the longest `Duration` if it
/// does not fit one. `Duration::from_nanos` takes only a `u64`.
#[doc(hidden)]
#[inline]
#[must_use]
pub fn duration_from_nanos(nanos: u128) -> Duration {
    const NANOS_PER_SECOND: u128 = 1_000_000_000;
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
/// Deprecated. The clocked types take a [`Tick`] or a [`Timestamp`]
/// directly, and the caller brings the clock.
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

    /// A time type of the caller's own is a timestamp once its span is a
    /// `Duration`.
    #[test]
    fn a_caller_can_bring_a_timestamp() {
        use core::time::Duration;

        #[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
        struct Micros(i64);

        impl Tick for Micros {
            type Span = Duration;
            fn since(self, earlier: Self) -> Duration {
                Duration::from_micros(self.0.saturating_sub(earlier.0).max(0) as u64)
            }
        }

        fn span_of<T: Timestamp>(later: T, earlier: T) -> Duration {
            later.since(earlier)
        }

        assert_eq!(
            span_of(Micros(2_500), Micros(500)),
            Duration::from_millis(2)
        );
        assert_eq!(span_of(Micros(500), Micros(2_500)), Duration::ZERO);
    }

    #[test]
    fn a_raw_i64_is_nanoseconds() {
        use core::time::Duration;

        assert_eq!(1_500_i64.since(500), Duration::from_nanos(1_000));
        assert_eq!(500_i64.since(1_500), Duration::ZERO);
        assert_eq!(7_i64.since(7), Duration::ZERO);
        assert_eq!((-5_i64).since(-2_000_000_005), Duration::from_secs(2));
        // The whole range: the distance fits a `u64` of nanoseconds.
        assert_eq!(i64::MAX.since(i64::MIN), Duration::from_nanos(u64::MAX));
        assert_eq!(i64::MIN.since(i64::MAX), Duration::ZERO);
        // The same span as on an `i128`.
        assert_eq!(i64::MAX.since(-3), i128::from(i64::MAX).since(-3));
    }

    #[test]
    fn the_named_types_measure_in_their_unit() {
        use core::time::Duration;

        assert_eq!(Nanos(2_500).since(Nanos(500)), Duration::from_nanos(2_000));
        assert_eq!(Micros(2_500).since(Micros(500)), Duration::from_millis(2));
        assert_eq!(Millis(2_500).since(Millis(500)), Duration::from_secs(2));
        assert_eq!(
            Seconds(2_500).since(Seconds(500)),
            Duration::from_secs(2_000)
        );
        // Not after: zero.
        assert_eq!(Nanos(1).since(Nanos(2)), Duration::ZERO);
        assert_eq!(Micros(1).since(Micros(2)), Duration::ZERO);
        assert_eq!(Millis(1).since(Millis(2)), Duration::ZERO);
        assert_eq!(Seconds(1).since(Seconds(2)), Duration::ZERO);
        // The whole range of each fits a `Duration`.
        assert_eq!(
            Micros(i64::MAX).since(Micros(i64::MIN)),
            Duration::from_micros(u64::MAX)
        );
        assert_eq!(
            Millis(i64::MAX).since(Millis(i64::MIN)),
            Duration::from_millis(u64::MAX)
        );
        assert_eq!(
            Seconds(i64::MAX).since(Seconds(i64::MIN)),
            Duration::from_secs(u64::MAX)
        );
        assert_eq!(Nanos(i128::MAX).since(Nanos(i128::MIN)), Duration::MAX);
        // They order as their numbers do.
        assert!(Millis(-1) < Millis(0) && Seconds(3) > Seconds(2));
    }

    /// One moment written in each unit is the same distance from another.
    #[test]
    fn every_unit_agrees_on_the_same_span() {
        use core::time::Duration;

        let want = Duration::from_secs(90);
        assert_eq!(Seconds(1_700_000_090).since(Seconds(1_700_000_000)), want);
        assert_eq!(
            Millis(1_700_000_090_000).since(Millis(1_700_000_000_000)),
            want
        );
        assert_eq!(
            Micros(1_700_000_090_000_000).since(Micros(1_700_000_000_000_000)),
            want
        );
        assert_eq!(
            1_700_000_090_000_000_000_i64.since(1_700_000_000_000_000_000),
            want
        );
        assert_eq!(
            Nanos(1_700_000_090_000_000_000).since(Nanos(1_700_000_000_000_000_000)),
            want
        );
    }
}
