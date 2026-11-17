/// A source of monotonic u64 timestamps.
///
/// All nexus-stats time-aware types accept `u64` timestamps.
/// The `Clock` trait bridges real-time sources to that interface.
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
}
