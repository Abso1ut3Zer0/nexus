//! Clock abstractions for event-driven runtimes.
//!
//! `Clock` is a resource registered in the World. Handlers read it via
//! `Res<Clock>`. Sync sources install into the World via the `Installer`
//! trait and return pollers that sync the clock each poll loop iteration.
//!
//! Three sync sources:
//! - `RealtimeClockInstaller` → `RealtimeClockPoller` — production
//! - `TestClockInstaller` → `TestClockPoller` — deterministic testing
//! - `HistoricalClockInstaller` → `HistoricalClockPoller` — replay
//!
//! The `RealtimeClockPoller` calibration design is inspired by Agrona's
//! [`OffsetEpochNanoClock`](https://github.com/real-logic/agrona).

use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use crate::World;
use crate::driver::Installer;
use crate::world::{ResourceId, WorldBuilder};

/// Configuration error from clock construction.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ConfigError {
    /// A parameter value is invalid.
    Invalid(&'static str),
}

impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(msg) => write!(f, "clock configuration error: {msg}"),
        }
    }
}

impl std::error::Error for ConfigError {}

// =============================================================================
// Clock — the World resource
// =============================================================================

/// The current time — registered as a World resource.
///
/// Synced once per poll loop iteration by a clock poller. Handlers read
/// via `Res<Clock>`.
///
/// # Example
///
/// ```ignore
/// fn on_event(clock: Res<Clock>, event: SomeEvent) {
///     let timestamp = clock.unix_nanos();
///     let when = clock.instant();
/// }
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Clock {
    instant: Instant,
    unix_nanos: i128,
}

impl crate::world::Resource for Clock {}

impl Clock {
    /// Monotonic instant from this poll iteration.
    #[inline]
    #[must_use]
    pub fn instant(&self) -> Instant {
        self.instant
    }

    /// UTC nanoseconds since Unix epoch (1970-01-01 00:00:00 UTC).
    #[inline]
    #[must_use]
    pub fn unix_nanos(&self) -> i128 {
        self.unix_nanos
    }
}

impl Default for Clock {
    fn default() -> Self {
        Self {
            instant: Instant::now(),
            unix_nanos: 0,
        }
    }
}

// =============================================================================
// RealtimeClock — installer + poller
// =============================================================================

#[cfg(debug_assertions)]
const DEFAULT_THRESHOLD: Duration = Duration::from_micros(1);
#[cfg(not(debug_assertions))]
const DEFAULT_THRESHOLD: Duration = Duration::from_nanos(250);

#[cfg(debug_assertions)]
const MIN_THRESHOLD: Duration = Duration::from_micros(1);
#[cfg(not(debug_assertions))]
const MIN_THRESHOLD: Duration = Duration::from_nanos(100);

/// Installer for the realtime clock. Consumed at setup.
///
/// Registers a [`Clock`] resource in the World, calibrates the
/// monotonic-to-UTC offset, and returns a [`RealtimeClockPoller`].
///
/// # Example
///
/// ```ignore
/// let mut wb = WorldBuilder::new();
/// let mut clock_poller = wb.install_driver(
///     RealtimeClockInstaller::builder().build().unwrap()
/// );
/// let mut world = wb.build();
///
/// loop {
///     let now = Instant::now();
///     clock_poller.sync(&mut world, now);
///     // ...
/// }
/// ```
pub struct RealtimeClockInstaller {
    threshold: Duration,
    max_retries: u32,
    resync_interval: Duration,
}

/// Builder for [`RealtimeClockInstaller`].
pub struct RealtimeClockInstallerBuilder {
    threshold: Duration,
    max_retries: u32,
    resync_interval: Duration,
}

impl RealtimeClockInstaller {
    /// Creates a builder with sensible defaults.
    #[must_use]
    pub fn builder() -> RealtimeClockInstallerBuilder {
        RealtimeClockInstallerBuilder::default()
    }
}

impl Installer for RealtimeClockInstaller {
    type Poller = RealtimeClockPoller;

    fn install(self, world: &mut WorldBuilder) -> RealtimeClockPoller {
        // `Clock` is a shared dependency (handlers read it via `Res<Clock>`); the
        // installer owns the value it writes each `sync()`, not the slot. `ensure`
        // rather than `register` so a clock source composes even if something else
        // already registered a `Clock` — see the `Installer` trait docs.
        let clock_id = world.ensure_default::<Clock>();

        let (base_instant, base_nanos, gap) =
            RealtimeClockPoller::calibrate(self.threshold, self.max_retries);
        let accurate = gap <= self.threshold;

        RealtimeClockPoller {
            clock_id,
            base_instant,
            base_nanos,
            last_resync: base_instant,
            resync_interval: self.resync_interval,
            threshold: self.threshold,
            max_retries: self.max_retries,
            calibration_gap: gap,
            accurate,
        }
    }
}

impl Default for RealtimeClockInstaller {
    fn default() -> Self {
        Self::builder()
            .build()
            .expect("default config is always valid")
    }
}

impl std::fmt::Debug for RealtimeClockInstaller {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RealtimeClockInstaller")
            .field("threshold", &self.threshold)
            .field("max_retries", &self.max_retries)
            .field("resync_interval", &self.resync_interval)
            .finish()
    }
}

/// Runtime poller for the realtime clock.
///
/// Holds a pre-resolved `ResourceId` for the `Clock` resource and
/// calibration state. Call `sync()` once per poll loop iteration.
pub struct RealtimeClockPoller {
    clock_id: ResourceId,
    base_instant: Instant,
    base_nanos: i128,
    last_resync: Instant,
    resync_interval: Duration,
    threshold: Duration,
    max_retries: u32,
    calibration_gap: Duration,
    accurate: bool,
}

impl RealtimeClockPoller {
    /// Sync the Clock resource with the current time.
    ///
    /// Returns the [`Clock`] it just wrote (it's `Copy`), so event-loop code
    /// holding the poller can stamp/log the timestamp without a second
    /// `world.resource::<Clock>()` lookup. Ignoring the return is fine.
    #[inline]
    pub fn sync(&mut self, world: &mut World, now: Instant) -> Clock {
        if now.saturating_duration_since(self.last_resync) >= self.resync_interval {
            self.resync_at(now);
        }

        let elapsed = now.saturating_duration_since(self.base_instant);
        let nanos = self.base_nanos + elapsed.as_nanos() as i128;

        // SAFETY: clock_id was obtained via ensure_default() during install()
        // and points at the registered Clock.
        let clock = unsafe { world.get_mut::<Clock>(self.clock_id) };
        clock.instant = now;
        clock.unix_nanos = nanos;
        *clock
    }

    /// Force recalibration.
    pub fn resync(&mut self) {
        self.resync_at(Instant::now());
    }

    /// Whether calibration achieved the configured threshold.
    #[inline]
    #[must_use]
    pub fn is_accurate(&self) -> bool {
        self.accurate
    }

    /// Best measurement gap achieved during calibration.
    #[inline]
    #[must_use]
    pub fn calibration_gap(&self) -> Duration {
        self.calibration_gap
    }

    fn resync_at(&mut self, now: Instant) {
        let (best_instant, base_nanos, gap) = Self::calibrate(self.threshold, self.max_retries);
        let adjustment = now.saturating_duration_since(best_instant);
        self.base_instant = now;
        self.base_nanos = base_nanos + adjustment.as_nanos() as i128;
        self.calibration_gap = gap;
        self.accurate = gap <= self.threshold;
        self.last_resync = now;
    }

    fn calibrate(threshold: Duration, max_retries: u32) -> (Instant, i128, Duration) {
        let mut best_gap = Duration::MAX;
        let mut best_instant = Instant::now();
        let mut best_nanos = 0i128;

        for _ in 0..max_retries {
            let before = Instant::now();
            let wall = SystemTime::now();
            let after = Instant::now();

            let gap = after.duration_since(before);
            if gap < best_gap {
                best_gap = gap;
                best_instant = before + gap / 2;
                best_nanos = match wall.duration_since(UNIX_EPOCH) {
                    Ok(d) => d.as_nanos() as i128,
                    Err(e) => -(e.duration().as_nanos() as i128),
                };
            }

            if gap <= threshold {
                break;
            }
        }

        (best_instant, best_nanos, best_gap)
    }
}

impl std::fmt::Debug for RealtimeClockPoller {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RealtimeClockPoller")
            .field("calibration_gap", &self.calibration_gap)
            .field("accurate", &self.accurate)
            .finish()
    }
}

// -- Builder --

impl RealtimeClockInstallerBuilder {
    /// Target accuracy threshold. Clamped to platform minimum.
    #[must_use]
    pub fn threshold(mut self, threshold: Duration) -> Self {
        self.threshold = threshold.max(MIN_THRESHOLD);
        self
    }

    /// Maximum calibration attempts. Default: 20.
    #[must_use]
    pub fn max_retries(mut self, n: u32) -> Self {
        self.max_retries = n;
        self
    }

    /// Resync interval. Default: 1 hour.
    #[must_use]
    pub fn resync_interval(mut self, interval: Duration) -> Self {
        self.resync_interval = interval;
        self
    }

    /// Builds the installer.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `max_retries` is 0.
    pub fn build(self) -> Result<RealtimeClockInstaller, ConfigError> {
        if self.max_retries == 0 {
            return Err(ConfigError::Invalid("max_retries must be > 0"));
        }
        Ok(RealtimeClockInstaller {
            threshold: self.threshold,
            max_retries: self.max_retries,
            resync_interval: self.resync_interval,
        })
    }
}

impl Default for RealtimeClockInstallerBuilder {
    fn default() -> Self {
        Self {
            threshold: DEFAULT_THRESHOLD,
            max_retries: 20,
            resync_interval: Duration::from_secs(3600),
        }
    }
}

// =============================================================================
// TestClock — installer + poller
// =============================================================================

/// Installer for the test clock.
///
/// Registers a [`Clock`] resource and returns a [`TestClockPoller`].
#[derive(Debug)]
pub struct TestClockInstaller {
    base_nanos: i128,
}

impl TestClockInstaller {
    /// Creates an installer starting at epoch (nanos = 0).
    #[must_use]
    pub fn new() -> Self {
        Self { base_nanos: 0 }
    }

    /// Creates an installer starting at the given UTC nanos.
    #[must_use]
    pub fn starting_at(nanos: i128) -> Self {
        Self { base_nanos: nanos }
    }
}

impl Default for TestClockInstaller {
    fn default() -> Self {
        Self::new()
    }
}

impl Installer for TestClockInstaller {
    type Poller = TestClockPoller;

    fn install(self, world: &mut WorldBuilder) -> TestClockPoller {
        // `Clock` is a shared dependency (handlers read it via `Res<Clock>`); the
        // installer owns the value it writes each `sync()`, not the slot. `ensure`
        // rather than `register` so a clock source composes even if something else
        // already registered a `Clock` — see the `Installer` trait docs.
        let clock_id = world.ensure_default::<Clock>();
        TestClockPoller {
            clock_id,
            elapsed: Duration::ZERO,
            base_nanos: self.base_nanos,
            base_instant: Instant::now(),
        }
    }
}

/// Runtime poller for the test clock — manually controlled.
///
/// Use `advance()` to move time forward, then `sync()` to write into
/// the `Clock` resource.
pub struct TestClockPoller {
    clock_id: ResourceId,
    elapsed: Duration,
    base_nanos: i128,
    base_instant: Instant,
}

impl TestClockPoller {
    /// Sync the Clock resource with the test clock's current state.
    ///
    /// Returns the [`Clock`] it just wrote (it's `Copy`), matching the other
    /// pollers — no `world.resource::<Clock>()` round-trip needed. Ignoring the
    /// return is fine.
    #[inline]
    pub fn sync(&self, world: &mut World) -> Clock {
        // SAFETY: clock_id was obtained via ensure_default() during install()
        // and points at the registered Clock.
        let clock = unsafe { world.get_mut::<Clock>(self.clock_id) };
        clock.instant = self.base_instant + self.elapsed;
        clock.unix_nanos = self.base_nanos + self.elapsed.as_nanos() as i128;
        *clock
    }

    /// Advances time by the given duration.
    #[inline]
    pub fn advance(&mut self, duration: Duration) {
        self.elapsed += duration;
    }

    /// Sets the elapsed time to an exact value.
    #[inline]
    pub fn set_elapsed(&mut self, elapsed: Duration) {
        self.elapsed = elapsed;
    }

    /// Sets the UTC nanos directly (resets elapsed to zero).
    #[inline]
    pub fn set_nanos(&mut self, nanos: i128) {
        self.base_nanos = nanos;
        self.elapsed = Duration::ZERO;
    }

    /// Returns the current elapsed duration.
    #[inline]
    #[must_use]
    pub fn elapsed(&self) -> Duration {
        self.elapsed
    }

    /// Resets to zero elapsed, keeping the base nanos.
    #[inline]
    pub fn reset(&mut self) {
        self.elapsed = Duration::ZERO;
    }
}

impl std::fmt::Debug for TestClockPoller {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TestClockPoller")
            .field("elapsed", &self.elapsed)
            .field("base_nanos", &self.base_nanos)
            .finish()
    }
}

// =============================================================================
// HistoricalClock — installer + poller
// =============================================================================

/// Installer for the historical (replay) clock.
///
/// Registers a [`Clock`] resource and returns a [`HistoricalClockPoller`].
pub struct HistoricalClockInstaller {
    start_nanos: i128,
    end_nanos: i128,
    step: Duration,
}

impl HistoricalClockInstaller {
    /// Creates an installer for replay.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `start_nanos >= end_nanos` or
    /// `step` is zero.
    pub fn new(start_nanos: i128, end_nanos: i128, step: Duration) -> Result<Self, ConfigError> {
        if start_nanos >= end_nanos {
            return Err(ConfigError::Invalid("start_nanos must be < end_nanos"));
        }
        if step.is_zero() {
            return Err(ConfigError::Invalid("step must be > 0"));
        }
        Ok(Self {
            start_nanos,
            end_nanos,
            step,
        })
    }
}

impl std::fmt::Debug for HistoricalClockInstaller {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HistoricalClockInstaller")
            .field("start_nanos", &self.start_nanos)
            .field("end_nanos", &self.end_nanos)
            .field("step", &self.step)
            .finish()
    }
}

impl Installer for HistoricalClockInstaller {
    type Poller = HistoricalClockPoller;

    fn install(self, world: &mut WorldBuilder) -> HistoricalClockPoller {
        // `Clock` is a shared dependency (handlers read it via `Res<Clock>`); the
        // installer owns the value it writes each `sync()`, not the slot. `ensure`
        // rather than `register` so a clock source composes even if something else
        // already registered a `Clock` — see the `Installer` trait docs.
        let clock_id = world.ensure_default::<Clock>();
        HistoricalClockPoller {
            clock_id,
            start_nanos: self.start_nanos,
            end_nanos: self.end_nanos,
            current_nanos: self.start_nanos,
            step_nanos: self.step.as_nanos() as i128,
            base_instant: Instant::now(),
            exhausted: false,
        }
    }
}

/// Runtime poller for historical (replay) clock — auto-advances per sync.
pub struct HistoricalClockPoller {
    clock_id: ResourceId,
    start_nanos: i128,
    end_nanos: i128,
    current_nanos: i128,
    step_nanos: i128,
    base_instant: Instant,
    exhausted: bool,
}

impl HistoricalClockPoller {
    /// Sync the Clock resource and auto-advance the replay position.
    ///
    /// Writes current position into Clock, then advances by one step. Returns
    /// the [`Clock`] it wrote — the replay position *before* the advance, i.e.
    /// the timestamp now visible via `Res<Clock>` this iteration. Ignoring the
    /// return is fine.
    #[inline]
    pub fn sync(&mut self, world: &mut World) -> Clock {
        let elapsed = (self.current_nanos - self.start_nanos).max(0);
        let elapsed_nanos = u64::try_from(elapsed).unwrap_or(u64::MAX);

        // SAFETY: clock_id was obtained via ensure_default() during install()
        // and points at the registered Clock.
        let clock = unsafe { world.get_mut::<Clock>(self.clock_id) };
        clock.instant = self.base_instant + Duration::from_nanos(elapsed_nanos);
        clock.unix_nanos = self.current_nanos;
        let synced = *clock;

        if !self.exhausted {
            self.current_nanos += self.step_nanos;
            if self.current_nanos >= self.end_nanos {
                self.current_nanos = self.end_nanos;
                self.exhausted = true;
            }
        }

        synced
    }

    /// Whether the replay has reached `end_nanos`.
    #[inline]
    #[must_use]
    pub fn is_exhausted(&self) -> bool {
        self.exhausted
    }

    /// Current replay position in UTC nanos.
    #[inline]
    #[must_use]
    pub fn current_nanos(&self) -> i128 {
        self.current_nanos
    }

    /// Resets to start position.
    #[inline]
    pub fn reset(&mut self) {
        self.current_nanos = self.start_nanos;
        self.exhausted = false;
    }
}

impl std::fmt::Debug for HistoricalClockPoller {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HistoricalClockPoller")
            .field("current_nanos", &self.current_nanos)
            .field("exhausted", &self.exhausted)
            .finish()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // Clock struct
    // =========================================================================

    #[test]
    fn clock_default() {
        let clock = Clock::default();
        assert_eq!(clock.unix_nanos(), 0);
    }

    // =========================================================================
    // RealtimeClock
    // =========================================================================

    #[test]
    fn realtime_install_and_sync() {
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(RealtimeClockInstaller::default());
        let mut world = wb.build();

        let now = Instant::now();
        poller.sync(&mut world, now);

        let clock = world.resource::<Clock>();
        assert_eq!(clock.instant(), now);

        let expected = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos() as i128;
        let diff = (clock.unix_nanos() - expected).unsigned_abs();
        assert!(diff < 1_000_000_000, "nanos off by {diff}ns");
    }

    #[test]
    fn realtime_nanos_increase() {
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(RealtimeClockInstaller::default());
        let mut world = wb.build();

        poller.sync(&mut world, Instant::now());
        let n1 = world.resource::<Clock>().unix_nanos();

        std::thread::sleep(Duration::from_millis(1));
        poller.sync(&mut world, Instant::now());
        let n2 = world.resource::<Clock>().unix_nanos();

        assert!(n2 > n1);
    }

    #[test]
    fn realtime_resync_no_panic() {
        let mut wb = WorldBuilder::new();
        let installer = RealtimeClockInstaller::builder()
            .resync_interval(Duration::ZERO)
            .build()
            .unwrap();
        let mut poller = wb.install_driver(installer);
        let mut world = wb.build();

        poller.sync(&mut world, Instant::now());
        assert!(world.resource::<Clock>().unix_nanos() > 0);
    }

    #[test]
    fn realtime_zero_retries_rejected() {
        let result = RealtimeClockInstaller::builder().max_retries(0).build();
        assert!(matches!(result, Err(ConfigError::Invalid(_))));
    }

    // =========================================================================
    // TestClock
    // =========================================================================

    #[test]
    fn test_clock_install_and_sync() {
        let mut wb = WorldBuilder::new();
        let poller = wb.install_driver(TestClockInstaller::new());
        let mut world = wb.build();

        poller.sync(&mut world);
        assert_eq!(world.resource::<Clock>().unix_nanos(), 0);
    }

    #[test]
    fn test_clock_advance() {
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(TestClockInstaller::new());
        let mut world = wb.build();

        poller.advance(Duration::from_millis(100));
        poller.sync(&mut world);
        assert_eq!(world.resource::<Clock>().unix_nanos(), 100_000_000);
    }

    #[test]
    fn test_clock_starting_at() {
        let mut wb = WorldBuilder::new();
        let poller = wb.install_driver(TestClockInstaller::starting_at(1_000_000_000));
        let mut world = wb.build();

        poller.sync(&mut world);
        assert_eq!(world.resource::<Clock>().unix_nanos(), 1_000_000_000);
    }

    #[test]
    fn test_clock_set_nanos() {
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(TestClockInstaller::new());
        let mut world = wb.build();

        poller.set_nanos(42);
        poller.sync(&mut world);
        assert_eq!(world.resource::<Clock>().unix_nanos(), 42);
    }

    #[test]
    fn test_clock_reset() {
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(TestClockInstaller::new());
        let mut world = wb.build();

        poller.advance(Duration::from_secs(10));
        poller.reset();
        poller.sync(&mut world);
        assert_eq!(world.resource::<Clock>().unix_nanos(), 0);
    }

    #[test]
    fn test_clock_instant_advances() {
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(TestClockInstaller::new());
        let mut world = wb.build();

        poller.sync(&mut world);
        let i1 = world.resource::<Clock>().instant();

        poller.advance(Duration::from_millis(100));
        poller.sync(&mut world);
        let i2 = world.resource::<Clock>().instant();

        assert_eq!(i2.duration_since(i1), Duration::from_millis(100));
    }

    // =========================================================================
    // HistoricalClock
    // =========================================================================

    #[test]
    fn historical_install_and_sync() {
        let installer =
            HistoricalClockInstaller::new(1000, 2000, Duration::from_nanos(100)).unwrap();
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(installer);
        let mut world = wb.build();

        poller.sync(&mut world);
        assert_eq!(world.resource::<Clock>().unix_nanos(), 1000); // writes before advancing
        assert_eq!(poller.current_nanos(), 1100); // advanced after sync
    }

    #[test]
    fn historical_exhausts() {
        let installer = HistoricalClockInstaller::new(0, 200, Duration::from_nanos(100)).unwrap();
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(installer);
        let mut world = wb.build();

        poller.sync(&mut world); // writes 0, advances to 100
        poller.sync(&mut world); // writes 100, advances to 200 → exhausted

        assert!(poller.is_exhausted());
        poller.sync(&mut world); // writes 200, no further advance
        assert_eq!(world.resource::<Clock>().unix_nanos(), 200);
    }

    #[test]
    fn historical_reset() {
        let installer = HistoricalClockInstaller::new(100, 500, Duration::from_nanos(100)).unwrap();
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(installer);
        let mut world = wb.build();

        for _ in 0..10 {
            poller.sync(&mut world);
        }
        assert!(poller.is_exhausted());

        poller.reset();
        assert!(!poller.is_exhausted());
        assert_eq!(poller.current_nanos(), 100);
    }

    #[test]
    fn historical_rejects_bad_config() {
        assert!(HistoricalClockInstaller::new(1000, 1000, Duration::from_nanos(100)).is_err());
        assert!(HistoricalClockInstaller::new(2000, 1000, Duration::from_nanos(100)).is_err());
        assert!(HistoricalClockInstaller::new(0, 1000, Duration::ZERO).is_err());
    }

    // =========================================================================
    // sync() returns the Clock it wrote (#631)
    // =========================================================================

    #[test]
    fn sync_returns_the_written_clock() {
        // Realtime: the returned Clock matches what landed in the World.
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(RealtimeClockInstaller::default());
        let mut world = wb.build();
        let returned = poller.sync(&mut world, Instant::now());
        let in_world = world.resource::<Clock>();
        assert_eq!(returned.unix_nanos(), in_world.unix_nanos());
        assert_eq!(returned.instant(), in_world.instant());

        // Test clock.
        let mut wb = WorldBuilder::new();
        let poller = wb.install_driver(TestClockInstaller::new());
        let mut world = wb.build();
        let returned = poller.sync(&mut world);
        assert_eq!(
            returned.unix_nanos(),
            world.resource::<Clock>().unix_nanos()
        );

        // Historical: returns the pre-advance position (what `Res<Clock>` sees
        // this iteration), not the advanced cursor.
        let installer =
            HistoricalClockInstaller::new(1000, 2000, Duration::from_nanos(100)).unwrap();
        let mut wb = WorldBuilder::new();
        let mut poller = wb.install_driver(installer);
        let mut world = wb.build();
        let returned = poller.sync(&mut world);
        assert_eq!(returned.unix_nanos(), 1000);
        assert_eq!(
            returned.unix_nanos(),
            world.resource::<Clock>().unix_nanos()
        );
        assert_eq!(poller.current_nanos(), 1100); // cursor advanced, return did not
    }
}
