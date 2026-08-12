//! Timer driver for nexus-rt.
//!
//! Integrates [`nexus_timer::Wheel`] as a driver following the
//! [`Installer`]/[`Plugin`](crate::Plugin) pattern. Handlers access the
//! timer wheel directly via `ResMut<Wheel<S>>` during dispatch — no
//! command queues, no side-channel communication.
//!
//! # Architecture
//!
//! - [`TimerInstaller`] is the installer — consumed at setup, registers the
//!   wheel into [`WorldBuilder`] and returns a [`TimerPoller`].
//! - [`TimerPoller`] is the poll-time handle. `poll(world, now)` drains
//!   expired timers and fires their handlers.
//! - Handlers reschedule themselves directly via `ResMut<Wheel<S>>`.
//!
//! # Timing
//!
//! The timer wheel records an **epoch** (`Instant`) at construction time
//! (inside [`TimerInstaller::install`]). All deadlines are converted to
//! integer ticks relative to this epoch:
//!
//! ```text
//! ticks = (deadline - epoch).as_nanos() / tick_ns
//! ```
//!
//! - **Default tick resolution**: 1ms (configurable via [`WheelBuilder::tick_duration`]).
//! - **Instants before the epoch** saturate to tick 0 (fire immediately).
//! - **Instants beyond the wheel's range** are clamped to the highest
//!   level's last slot (they fire eventually, not exactly on time).
//! - **Deadlines in the past** at poll time fire immediately — no "missed
//!   timer" error.
//!
//! The epoch is captured as `Instant::now()` during `install()`. This
//! means the wheel's zero point is the moment the driver is installed,
//! which is fine for monotonic deadlines derived from the same clock.
//!
//! # Examples
//!
//! ```ignore
//! use std::time::{Duration, Instant};
//! use nexus_rt::{WorldBuilder, ResMut, IntoHandler, Handler, WheelBuilder};
//! use nexus_rt::timer::{TimerInstaller, TimerPoller, TimerWheel};
//!
//! fn on_timeout(mut state: ResMut<bool>, _poll_time: Instant) {
//!     *state = true;
//! }
//!
//! let mut builder = WorldBuilder::new();
//! builder.register::<bool>(false);
//! let wheel = WheelBuilder::default().unbounded(64).build(Instant::now()).unwrap();
//! let mut timer: TimerPoller = builder.install_driver(
//!     TimerInstaller::new(wheel),
//! );
//! let mut world = builder.build();
//!
//! // Schedule a one-shot timer
//! let handler = on_timeout.into_handler(world.registry());
//! world.resource_mut::<TimerWheel>().schedule_forget(
//!     Instant::now() + Duration::from_millis(100),
//!     Box::new(handler),
//! );
//!
//! // In the poll loop:
//! // timer.poll(&mut world, Instant::now());
//! ```

use std::marker::PhantomData;
use std::ops::DerefMut;
use std::time::{Duration, Instant};

use nexus_timer::store::SlabStore;

// Re-export types that users need from nexus-timer
pub use nexus_timer::{
    BoundedWheel, BoundedWheelBuilder, ConfigError, Full, TimerHandle, UnboundedWheelBuilder,
    Wheel, WheelBuilder, WheelEntry,
};

// Resource impls for timer wheel types registered by the timer driver.
// TimerWheel has its own `unsafe impl Send` (the wheel owns the slab
// exclusively, no RawSlots escape). We don't require S: Send here —
// the wheel's Send impl handles it.
impl<T: Send + 'static, S: nexus_timer::store::SlabStore<Item = WheelEntry<T>> + 'static>
    crate::world::Resource for nexus_timer::TimerWheel<T, S>
{
}

use crate::Handler;
use crate::driver::Installer;
use crate::world::{ResourceId, World, WorldBuilder};

/// Type alias for a timer wheel using boxed handlers (heap-allocated).
///
/// `Box<dyn Handler<Instant>>` — each timer entry is a type-erased handler
/// that receives the poll timestamp as its event.
pub type TimerWheel = Wheel<Box<dyn Handler<Instant>>>;

/// Type alias for a bounded timer wheel using boxed handlers (heap-allocated).
///
/// Fixed-capacity — `try_schedule` returns `Err(Full)` when the wheel is full.
pub type BoundedTimerWheel = BoundedWheel<Box<dyn Handler<Instant>>>;

/// Type alias for a timer wheel using inline handler storage.
///
/// B256 = 256-byte inline buffer. Panics if a handler doesn't fit.
/// Realistic timer callbacks (0-2 resources + context) are 24-96 bytes
/// (ResourceId is pointer-sized: 8 bytes per resource param, plus 16
/// bytes base overhead, plus context size). B256 provides comfortable
/// headroom without a cache-line penalty over B128 (SIMD memcpy).
#[cfg(feature = "smartptr")]
pub type InlineTimerWheel = Wheel<crate::FlatVirtual<Instant, nexus_smartptr::B256>>;

/// Type alias for a timer wheel using inline storage with heap fallback.
#[cfg(feature = "smartptr")]
pub type FlexTimerWheel = Wheel<crate::FlexVirtual<Instant, nexus_smartptr::B256>>;

/// Type alias for a bounded timer wheel using inline handler storage.
#[cfg(feature = "smartptr")]
pub type BoundedInlineTimerWheel = BoundedWheel<crate::FlatVirtual<Instant, nexus_smartptr::B256>>;

/// Type alias for a bounded timer wheel using inline storage with heap fallback.
#[cfg(feature = "smartptr")]
pub type BoundedFlexTimerWheel = BoundedWheel<crate::FlexVirtual<Instant, nexus_smartptr::B256>>;

/// Configuration trait for generic timer code.
///
/// ZST annotation type that bundles the handler storage type with a
/// wrapping function. Library code parameterized over `C: TimerConfig`
/// can schedule, cancel, and wrap handlers without knowing the concrete
/// storage strategy.
///
/// # Example
///
/// ```ignore
/// use std::time::Instant;
/// use nexus_rt::timer::{BoxedTimers, TimerConfig};
/// use nexus_rt::{Handler, World};
/// use nexus_timer::Wheel;
///
/// fn schedule_heartbeat<C: TimerConfig>(
///     world: &mut World,
///     handler: impl Handler<Instant> + 'static,
///     deadline: Instant,
/// ) {
///     world.resource_mut::<Wheel<C::Storage>>()
///         .schedule_forget(deadline, C::wrap(handler));
/// }
/// ```
pub trait TimerConfig: Send + 'static {
    /// The handler storage type (e.g. `Box<dyn Handler<Instant>>`).
    type Storage: DerefMut<Target = dyn Handler<Instant>> + Send + 'static;

    /// Wrap a concrete handler into the storage type.
    fn wrap(handler: impl Handler<Instant> + 'static) -> Self::Storage;
}

/// Boxed timer configuration — heap-allocates each handler.
///
/// This is the default and most flexible option. Zero-overhead for
/// `Option<Box<T>>` due to niche optimization.
pub struct BoxedTimers;

impl TimerConfig for BoxedTimers {
    type Storage = Box<dyn Handler<Instant>>;

    fn wrap(handler: impl Handler<Instant> + 'static) -> Self::Storage {
        Box::new(handler)
    }
}

/// Inline timer configuration — stores handlers in a fixed-size buffer.
///
/// Panics if a handler exceeds the buffer size (256 bytes).
/// Realistic timer callbacks (0-2 resources + context) are 24-96 bytes.
#[cfg(feature = "smartptr")]
pub struct InlineTimers;

#[cfg(feature = "smartptr")]
impl TimerConfig for InlineTimers {
    type Storage = crate::FlatVirtual<Instant, nexus_smartptr::B256>;

    fn wrap(handler: impl Handler<Instant> + 'static) -> Self::Storage {
        let ptr: *const dyn Handler<Instant> = &handler;
        // SAFETY: ptr's metadata (vtable) corresponds to handler's concrete type.
        unsafe { nexus_smartptr::Flat::new_raw(handler, ptr) }
    }
}

/// Flex timer configuration — inline with heap fallback.
///
/// Stores inline if the handler fits in 256 bytes, otherwise
/// heap-allocates. No panics.
#[cfg(feature = "smartptr")]
pub struct FlexTimers;

#[cfg(feature = "smartptr")]
impl TimerConfig for FlexTimers {
    type Storage = crate::FlexVirtual<Instant, nexus_smartptr::B256>;

    fn wrap(handler: impl Handler<Instant> + 'static) -> Self::Storage {
        let ptr: *const dyn Handler<Instant> = &handler;
        // SAFETY: ptr's metadata (vtable) corresponds to handler's concrete type.
        unsafe { nexus_smartptr::Flex::new_raw(handler, ptr) }
    }
}

/// Timer driver installer — takes a pre-built [`TimerWheel`](nexus_timer::TimerWheel).
///
/// Build the wheel via [`WheelBuilder`], then hand it to the installer.
/// The installer registers it into the [`World`] and returns a
/// [`TimerPoller`] for poll-time use.
///
/// # Examples
///
/// ```ignore
/// use std::time::{Duration, Instant};
/// use nexus_rt::{TimerInstaller, TimerPoller, BoundedTimerPoller, WheelBuilder};
///
/// // Unbounded — slab grows as needed, scheduling never fails
/// let wheel = WheelBuilder::default().unbounded(64).build(Instant::now()).unwrap();
/// let timer: TimerPoller = wb.install_driver(TimerInstaller::new(wheel));
///
/// // Bounded — fixed capacity, try_schedule returns Err(Full) when full
/// let wheel = WheelBuilder::default().bounded(1024).build(Instant::now()).unwrap();
/// let timer: BoundedTimerPoller = wb.install_driver(TimerInstaller::new(wheel));
///
/// // Custom tick resolution for microsecond-precision timers
/// let wheel = WheelBuilder::default()
///     .tick_duration(Duration::from_micros(100))
///     .unbounded(256)
///     .build(Instant::now())
///     .unwrap();
/// let timer: TimerPoller = wb.install_driver(TimerInstaller::new(wheel));
/// ```
pub struct TimerInstaller<
    S: 'static = Box<dyn Handler<Instant>>,
    Store: SlabStore<Item = WheelEntry<S>> = nexus_timer::store::UnboundedSlab<WheelEntry<S>>,
> {
    wheel: nexus_timer::TimerWheel<S, Store>,
}

impl<S: 'static, Store: SlabStore<Item = WheelEntry<S>>> TimerInstaller<S, Store> {
    /// Creates a timer installer from a pre-built wheel.
    ///
    /// Build the wheel via [`WheelBuilder`], then pass it here.
    pub fn new(wheel: nexus_timer::TimerWheel<S, Store>) -> Self {
        TimerInstaller { wheel }
    }
}

impl<S, Store> Installer for TimerInstaller<S, Store>
where
    S: Send + 'static,
    Store: SlabStore<Item = WheelEntry<S>> + 'static,
{
    type Poller = TimerPoller<S, Store>;

    fn install(self, world: &mut WorldBuilder) -> TimerPoller<S, Store> {
        let wheel_id = world.register(self.wheel);
        TimerPoller {
            wheel_id,
            buf: Vec::new(),
            _marker: PhantomData,
        }
    }
}

/// Type alias for a bounded timer installer.
pub type BoundedTimerInstaller<S = Box<dyn Handler<Instant>>> =
    TimerInstaller<S, nexus_timer::store::BoundedSlab<WheelEntry<S>>>;

/// Timer driver poller — generic over handler storage and slab store.
///
/// Returned by [`TimerInstaller::install`]. Holds a pre-resolved
/// [`ResourceId`] for the wheel and a reusable drain buffer.
///
/// `Store` is the slab backend — determines which [`TimerWheel<S, Store>`]
/// resource to look up in the [`World`]. Defaults to the unbounded slab.
pub struct TimerPoller<
    S = Box<dyn Handler<Instant>>,
    Store = nexus_timer::store::UnboundedSlab<WheelEntry<S>>,
> {
    wheel_id: ResourceId,
    buf: Vec<S>,
    _marker: PhantomData<fn() -> Store>,
}

/// Type alias for a bounded timer poller.
pub type BoundedTimerPoller<S = Box<dyn Handler<Instant>>> =
    TimerPoller<S, nexus_timer::store::BoundedSlab<WheelEntry<S>>>;

impl<S, Store> std::fmt::Debug for TimerPoller<S, Store> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TimerPoller")
            .field("wheel_id", &self.wheel_id)
            .field("buf_len", &self.buf.len())
            .finish()
    }
}

impl<S, Store> TimerPoller<S, Store>
where
    S: DerefMut + Send + 'static,
    S::Target: Handler<Instant>,
    Store: SlabStore<Item = WheelEntry<S>> + 'static,
{
    /// Poll expired timers — drain from wheel, fire each handler, done.
    ///
    /// Each handler receives `now` as its event. Handlers that need to
    /// reschedule themselves do so directly via the wheel resource.
    ///
    /// Returns the number of timers fired.
    pub fn poll(&mut self, world: &mut World, now: Instant) -> usize {
        // SAFETY: wheel_id was produced by install() on the same builder.
        // Type matches TimerWheel<S, Store>. No aliases — we have &mut World.
        let wheel = unsafe { world.get_mut::<nexus_timer::TimerWheel<S, Store>>(self.wheel_id) };
        wheel.poll(now, &mut self.buf);
        let fired = self.buf.len();

        for mut handler in self.buf.drain(..) {
            world.next_sequence();
            handler.deref_mut().run(world, now);
        }

        fired
    }

    /// Earliest deadline in the wheel.
    pub fn next_deadline(&self, world: &World) -> Option<Instant> {
        // SAFETY: wheel_id from install(). Type matches. &World = shared access.
        let wheel = unsafe { world.get::<nexus_timer::TimerWheel<S, Store>>(self.wheel_id) };
        wheel.next_deadline()
    }

    /// Number of active timers.
    pub fn len(&self, world: &World) -> usize {
        // SAFETY: wheel_id from install(). Type matches. &World = shared access.
        let wheel = unsafe { world.get::<nexus_timer::TimerWheel<S, Store>>(self.wheel_id) };
        wheel.len()
    }

    /// Whether the wheel is empty.
    pub fn is_empty(&self, world: &World) -> bool {
        // SAFETY: wheel_id from install(). Type matches. &World = shared access.
        let wheel = unsafe { world.get::<nexus_timer::TimerWheel<S, Store>>(self.wheel_id) };
        wheel.is_empty()
    }
}

// =============================================================================
// Periodic
// =============================================================================

/// Periodic timer wrapper — automatically reschedules after each firing.
///
/// Generic over the concrete handler type `H` — no nesting, no type erasure
/// overhead. When stored in a wheel, the `Periodic<H, C, Store>` is wrapped
/// in `C::Storage` (e.g. `Box<dyn Handler<Instant>>`) once at the outermost
/// level. The inner handler `H` is stored directly, not wrapped.
///
/// This means `Periodic<H>` is `size_of::<H>() + size_of::<Duration>()` plus
/// a small marker — compact enough to fit in inline storage (`FlatVirtual`)
/// alongside typical handlers.
///
/// # Scheduling
///
/// [`schedule_forget`](nexus_timer::TimerWheel::schedule_forget) is used for
/// rescheduling. On bounded wheels, this panics if the slab is at capacity.
/// This is a capacity planning error — size your wheel for peak concurrent
/// timers including periodic overhead. See the [`store`](nexus_timer::store)
/// module documentation for the OOM-as-panic rationale.
///
/// # Cancellation
///
/// If the periodic timer is cancelled (via [`cancel`](nexus_timer::TimerWheel::cancel))
/// or dropped during shutdown, the inner handler is dropped normally — no leak.
///
/// # Example
///
/// ```ignore
/// use std::time::{Duration, Instant};
/// use nexus_rt::{IntoHandler, ResMut};
/// use nexus_rt::timer::{Periodic, TimerWheel};
///
/// fn heartbeat(mut counter: ResMut<u64>, _now: Instant) {
///     *counter += 1;
/// }
///
/// let handler = heartbeat.into_handler(world.registry());
/// let periodic = Periodic::new(handler, Duration::from_millis(100));
/// world.resource_mut::<TimerWheel>()
///     .schedule_forget(Instant::now(), Box::new(periodic));
/// ```
pub struct Periodic<
    H,
    C: TimerConfig = BoxedTimers,
    Store: SlabStore<Item = WheelEntry<C::Storage>> = nexus_timer::store::UnboundedSlab<
        WheelEntry<Box<dyn Handler<Instant>>>,
    >,
> {
    inner: Option<H>,
    interval: Duration,
    #[allow(clippy::type_complexity)]
    _marker: PhantomData<(fn() -> C, fn() -> Store)>,
}

impl<H, C: TimerConfig, Store: SlabStore<Item = WheelEntry<C::Storage>>> std::fmt::Debug
    for Periodic<H, C, Store>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Periodic")
            .field("has_inner", &self.inner.is_some())
            .field("interval", &self.interval)
            .finish()
    }
}

impl<H, C: TimerConfig, Store: SlabStore<Item = WheelEntry<C::Storage>>> Periodic<H, C, Store> {
    /// Create a periodic wrapper around a handler.
    ///
    /// `C` and `Store` determine how the handler is stored in the wheel
    /// and which wheel resource to look up on reschedule. Defaults are
    /// `BoxedTimers` + `UnboundedSlab` — override via type annotation or
    /// turbofish for inline/bounded configurations.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Boxed + unbounded (defaults)
    /// let p = Periodic::new(handler, Duration::from_millis(100));
    ///
    /// // Inline + unbounded (Store must be specified when C changes)
    /// use nexus_timer::store::UnboundedSlab;
    /// let p: Periodic<_, InlineTimers, UnboundedSlab<_>> =
    ///     Periodic::new(handler, Duration::from_millis(100));
    /// ```
    pub fn new(handler: H, interval: Duration) -> Self {
        Periodic {
            inner: Some(handler),
            interval,
            _marker: PhantomData,
        }
    }

    /// Returns the repetition interval.
    pub fn interval(&self) -> Duration {
        self.interval
    }

    /// Unwrap the inner handler, if present.
    ///
    /// Returns `None` only during the transient state inside
    /// `Handler::run` (after fire, before reschedule).
    pub fn into_inner(self) -> Option<H> {
        self.inner
    }
}

impl<H, C, Store> Handler<Instant> for Periodic<H, C, Store>
where
    H: Handler<Instant> + 'static,
    C: TimerConfig,
    Store: SlabStore<Item = WheelEntry<C::Storage>> + 'static,
{
    fn run(&mut self, world: &mut World, now: Instant) {
        let mut inner = self
            .inner
            .take()
            .expect("periodic handler already consumed");

        // Fire the inner handler.
        inner.run(world, now);

        // Reconstruct and reschedule. The new Periodic<H, C, Store> is
        // wrapped in C::Storage and placed back into the wheel. No nesting —
        // H is the concrete handler, not C::Storage.
        let next: Periodic<H, C, Store> = Periodic {
            inner: Some(inner),
            interval: self.interval,
            _marker: PhantomData,
        };
        let deadline = now + self.interval;
        let wheel = world.resource_mut::<nexus_timer::TimerWheel<C::Storage, Store>>();
        wheel.schedule_forget(deadline, C::wrap(next));
    }

    fn name(&self) -> &'static str {
        self.inner
            .as_ref()
            .map_or("<periodic:consumed>", |inner| inner.name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{IntoCallback, IntoHandler, RegistryRef, ResMut, WorldBuilder};
    use std::time::Duration;

    #[test]
    fn install_registers_wheel() {
        let mut builder = WorldBuilder::new();
        let _handle: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let world = builder.build();
        assert!(world.contains::<TimerWheel>());
    }

    #[test]
    fn poll_empty_returns_zero() {
        let mut builder = WorldBuilder::new();
        let mut handle: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();
        assert_eq!(handle.poll(&mut world, Instant::now()), 0);
    }

    #[test]
    fn one_shot_fires() {
        let mut builder = WorldBuilder::new();
        builder.register::<bool>(false);
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        fn on_timeout(mut flag: ResMut<bool>, _now: Instant) {
            *flag = true;
        }

        let handler = on_timeout.into_handler(world.registry());
        let now = Instant::now();
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(now, Box::new(handler));

        assert!(!*world.resource::<bool>());
        let fired = timer.poll(&mut world, now);
        assert_eq!(fired, 1);
        assert!(*world.resource::<bool>());
    }

    #[test]
    fn expired_timer_fires_accumulated() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        fn inc(mut counter: ResMut<u64>, _now: Instant) {
            *counter += 1;
        }

        let now = Instant::now();
        let past = now.checked_sub(Duration::from_millis(10)).unwrap();

        for _ in 0..3 {
            let h = inc.into_handler(world.registry());
            world
                .resource_mut::<TimerWheel>()
                .schedule_forget(past, Box::new(h));
        }

        let fired = timer.poll(&mut world, now);
        assert_eq!(fired, 3);
        assert_eq!(*world.resource::<u64>(), 3);
    }

    #[test]
    fn future_timer_does_not_fire() {
        let mut builder = WorldBuilder::new();
        builder.register::<bool>(false);
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        fn on_timeout(mut flag: ResMut<bool>, _now: Instant) {
            *flag = true;
        }

        let now = Instant::now();
        let future = now + Duration::from_secs(60);
        let h = on_timeout.into_handler(world.registry());
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(future, Box::new(h));

        let fired = timer.poll(&mut world, now);
        assert_eq!(fired, 0);
        assert!(!*world.resource::<bool>());
    }

    #[test]
    fn next_deadline_reports_earliest() {
        let mut builder = WorldBuilder::new();
        let timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        let now = Instant::now();
        let early = now + Duration::from_millis(50);
        let late = now + Duration::from_millis(200);

        fn noop(_now: Instant) {}

        let h1 = noop.into_handler(world.registry());
        let h2 = noop.into_handler(world.registry());
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(late, Box::new(h1));
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(early, Box::new(h2));

        let deadline = timer.next_deadline(&world);
        assert!(deadline.is_some());
        // Deadline should be <= early (timer wheel rounds to tick granularity)
        assert!(deadline.unwrap() <= early + Duration::from_millis(1));
    }

    #[test]
    fn len_tracks_active_timers() {
        let mut builder = WorldBuilder::new();
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        assert_eq!(timer.len(&world), 0);
        assert!(timer.is_empty(&world));

        let now = Instant::now();
        fn noop(_now: Instant) {}

        let h = noop.into_handler(world.registry());
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(now, Box::new(h));

        assert_eq!(timer.len(&world), 1);
        assert!(!timer.is_empty(&world));

        timer.poll(&mut world, now);
        assert_eq!(timer.len(&world), 0);
    }

    #[test]
    fn self_rescheduling_callback() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        fn periodic(
            ctx: &mut Duration,
            mut counter: ResMut<u64>,
            mut wheel: ResMut<TimerWheel>,
            reg: RegistryRef,
            now: Instant,
        ) {
            *counter += 1;
            if *counter < 3 {
                let interval = *ctx;
                let next = periodic.into_callback(interval, &reg);
                wheel.schedule_forget(now + interval, Box::new(next));
            }
        }

        let now = Instant::now();
        let interval = Duration::from_millis(1);
        let cb = periodic.into_callback(interval, world.registry());
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(now, Box::new(cb));

        // Fire first
        timer.poll(&mut world, now);
        assert_eq!(*world.resource::<u64>(), 1);

        // Fire second (rescheduled)
        timer.poll(&mut world, now + interval);
        assert_eq!(*world.resource::<u64>(), 2);

        // Fire third (rescheduled again, but won't reschedule since counter >= 3)
        timer.poll(&mut world, now + interval * 2);
        assert_eq!(*world.resource::<u64>(), 3);

        // No more timers
        assert!(timer.is_empty(&world));
    }

    #[test]
    fn cancellable_timer() {
        let mut builder = WorldBuilder::new();
        builder.register::<bool>(false);
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        fn on_fire(mut flag: ResMut<bool>, _now: Instant) {
            *flag = true;
        }

        let now = Instant::now();
        let deadline = now + Duration::from_millis(100);
        let h = on_fire.into_handler(world.registry());
        let cancel_handle = world
            .resource_mut::<TimerWheel>()
            .schedule(deadline, Box::new(h));

        // Cancel before firing
        let cancelled = world.resource_mut::<TimerWheel>().cancel(cancel_handle);
        assert!(cancelled.is_some());

        // Poll — nothing fires
        let fired = timer.poll(&mut world, deadline);
        assert_eq!(fired, 0);
        assert!(!*world.resource::<bool>());
    }

    #[test]
    fn poll_advances_sequence() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        fn inc(mut counter: ResMut<u64>, _now: Instant) {
            *counter += 1;
        }

        let now = Instant::now();
        let h1 = inc.into_handler(world.registry());
        let h2 = inc.into_handler(world.registry());
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(now, Box::new(h1));
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(now, Box::new(h2));

        let seq_before = world.current_sequence();
        timer.poll(&mut world, now);
        // Two handlers fired, two next_sequence calls
        assert_eq!(world.current_sequence().0, seq_before.0 + 2);
    }

    #[test]
    fn reschedule_timer() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        fn on_fire(mut counter: ResMut<u64>, _now: Instant) {
            *counter += 1;
        }

        let now = Instant::now();
        let h = on_fire.into_handler(world.registry());
        let handle = world
            .resource_mut::<TimerWheel>()
            .schedule(now + Duration::from_millis(100), Box::new(h));

        // Reschedule to earlier
        let handle = world
            .resource_mut::<TimerWheel>()
            .reschedule(handle, now + Duration::from_millis(50));

        // Should NOT fire at 40ms
        let fired = timer.poll(&mut world, now + Duration::from_millis(40));
        assert_eq!(fired, 0);
        assert_eq!(*world.resource::<u64>(), 0);

        // Should fire at 55ms
        let fired = timer.poll(&mut world, now + Duration::from_millis(55));
        assert_eq!(fired, 1);
        assert_eq!(*world.resource::<u64>(), 1);

        // Clean up zombie handle
        world.resource_mut::<TimerWheel>().cancel(handle);
    }

    #[test]
    fn periodic_fires_repeatedly() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        fn tick(mut counter: ResMut<u64>, _now: Instant) {
            *counter += 1;
        }

        let now = Instant::now();
        let interval = Duration::from_millis(10);
        let handler = tick.into_handler(world.registry());
        let periodic: Periodic<_> = Periodic::new(handler, interval);
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(now, Box::new(periodic));

        // First firing
        timer.poll(&mut world, now);
        assert_eq!(*world.resource::<u64>(), 1);

        // Second firing (rescheduled to now + 10ms)
        timer.poll(&mut world, now + interval);
        assert_eq!(*world.resource::<u64>(), 2);

        // Third firing (rescheduled to now + 20ms)
        timer.poll(&mut world, now + interval * 2);
        assert_eq!(*world.resource::<u64>(), 3);

        // Still active — periodic never stops on its own
        assert!(!timer.is_empty(&world));
    }

    #[test]
    fn periodic_cancel_drops_inner() {
        let mut builder = WorldBuilder::new();
        builder.register::<bool>(false);
        let mut timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let mut world = builder.build();

        fn on_fire(mut flag: ResMut<bool>, _now: Instant) {
            *flag = true;
        }

        let now = Instant::now();
        let handler = on_fire.into_handler(world.registry());
        let periodic: Periodic<_> = Periodic::new(handler, Duration::from_millis(50));
        let handle = world
            .resource_mut::<TimerWheel>()
            .schedule(now + Duration::from_millis(50), Box::new(periodic));

        // Cancel before it fires
        let cancelled = world.resource_mut::<TimerWheel>().cancel(handle);
        assert!(cancelled.is_some());

        // Poll — nothing fires
        let fired = timer.poll(&mut world, now + Duration::from_millis(100));
        assert_eq!(fired, 0);
        assert!(!*world.resource::<bool>());
    }

    #[test]
    fn periodic_into_inner_recovers_handler() {
        let mut builder = WorldBuilder::new();
        let _timer: TimerPoller =
            builder.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
        let world = builder.build();

        fn noop(_now: Instant) {}

        let handler = noop.into_handler(world.registry());
        let periodic: Periodic<_> = Periodic::new(handler, Duration::from_millis(10));
        assert!(periodic.into_inner().is_some());
    }

    // -- Bounded wheel tests --------------------------------------------------

    #[test]
    fn bounded_install_registers_wheel() {
        let mut builder = WorldBuilder::new();
        let wheel = BoundedTimerWheel::bounded(64, Instant::now());
        let _handle: BoundedTimerPoller = builder.install_driver(TimerInstaller::new(wheel));
        let world = builder.build();
        assert!(world.contains::<BoundedTimerWheel>());
    }

    #[test]
    fn bounded_one_shot_fires() {
        let mut builder = WorldBuilder::new();
        builder.register::<bool>(false);
        let wheel = BoundedTimerWheel::bounded(64, Instant::now());
        let mut timer: BoundedTimerPoller = builder.install_driver(TimerInstaller::new(wheel));
        let mut world = builder.build();

        fn on_timeout(mut flag: ResMut<bool>, _now: Instant) {
            *flag = true;
        }

        let handler = on_timeout.into_handler(world.registry());
        let now = Instant::now();
        world
            .resource_mut::<BoundedTimerWheel>()
            .try_schedule_forget(now, Box::new(handler))
            .expect("should not be full");

        assert!(!*world.resource::<bool>());
        let fired = timer.poll(&mut world, now);
        assert_eq!(fired, 1);
        assert!(*world.resource::<bool>());
    }

    #[test]
    fn bounded_cancel_and_query() {
        let mut builder = WorldBuilder::new();
        let wheel = BoundedTimerWheel::bounded(64, Instant::now());
        let mut timer: BoundedTimerPoller = builder.install_driver(TimerInstaller::new(wheel));
        let mut world = builder.build();

        fn noop(_now: Instant) {}

        let now = Instant::now();
        let h = noop.into_handler(world.registry());
        let handle = world
            .resource_mut::<BoundedTimerWheel>()
            .try_schedule(now + Duration::from_millis(100), Box::new(h))
            .expect("should not be full");

        assert_eq!(timer.len(&world), 1);
        assert!(!timer.is_empty(&world));
        assert!(timer.next_deadline(&world).is_some());

        let cancelled = world.resource_mut::<BoundedTimerWheel>().cancel(handle);
        assert!(cancelled.is_some());

        let fired = timer.poll(&mut world, now + Duration::from_millis(200));
        assert_eq!(fired, 0);
        assert_eq!(timer.len(&world), 0);
    }

    #[test]
    fn bounded_full_returns_error() {
        let mut builder = WorldBuilder::new();
        let wheel = BoundedTimerWheel::bounded(1, Instant::now());
        let _timer: BoundedTimerPoller = builder.install_driver(TimerInstaller::new(wheel));
        let mut world = builder.build();

        fn noop(_now: Instant) {}

        let now = Instant::now();
        let h1 = noop.into_handler(world.registry());
        world
            .resource_mut::<BoundedTimerWheel>()
            .try_schedule_forget(now + Duration::from_secs(60), Box::new(h1))
            .expect("first should succeed");

        let h2 = noop.into_handler(world.registry());
        let result = world
            .resource_mut::<BoundedTimerWheel>()
            .try_schedule_forget(now + Duration::from_secs(60), Box::new(h2));
        assert!(result.is_err());
    }

    // -- Builder configuration coverage ---------------------------------------

    /// Helper: install, schedule, poll, assert fired. Proves the full
    /// path works end-to-end for a given installer configuration.
    fn assert_unbounded_fires(installer: TimerInstaller) {
        let mut builder = WorldBuilder::new();
        builder.register::<bool>(false);
        let mut timer: TimerPoller = builder.install_driver(installer);
        let mut world = builder.build();

        fn on_fire(mut flag: ResMut<bool>, _now: Instant) {
            *flag = true;
        }

        let now = Instant::now();
        let h = on_fire.into_handler(world.registry());
        world
            .resource_mut::<TimerWheel>()
            .schedule_forget(now, Box::new(h));

        let fired = timer.poll(&mut world, now);
        assert_eq!(fired, 1);
        assert!(*world.resource::<bool>());
    }

    fn assert_bounded_fires(installer: BoundedTimerInstaller) {
        let mut builder = WorldBuilder::new();
        builder.register::<bool>(false);
        let mut timer: BoundedTimerPoller = builder.install_driver(installer);
        let mut world = builder.build();

        fn on_fire(mut flag: ResMut<bool>, _now: Instant) {
            *flag = true;
        }

        let now = Instant::now();
        let h = on_fire.into_handler(world.registry());
        world
            .resource_mut::<BoundedTimerWheel>()
            .try_schedule_forget(now, Box::new(h))
            .expect("should not be full");

        let fired = timer.poll(&mut world, now);
        assert_eq!(fired, 1);
        assert!(*world.resource::<bool>());
    }

    // -- Unbounded constructors -----------------------------------------------

    #[test]
    fn cfg_unbounded_default() {
        let now = Instant::now();
        assert_unbounded_fires(TimerInstaller::new(Wheel::unbounded(64, now)));
    }

    #[test]
    fn cfg_unbounded_chunk_capacity() {
        let now = Instant::now();
        assert_unbounded_fires(TimerInstaller::new(Wheel::unbounded(256, now)));
    }

    #[test]
    fn cfg_unbounded_tick_duration() {
        let now = Instant::now();
        assert_unbounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .tick_duration(Duration::from_micros(100))
                .unbounded(64)
                .build(now)
                .unwrap(),
        ));
    }

    #[test]
    fn cfg_unbounded_slots_per_level() {
        let now = Instant::now();
        assert_unbounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .slots_per_level(32)
                .unbounded(64)
                .build(now)
                .unwrap(),
        ));
    }

    #[test]
    fn cfg_unbounded_clk_shift() {
        let now = Instant::now();
        assert_unbounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .clk_shift(2)
                .unbounded(64)
                .build(now)
                .unwrap(),
        ));
    }

    #[test]
    fn cfg_unbounded_num_levels() {
        let now = Instant::now();
        assert_unbounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .num_levels(4)
                .unbounded(64)
                .build(now)
                .unwrap(),
        ));
    }

    #[test]
    fn cfg_unbounded_full_chain() {
        let now = Instant::now();
        assert_unbounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .tick_duration(Duration::from_micros(500))
                .slots_per_level(32)
                .clk_shift(2)
                .num_levels(5)
                .unbounded(128)
                .build(now)
                .unwrap(),
        ));
    }

    // -- Bounded constructors -------------------------------------------------

    #[test]
    fn cfg_bounded_default() {
        let now = Instant::now();
        assert_bounded_fires(TimerInstaller::new(
            WheelBuilder::default().bounded(64).build(now).unwrap(),
        ));
    }

    #[test]
    fn cfg_bounded_tick_duration() {
        let now = Instant::now();
        assert_bounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .tick_duration(Duration::from_micros(100))
                .bounded(64)
                .build(now)
                .unwrap(),
        ));
    }

    #[test]
    fn cfg_bounded_slots_per_level() {
        let now = Instant::now();
        assert_bounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .slots_per_level(32)
                .bounded(64)
                .build(now)
                .unwrap(),
        ));
    }

    #[test]
    fn cfg_bounded_clk_shift() {
        let now = Instant::now();
        assert_bounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .clk_shift(2)
                .bounded(64)
                .build(now)
                .unwrap(),
        ));
    }

    #[test]
    fn cfg_bounded_num_levels() {
        let now = Instant::now();
        assert_bounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .num_levels(4)
                .bounded(64)
                .build(now)
                .unwrap(),
        ));
    }

    #[test]
    fn cfg_bounded_full_chain() {
        let now = Instant::now();
        assert_bounded_fires(TimerInstaller::new(
            WheelBuilder::default()
                .tick_duration(Duration::from_micros(500))
                .slots_per_level(32)
                .clk_shift(2)
                .num_levels(5)
                .bounded(128)
                .build(now)
                .unwrap(),
        ));
    }

    // -- Different handler storage types --------------------------------------

    #[cfg(feature = "smartptr")]
    mod storage_tests {
        use super::*;

        #[test]
        fn unbounded_inline_storage() {
            let mut builder = WorldBuilder::new();
            builder.register::<bool>(false);
            let wheel = InlineTimerWheel::unbounded(64, Instant::now());
            let mut timer = builder.install_driver(TimerInstaller::new(wheel));
            let mut world = builder.build();

            fn on_fire(mut flag: ResMut<bool>, _now: Instant) {
                *flag = true;
            }

            let now = Instant::now();
            let h = on_fire.into_handler(world.registry());
            let ptr: *const dyn Handler<Instant> = &h;
            // SAFETY: ptr metadata from h's concrete type
            let storage = unsafe { nexus_smartptr::Flat::new_raw(h, ptr) };
            world
                .resource_mut::<InlineTimerWheel>()
                .schedule_forget(now, storage);

            let fired = timer.poll(&mut world, now);
            assert_eq!(fired, 1);
            assert!(*world.resource::<bool>());
        }

        #[test]
        fn unbounded_flex_storage() {
            let mut builder = WorldBuilder::new();
            builder.register::<bool>(false);
            let wheel = FlexTimerWheel::unbounded(64, Instant::now());
            let mut timer = builder.install_driver(TimerInstaller::new(wheel));
            let mut world = builder.build();

            fn on_fire(mut flag: ResMut<bool>, _now: Instant) {
                *flag = true;
            }

            let now = Instant::now();
            let h = on_fire.into_handler(world.registry());
            let ptr: *const dyn Handler<Instant> = &h;
            // SAFETY: ptr metadata from h's concrete type
            let storage = unsafe { nexus_smartptr::Flex::new_raw(h, ptr) };
            world
                .resource_mut::<FlexTimerWheel>()
                .schedule_forget(now, storage);

            let fired = timer.poll(&mut world, now);
            assert_eq!(fired, 1);
            assert!(*world.resource::<bool>());
        }

        #[test]
        fn bounded_inline_storage() {
            let mut builder = WorldBuilder::new();
            builder.register::<bool>(false);
            let wheel = BoundedInlineTimerWheel::bounded(64, Instant::now());
            let mut timer = builder.install_driver(TimerInstaller::new(wheel));
            let mut world = builder.build();

            fn on_fire(mut flag: ResMut<bool>, _now: Instant) {
                *flag = true;
            }

            let now = Instant::now();
            let h = on_fire.into_handler(world.registry());
            let ptr: *const dyn Handler<Instant> = &h;
            // SAFETY: ptr metadata from h's concrete type
            let storage = unsafe { nexus_smartptr::Flat::new_raw(h, ptr) };
            world
                .resource_mut::<BoundedInlineTimerWheel>()
                .try_schedule_forget(now, storage)
                .expect("should not be full");

            let fired = timer.poll(&mut world, now);
            assert_eq!(fired, 1);
            assert!(*world.resource::<bool>());
        }

        #[test]
        fn bounded_flex_storage() {
            let mut builder = WorldBuilder::new();
            builder.register::<bool>(false);
            let wheel = BoundedFlexTimerWheel::bounded(64, Instant::now());
            let mut timer = builder.install_driver(TimerInstaller::new(wheel));
            let mut world = builder.build();

            fn on_fire(mut flag: ResMut<bool>, _now: Instant) {
                *flag = true;
            }

            let now = Instant::now();
            let h = on_fire.into_handler(world.registry());
            let ptr: *const dyn Handler<Instant> = &h;
            // SAFETY: ptr metadata from h's concrete type
            let storage = unsafe { nexus_smartptr::Flex::new_raw(h, ptr) };
            world
                .resource_mut::<BoundedFlexTimerWheel>()
                .try_schedule_forget(now, storage)
                .expect("should not be full");

            let fired = timer.poll(&mut world, now);
            assert_eq!(fired, 1);
            assert!(*world.resource::<bool>());
        }

        #[test]
        fn periodic_inline_fires_repeatedly() {
            let mut builder = WorldBuilder::new();
            builder.register::<u64>(0);
            let wheel = InlineTimerWheel::unbounded(64, Instant::now());
            let mut timer = builder.install_driver(TimerInstaller::new(wheel));
            let mut world = builder.build();

            fn tick(mut counter: ResMut<u64>, _now: Instant) {
                *counter += 1;
            }

            let now = Instant::now();
            let interval = Duration::from_millis(10);
            let handler = tick.into_handler(world.registry());
            let periodic: Periodic<_, InlineTimers, nexus_timer::store::UnboundedSlab<_>> =
                Periodic::new(handler, interval);
            world
                .resource_mut::<InlineTimerWheel>()
                .schedule_forget(now, InlineTimers::wrap(periodic));

            // First firing
            timer.poll(&mut world, now);
            assert_eq!(*world.resource::<u64>(), 1);

            // Second firing (rescheduled to now + 10ms)
            timer.poll(&mut world, now + interval);
            assert_eq!(*world.resource::<u64>(), 2);

            // Third firing (rescheduled to now + 20ms)
            timer.poll(&mut world, now + interval * 2);
            assert_eq!(*world.resource::<u64>(), 3);

            // Still active — periodic never stops on its own
            assert!(!timer.is_empty(&world));
        }

        #[test]
        fn periodic_flex_fires_repeatedly() {
            let mut builder = WorldBuilder::new();
            builder.register::<u64>(0);
            let wheel = FlexTimerWheel::unbounded(64, Instant::now());
            let mut timer = builder.install_driver(TimerInstaller::new(wheel));
            let mut world = builder.build();

            fn tick(mut counter: ResMut<u64>, _now: Instant) {
                *counter += 1;
            }

            let now = Instant::now();
            let interval = Duration::from_millis(10);
            let handler = tick.into_handler(world.registry());
            let periodic: Periodic<_, FlexTimers, nexus_timer::store::UnboundedSlab<_>> =
                Periodic::new(handler, interval);
            world
                .resource_mut::<FlexTimerWheel>()
                .schedule_forget(now, FlexTimers::wrap(periodic));

            timer.poll(&mut world, now);
            assert_eq!(*world.resource::<u64>(), 1);

            timer.poll(&mut world, now + interval);
            assert_eq!(*world.resource::<u64>(), 2);

            timer.poll(&mut world, now + interval * 2);
            assert_eq!(*world.resource::<u64>(), 3);

            assert!(!timer.is_empty(&world));
        }
    }
}
