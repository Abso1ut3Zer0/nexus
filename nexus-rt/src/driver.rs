//! Installer trait for event source installation.

use crate::world::WorldBuilder;

/// Install-time trait for event sources.
///
/// An installer registers its resources into [`WorldBuilder`] and returns a
/// concrete poller. The poller is a thin struct of pre-resolved
/// [`ResourceId`](crate::ResourceId)s — it knows how to reach into
/// [`World`](crate::World) but owns nothing.
///
/// Each poller defines its own `poll()` signature. This is intentional:
/// different drivers need different parameters (e.g. a timer driver
/// needs `Instant`, an IO driver does not).
///
/// # Registering resources: owned vs. shared
///
/// Choose the [`WorldBuilder`] registration method by **who owns the resource**:
///
/// - **Owned** — the installer creates it and is its sole writer (a driver's
///   wheel, an IO poller's state). Use [`register`](WorldBuilder::register). A
///   duplicate is a wiring bug, so it panics — and the panic names `ensure` /
///   `try_register` for anyone who meant to share. This is the default for
///   driver-private state.
/// - **Shared** — a common dependency several drivers read (e.g.
///   [`Clock`](crate::clock::Clock)); the installer may drive its value but does not
///   exclusively own the slot. Use [`ensure`](WorldBuilder::ensure) /
///   [`ensure_default`](WorldBuilder::ensure_default). Idempotent: the first
///   caller creates it, later callers get the same id, so it composes
///   regardless of install order. (Do not `ensure` a resource you *move* in and
///   exclusively mutate — the value would be dropped and you'd alias someone
///   else's; that is what "owned" is for.)
/// - **Required (provided elsewhere)** — a resource another installer must
///   register that this one cannot default. Resolve it with
///   [`id`](WorldBuilder::id) (check [`contains`](WorldBuilder::contains) first
///   if the dependency is optional). If it is absent, `id` panics with a
///   message naming how to provide it. Do **not** return `Result` from
///   `install` for this: a missing dependency is a deterministic composition
///   error caught at startup, with no runtime recovery — panic, fail fast.
///   Only *config values* are fallible; validate those to a `Result` (e.g. a
///   `ConfigError`) in your builder, before `install`.
///
/// # Examples
///
/// ```ignore
/// struct IoInstaller { capacity: usize }
///
/// struct IoPoller {
///     poller_id: ResourceId,
///     events_id: ResourceId,
/// }
///
/// impl Installer for IoInstaller {
///     type Poller = IoPoller;
///
///     fn install(self, world: &mut WorldBuilder) -> IoPoller {
///         let poller_id = world.register(Poller::new());
///         let events_id = world.register(MioEvents::with_capacity(self.capacity));
///         IoPoller { poller_id, events_id }
///     }
/// }
///
/// // Poller has its own poll signature — NOT a trait method.
/// impl IoPoller {
///     fn poll(&mut self, world: &mut World) {
///         // get resources via pre-resolved IDs, poll mio, dispatch
///     }
/// }
///
/// let mut wb = WorldBuilder::new();
/// let io = wb.install_driver(IoInstaller { capacity: 1024 });
/// let mut world = wb.build();
///
/// loop {
///     io.poll(&mut world);
/// }
/// ```
pub trait Installer {
    /// The concrete poller returned after installation.
    type Poller;

    /// Register resources into the world and return a poller for dispatch.
    fn install(self, world: &mut WorldBuilder) -> Self::Poller;
}
