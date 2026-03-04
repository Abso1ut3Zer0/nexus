//! Type-erased singleton resource storage.
//!
//! [`World`] is a unified store where each resource type gets a dense index
//! ([`ResourceId`]) for O(1) dispatch-time access. Registration happens through
//! [`WorldBuilder`], which freezes into an immutable [`World`] container via
//! [`build()`](WorldBuilder::build).
//!
//! The type [`Registry`] maps types to dense indices. It is shared between
//! [`WorldBuilder`] and [`World`], and is passed to [`Param::init`] and
//! [`IntoHandler::into_handler`](crate::IntoHandler::into_handler) so that handlers can resolve their parameter
//! state during driver setup — before or after `build()`.
//!
//! # Lifecycle
//!
//! ```text
//! let mut builder = WorldBuilder::new();
//! builder.register::<PriceCache>(value);
//! builder.register::<TimerDriver>(value);
//!
//! // Drivers can resolve handlers against builder.registry()
//! // before World is built.
//!
//! let world = builder.build();  // → World (frozen)
//! ```
//!
//! After `build()`, the container is frozen — no inserts, no removes. All
//! [`ResourceId`] values are valid for the lifetime of the [`World`] container.

use std::any::{TypeId, type_name};
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;

use rustc_hash::FxHashMap;

// =============================================================================
// Core types
// =============================================================================

/// Dense index identifying a resource type within a [`World`] container.
///
/// Assigned sequentially at registration (0, 1, 2, ...). Used as a direct
/// index into internal storage at dispatch time — no hashing, no searching.
///
/// Obtained from [`WorldBuilder::register`], [`WorldBuilder::ensure`],
/// [`Registry::id`], [`World::id`], or their `try_` / `_default` variants.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ResourceId(u16);

impl std::fmt::Display for ResourceId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Monotonic event sequence number for change detection.
///
/// Each event processed by a driver is assigned a unique sequence number
/// via [`World::next_sequence`]. Resources record the sequence at which
/// they were last written. A resource is considered "changed" if its
/// `changed_at` equals the world's `current_sequence`. Wrapping is
/// harmless — only equality is checked.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct Sequence(pub(crate) u64);

impl std::fmt::Display for Sequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Type-erased drop function. Monomorphized at registration time so we
/// can reconstruct and drop the original `Box<T>` from a `*mut u8`.
pub(crate) type DropFn = unsafe fn(*mut u8);

/// Reconstruct and drop a `Box<T>` from a raw pointer.
///
/// # Safety
///
/// `ptr` must have been produced by `Box::into_raw(Box::new(value))`
/// where `value: T`. Must only be called once per pointer.
pub(crate) unsafe fn drop_resource<T>(ptr: *mut u8) {
    // SAFETY: ptr was produced by Box::into_raw(Box::new(value))
    // where value: T. Called exactly once in Storage::drop.
    unsafe {
        let _ = Box::from_raw(ptr as *mut T);
    }
}

// =============================================================================
// Registry — type-to-index mapping
// =============================================================================

/// Type-to-index mapping shared between [`WorldBuilder`] and [`World`].
///
/// Contains only the type registry — no storage, no pointers. Passed to
/// [`IntoHandler::into_handler`](crate::IntoHandler::into_handler) and
/// [`Param::init`](crate::Param::init) so handlers can resolve
/// [`ResourceId`]s during driver setup.
///
/// Obtained via [`WorldBuilder::registry()`] or [`World::registry()`].
pub struct Registry {
    indices: FxHashMap<TypeId, ResourceId>,
    /// Scratch bitset reused across [`check_access`](Self::check_access) calls.
    /// Allocated once on the first call with >128 resources, then reused.
    ///
    /// Interior mutability via `UnsafeCell` — only accessed in `check_access`,
    /// which is single-threaded and non-reentrant. `UnsafeCell` makes
    /// `Registry` `!Sync` automatically, which is correct — `World` is
    /// already `!Sync`.
    scratch: UnsafeCell<Vec<u64>>,
}

impl Registry {
    pub(crate) fn new() -> Self {
        Self {
            indices: FxHashMap::default(),
            scratch: UnsafeCell::new(Vec::new()),
        }
    }

    /// Resolve the [`ResourceId`] for a type. Cold path — uses HashMap lookup.
    ///
    /// # Panics
    ///
    /// Panics if the resource type was not registered.
    pub fn id<T: 'static>(&self) -> ResourceId {
        *self
            .indices
            .get(&TypeId::of::<T>())
            .unwrap_or_else(|| panic!("resource `{}` not registered", type_name::<T>()))
    }

    /// Try to resolve the [`ResourceId`] for a type. Returns `None` if the
    /// type was not registered.
    pub fn try_id<T: 'static>(&self) -> Option<ResourceId> {
        self.indices.get(&TypeId::of::<T>()).copied()
    }

    /// Returns `true` if a resource of type `T` has been registered.
    pub fn contains<T: 'static>(&self) -> bool {
        self.indices.contains_key(&TypeId::of::<T>())
    }

    /// Returns the number of registered resources.
    pub fn len(&self) -> usize {
        self.indices.len()
    }

    /// Returns `true` if no resources have been registered.
    pub fn is_empty(&self) -> bool {
        self.indices.is_empty()
    }

    /// Validate that a set of parameter accesses don't conflict.
    ///
    /// Two accesses conflict when they target the same ResourceId.
    /// Called at construction time by `into_handler`, `into_callback`,
    /// and `into_stage`.
    ///
    /// Fast path (≤128 resources): single `u128` on the stack, zero heap.
    /// Slow path (>128 resources): reusable `Vec<u64>` owned by Registry —
    /// allocated once on first use, then cleared and reused.
    ///
    /// # Panics
    ///
    /// Panics if any resource is accessed by more than one parameter.
    #[cold]
    pub fn check_access(&self, accesses: &[(Option<ResourceId>, &str)]) {
        let n = self.len();
        if n == 0 {
            return;
        }

        if n <= 128 {
            // Fast path: single u128 on the stack.
            let mut seen = 0u128;
            for &(id, name) in accesses {
                let Some(id) = id else { continue };
                let bit = 1u128 << id.0;
                assert!(
                    seen & bit == 0,
                    "conflicting access: resource borrowed by `{}` is already \
                     borrowed by another parameter in the same handler",
                    name,
                );
                seen |= bit;
            }
        } else {
            // Slow path: reusable heap buffer.
            // SAFETY: single-threaded access guaranteed by !Sync on Registry
            // (UnsafeCell is !Sync). check_access is non-reentrant — it runs,
            // uses scratch, and returns. No aliasing possible.
            let scratch = unsafe { &mut *self.scratch.get() };
            let words = n.div_ceil(64);
            scratch.resize(words, 0);
            scratch.fill(0);
            for &(id, name) in accesses {
                let Some(id) = id else { continue };
                let idx = id.0 as usize;
                let word = idx / 64;
                let bit = 1u64 << (idx % 64);
                assert!(
                    scratch[word] & bit == 0,
                    "conflicting access: resource borrowed by `{}` is already \
                     borrowed by another parameter in the same handler",
                    name,
                );
                scratch[word] |= bit;
            }
        }
    }
}

// =============================================================================
// Storage — shared backing between builder and frozen container
// =============================================================================

/// Interleaved pointer + change sequence for a single resource.
/// 16 bytes — 4 slots per cache line.
#[repr(C)]
pub(crate) struct ResourceSlot {
    pub(crate) ptr: *mut u8,
    pub(crate) changed_at: Cell<Sequence>,
}

/// Internal storage for type-erased resource pointers and their destructors.
///
/// Owns the heap allocations and is responsible for cleanup. Shared between
/// [`WorldBuilder`] and [`World`] via move — avoids duplicating Drop logic.
pub(crate) struct Storage {
    /// Dense array of interleaved pointer + change sequence pairs.
    /// Each pointer was produced by `Box::into_raw`.
    pub(crate) slots: Vec<ResourceSlot>,
    /// Parallel array of drop functions. `drop_fns[i]` is the monomorphized
    /// destructor for the concrete type behind `slots[i].ptr`.
    pub(crate) drop_fns: Vec<DropFn>,
}

impl Storage {
    pub(crate) fn new() -> Self {
        Self {
            slots: Vec::new(),
            drop_fns: Vec::new(),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.slots.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}

// SAFETY: All values stored in Storage were registered via `register<T: Send + 'static>`,
// so every concrete type behind the raw pointers is Send. Storage exclusively owns
// these heap allocations — they are not aliased or shared. Transferring ownership
// to another thread is safe. Cell<Sequence> is !Sync but we're transferring
// ownership, not sharing.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl Send for Storage {}

impl Drop for Storage {
    fn drop(&mut self) {
        for (slot, drop_fn) in self.slots.iter().zip(&self.drop_fns) {
            // SAFETY: each (slot.ptr, drop_fn) pair was created together in
            // WorldBuilder::register(). drop_fn is the monomorphized
            // destructor for the concrete type behind ptr. Called exactly
            // once here.
            unsafe {
                drop_fn(slot.ptr);
            }
        }
    }
}

// =============================================================================
// WorldBuilder
// =============================================================================

/// Builder for registering resources before freezing into a [`World`] container.
///
/// Each resource type can only be registered once. Registration assigns a
/// dense [`ResourceId`] index (0, 1, 2, ...).
///
/// The [`registry()`](Self::registry) method exposes the type-to-index mapping
/// so that drivers can resolve handlers against the builder before `build()`.
///
/// # Examples
///
/// ```
/// use nexus_rt::WorldBuilder;
///
/// let mut builder = WorldBuilder::new();
/// let id = builder.register::<u64>(42);
/// builder.register::<bool>(true);
/// let world = builder.build();
///
/// unsafe {
///     assert_eq!(*world.get::<u64>(id), 42);
/// }
/// ```
pub struct WorldBuilder {
    registry: Registry,
    storage: Storage,
}

impl WorldBuilder {
    /// Create an empty builder.
    pub fn new() -> Self {
        Self {
            registry: Registry::new(),
            storage: Storage::new(),
        }
    }

    /// Register a resource and return its [`ResourceId`].
    ///
    /// The value is heap-allocated via `Box` and ownership is transferred
    /// to the container. The pointer is stable for the lifetime of the
    /// resulting [`World`].
    ///
    /// # Panics
    ///
    /// Panics if a resource of the same type is already registered.
    #[cold]
    pub fn register<T: Send + 'static>(&mut self, value: T) -> ResourceId {
        let type_id = TypeId::of::<T>();
        assert!(
            !self.registry.indices.contains_key(&type_id),
            "resource `{}` already registered",
            type_name::<T>(),
        );

        assert!(
            u16::try_from(self.storage.slots.len()).is_ok(),
            "resource limit exceeded ({} registered, max {})",
            self.storage.slots.len(),
            usize::from(u16::MAX) + 1,
        );

        let ptr = Box::into_raw(Box::new(value)) as *mut u8;
        let id = ResourceId(self.storage.slots.len() as u16);
        self.registry.indices.insert(type_id, id);
        self.storage.slots.push(ResourceSlot {
            ptr,
            changed_at: Cell::new(Sequence(0)),
        });
        self.storage.drop_fns.push(drop_resource::<T>);
        id
    }

    /// Register a resource using its [`Default`] value and return its
    /// [`ResourceId`].
    ///
    /// Equivalent to `self.register::<T>(T::default())`.
    #[cold]
    pub fn register_default<T: Default + Send + 'static>(&mut self) -> ResourceId {
        self.register(T::default())
    }

    /// Ensure a resource is registered, returning its [`ResourceId`].
    ///
    /// If the type is already registered, returns the existing ID and
    /// drops `value`. If not, registers it and returns the new ID.
    ///
    /// Use [`register`](Self::register) when duplicate registration is a
    /// bug that should panic. Use `ensure` when multiple plugins or
    /// drivers may independently need the same resource type.
    #[cold]
    pub fn ensure<T: Send + 'static>(&mut self, value: T) -> ResourceId {
        if let Some(id) = self.registry.try_id::<T>() {
            return id;
        }
        self.register(value)
    }

    /// Ensure a resource is registered using its [`Default`] value,
    /// returning its [`ResourceId`].
    ///
    /// If the type is already registered, returns the existing ID.
    /// If not, registers `T::default()` and returns the new ID.
    #[cold]
    pub fn ensure_default<T: Default + Send + 'static>(&mut self) -> ResourceId {
        if let Some(id) = self.registry.try_id::<T>() {
            return id;
        }
        self.register(T::default())
    }

    /// Returns a shared reference to the type registry.
    ///
    /// Use this for construction-time calls like
    /// [`into_handler`](crate::IntoHandler::into_handler),
    /// [`into_callback`](crate::IntoCallback::into_callback), and
    /// [`into_stage`](crate::IntoStage::into_stage).
    pub fn registry(&self) -> &Registry {
        &self.registry
    }

    /// Returns a mutable reference to the type registry.
    ///
    /// Rarely needed — [`registry()`](Self::registry) suffices for
    /// construction-time calls. Exists for direct mutation of the
    /// registry if needed.
    pub fn registry_mut(&mut self) -> &mut Registry {
        &mut self.registry
    }

    /// Returns the number of registered resources.
    pub fn len(&self) -> usize {
        self.storage.len()
    }

    /// Returns `true` if no resources have been registered.
    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
    }

    /// Returns `true` if a resource of type `T` has been registered.
    pub fn contains<T: 'static>(&self) -> bool {
        self.registry.contains::<T>()
    }

    /// Install a plugin. The plugin is consumed and registers its
    /// resources into this builder.
    pub fn install_plugin(&mut self, plugin: impl crate::plugin::Plugin) -> &mut Self {
        plugin.build(self);
        self
    }

    /// Install a driver. The installer is consumed, registers its resources
    /// into this builder, and returns a concrete poller for dispatch-time
    /// polling.
    pub fn install_driver<D: crate::driver::Installer>(&mut self, driver: D) -> D::Poller {
        driver.install(self)
    }

    /// Freeze the builder into an immutable [`World`] container.
    ///
    /// After this call, no more resources can be registered. All
    /// [`ResourceId`] values remain valid for the lifetime of the
    /// returned [`World`].
    pub fn build(self) -> World {
        World {
            registry: self.registry,
            storage: self.storage,
            current_sequence: Sequence(0),
            _not_sync: PhantomData,
        }
    }
}

impl Default for WorldBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// World — frozen container
// =============================================================================

/// Frozen singleton resource storage.
///
/// Analogous to Bevy's `World`, but restricted to singleton resources
/// (no entities, no components, no archetypes).
///
/// Created by [`WorldBuilder::build()`]. Resources are indexed by dense
/// [`ResourceId`] for O(1) dispatch-time access (~3 cycles per fetch).
///
/// # Safe API
///
/// - [`resource`](Self::resource) / [`resource_mut`](Self::resource_mut) —
///   cold-path access via HashMap lookup.
///
/// # Unsafe API (framework internals)
///
/// The low-level `get` / `get_mut` methods are `unsafe` — used by
/// [`Param::fetch`](crate::Param) for ~3-cycle dispatch.
/// The caller must ensure no mutable aliasing.
pub struct World {
    /// Type-to-index mapping. Same registry used during build.
    registry: Registry,
    /// Type-erased pointer storage. Drop handled by `Storage`.
    storage: Storage,
    /// Current sequence number. Advanced by the driver before
    /// each event dispatch.
    current_sequence: Sequence,
    /// World must not be shared across threads — it holds interior-mutable
    /// `Cell<Sequence>` values accessed through `&self`. `!Sync` enforced by
    /// `PhantomData<Cell<()>>`.
    _not_sync: PhantomData<Cell<()>>,
}

impl World {
    /// Convenience constructor — returns a new [`WorldBuilder`].
    pub fn builder() -> WorldBuilder {
        WorldBuilder::new()
    }

    /// Returns a shared reference to the type registry.
    ///
    /// Use this for read-only queries (e.g. [`id`](Registry::id),
    /// [`contains`](Registry::contains)) and construction-time calls
    /// like [`into_handler`](crate::IntoHandler::into_handler).
    pub fn registry(&self) -> &Registry {
        &self.registry
    }

    /// Returns a mutable reference to the type registry.
    ///
    /// Rarely needed — [`registry()`](Self::registry) suffices for
    /// construction-time calls. Exists for direct mutation of the
    /// registry if needed.
    pub fn registry_mut(&mut self) -> &mut Registry {
        &mut self.registry
    }

    /// Resolve the [`ResourceId`] for a type. Cold path — uses HashMap lookup.
    ///
    /// # Panics
    ///
    /// Panics if the resource type was not registered.
    pub fn id<T: 'static>(&self) -> ResourceId {
        self.registry.id::<T>()
    }

    /// Try to resolve the [`ResourceId`] for a type. Returns `None` if the
    /// type was not registered.
    pub fn try_id<T: 'static>(&self) -> Option<ResourceId> {
        self.registry.try_id::<T>()
    }

    /// Returns the number of registered resources.
    pub fn len(&self) -> usize {
        self.storage.len()
    }

    /// Returns `true` if no resources are stored.
    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
    }

    /// Returns `true` if a resource of type `T` is stored.
    pub fn contains<T: 'static>(&self) -> bool {
        self.registry.contains::<T>()
    }

    // =========================================================================
    // Safe resource access (cold path — HashMap lookup per call)
    // =========================================================================

    /// Safe shared access to a resource. Cold path — resolves via HashMap.
    ///
    /// Takes `&self` — multiple shared references can coexist. The borrow
    /// checker prevents mixing with [`resource_mut`](Self::resource_mut)
    /// (which takes `&mut self`).
    ///
    /// # Panics
    ///
    /// Panics if the resource type was not registered.
    pub fn resource<T: 'static>(&self) -> &T {
        let id = self.registry.id::<T>();
        // SAFETY: id resolved from our own registry. &self prevents mutable
        // aliases — resource_mut takes &mut self.
        unsafe { self.get(id) }
    }

    /// Safe exclusive access to a resource. Cold path — resolves via HashMap.
    ///
    /// # Panics
    ///
    /// Panics if the resource type was not registered.
    pub fn resource_mut<T: 'static>(&mut self) -> &mut T {
        let id = self.registry.id::<T>();
        // Cold path — stamp unconditionally. If you request &mut, you're writing.
        self.storage.slots[id.0 as usize]
            .changed_at
            .set(self.current_sequence);
        // SAFETY: id resolved from our own registry. &mut self ensures
        // exclusive access — no other references can exist.
        unsafe { self.get_mut(id) }
    }

    // =========================================================================
    // One-shot dispatch
    // =========================================================================

    /// Run a handler once with full Param resolution.
    ///
    /// Intended for one-shot initialization after [`build()`](WorldBuilder::build).
    /// The handler receives `()` as the event — the event parameter is
    /// discarded. Named functions only (same closure limitation as
    /// [`IntoHandler`](crate::IntoHandler)).
    ///
    /// Can be called multiple times for phased initialization.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// fn startup(
    ///     mut driver: ResMut<MioDriver>,
    ///     mut listener: ResMut<Listener>,
    ///     _event: (),
    /// ) {
    ///     // wire drivers to IO sources...
    /// }
    ///
    /// let mut world = wb.build();
    /// world.run_startup(startup);
    /// ```
    pub fn run_startup<F, Params>(&mut self, f: F)
    where
        F: crate::IntoHandler<(), Params>,
    {
        use crate::Handler;
        let mut handler = f.into_handler(&self.registry);
        handler.run(self, ());
    }

    // =========================================================================
    // Sequence / change detection
    // =========================================================================

    /// Returns the current event sequence number.
    pub fn current_sequence(&self) -> Sequence {
        self.current_sequence
    }

    /// Advance to the next event sequence number and return it.
    ///
    /// Drivers call this before dispatching each event. The returned
    /// sequence number identifies the event being processed. Resources
    /// mutated during dispatch will record this sequence in `changed_at`.
    pub fn next_sequence(&mut self) -> Sequence {
        self.current_sequence = Sequence(self.current_sequence.0.wrapping_add(1));
        self.current_sequence
    }

    // =========================================================================
    // Unsafe resource access (hot path — pre-resolved ResourceId)
    // =========================================================================

    /// Fetch a shared reference to a resource by pre-validated index.
    ///
    /// # Safety
    ///
    /// - `id` must have been returned by [`WorldBuilder::register`] for
    ///   the same builder that produced this container.
    /// - `T` must be the same type that was registered at this `id`.
    /// - The caller must ensure no mutable reference to this resource exists.
    #[inline(always)]
    pub unsafe fn get<T: 'static>(&self, id: ResourceId) -> &T {
        // SAFETY: caller guarantees id was returned by register() on the
        // builder that produced this container, so id.0 < self.storage.slots.len().
        // T matches the registered type. No mutable alias exists.
        unsafe { &*(self.get_ptr(id) as *const T) }
    }

    /// Fetch a mutable reference to a resource by pre-validated index.
    ///
    /// Takes `&self` — the container structure is frozen, but individual
    /// resources have interior mutability via raw pointers. Sound because
    /// callers (single-threaded sequential dispatch) uphold no-aliasing.
    ///
    /// # Safety
    ///
    /// - `id` must have been returned by [`WorldBuilder::register`] for
    ///   the same builder that produced this container.
    /// - `T` must be the same type that was registered at this `id`.
    /// - The caller must ensure no other reference (shared or mutable) to this
    ///   resource exists.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn get_mut<T: 'static>(&self, id: ResourceId) -> &mut T {
        // SAFETY: caller guarantees id was returned by register() on the
        // builder that produced this container, so id.0 < self.storage.slots.len().
        // T matches the registered type. No aliases exist.
        unsafe { &mut *(self.get_ptr(id) as *mut T) }
    }

    /// Fetch a raw pointer to a resource by pre-validated index.
    ///
    /// Intended for macro-generated dispatch code that needs direct pointer
    /// access.
    ///
    /// # Safety
    ///
    /// - `id` must have been returned by [`WorldBuilder::register`] for
    ///   the same builder that produced this container.
    #[inline(always)]
    pub unsafe fn get_ptr(&self, id: ResourceId) -> *mut u8 {
        debug_assert!(
            (id.0 as usize) < self.storage.slots.len(),
            "ResourceId({}) out of bounds (len {})",
            id.0,
            self.storage.slots.len(),
        );
        // SAFETY: caller guarantees id was returned by register() on the
        // builder that produced this container, so id.0 < self.storage.slots.len().
        unsafe { self.storage.slots.get_unchecked(id.0 as usize).ptr }
    }

    // =========================================================================
    // Change-detection internals (framework use only)
    // =========================================================================

    /// Read the sequence at which a resource was last changed.
    ///
    /// # Safety
    ///
    /// `id` must have been returned by [`WorldBuilder::register`] for
    /// the same builder that produced this container.
    #[inline(always)]
    pub(crate) unsafe fn changed_at(&self, id: ResourceId) -> Sequence {
        unsafe {
            self.storage
                .slots
                .get_unchecked(id.0 as usize)
                .changed_at
                .get()
        }
    }

    /// Get a reference to the `Cell` tracking a resource's change sequence.
    ///
    /// # Safety
    ///
    /// `id` must have been returned by [`WorldBuilder::register`] for
    /// the same builder that produced this container.
    #[inline(always)]
    pub(crate) unsafe fn changed_at_cell(&self, id: ResourceId) -> &Cell<Sequence> {
        unsafe { &self.storage.slots.get_unchecked(id.0 as usize).changed_at }
    }

    /// Stamp a resource as changed at the current sequence.
    ///
    /// # Safety
    ///
    /// `id` must have been returned by [`WorldBuilder::register`] for
    /// the same builder that produced this container.
    #[inline(always)]
    #[allow(dead_code)] // Available for driver implementations.
    pub(crate) unsafe fn stamp_changed(&self, id: ResourceId) {
        unsafe {
            self.storage
                .slots
                .get_unchecked(id.0 as usize)
                .changed_at
                .set(self.current_sequence);
        }
    }
}

// SAFETY: All resources are `T: Send` (enforced by `register`). World owns all
// heap-allocated data exclusively — the raw pointers are not aliased or shared.
// Transferring ownership to another thread is safe; the new thread becomes the
// sole accessor.
unsafe impl Send for World {}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Weak};

    struct Price {
        value: f64,
    }

    struct Venue {
        name: &'static str,
    }

    struct Config {
        max_orders: usize,
    }

    #[test]
    fn register_and_build() {
        let mut builder = WorldBuilder::new();
        builder.register::<Price>(Price { value: 100.0 });
        builder.register::<Venue>(Venue { name: "test" });
        let world = builder.build();
        assert_eq!(world.len(), 2);
    }

    #[test]
    fn resource_ids_are_sequential() {
        let mut builder = WorldBuilder::new();
        let id0 = builder.register::<Price>(Price { value: 0.0 });
        let id1 = builder.register::<Venue>(Venue { name: "" });
        let id2 = builder.register::<Config>(Config { max_orders: 0 });
        assert_eq!(id0, ResourceId(0));
        assert_eq!(id1, ResourceId(1));
        assert_eq!(id2, ResourceId(2));
    }

    #[test]
    fn get_returns_registered_value() {
        let mut builder = WorldBuilder::new();
        builder.register::<Price>(Price { value: 42.5 });
        let world = builder.build();

        let id = world.id::<Price>();
        // SAFETY: id resolved from this container, type matches, no aliasing.
        let price = unsafe { world.get::<Price>(id) };
        assert_eq!(price.value, 42.5);
    }

    #[test]
    fn get_mut_modifies_value() {
        let mut builder = WorldBuilder::new();
        builder.register::<Price>(Price { value: 1.0 });
        let world = builder.build();

        let id = world.id::<Price>();
        // SAFETY: id resolved from this container, type matches, no aliasing.
        unsafe {
            world.get_mut::<Price>(id).value = 99.0;
            assert_eq!(world.get::<Price>(id).value, 99.0);
        }
    }

    #[test]
    fn try_id_returns_none_for_unregistered() {
        let world = WorldBuilder::new().build();
        assert!(world.try_id::<Price>().is_none());
    }

    #[test]
    fn try_id_returns_some_for_registered() {
        let mut builder = WorldBuilder::new();
        builder.register::<Price>(Price { value: 0.0 });
        let world = builder.build();

        assert!(world.try_id::<Price>().is_some());
    }

    #[test]
    #[should_panic(expected = "already registered")]
    fn panics_on_duplicate_registration() {
        let mut builder = WorldBuilder::new();
        builder.register::<Price>(Price { value: 1.0 });
        builder.register::<Price>(Price { value: 2.0 });
    }

    #[test]
    #[should_panic(expected = "not registered")]
    fn panics_on_unregistered_id() {
        let world = WorldBuilder::new().build();
        world.id::<Price>();
    }

    #[test]
    fn empty_builder_builds_empty_world() {
        let world = WorldBuilder::new().build();
        assert_eq!(world.len(), 0);
        assert!(world.is_empty());
    }

    #[test]
    fn drop_runs_destructors() {
        let arc = Arc::new(42u32);
        let weak: Weak<u32> = Arc::downgrade(&arc);

        {
            let mut builder = WorldBuilder::new();
            builder.register::<Arc<u32>>(arc);
            let _world = builder.build();
            // Arc still alive — held by World
            assert!(weak.upgrade().is_some());
        }
        // World dropped — Arc should be deallocated
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn builder_drop_cleans_up_without_build() {
        let arc = Arc::new(99u32);
        let weak: Weak<u32> = Arc::downgrade(&arc);

        {
            let mut builder = WorldBuilder::new();
            builder.register::<Arc<u32>>(arc);
        }
        // Builder dropped without build() — Storage::drop cleans up
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn multiple_types_independent() {
        let mut builder = WorldBuilder::new();
        let price_id = builder.register::<Price>(Price { value: 10.0 });
        let venue_id = builder.register::<Venue>(Venue { name: "CB" });
        let config_id = builder.register::<Config>(Config { max_orders: 500 });
        let world = builder.build();

        unsafe {
            assert_eq!(world.get::<Price>(price_id).value, 10.0);
            assert_eq!(world.get::<Venue>(venue_id).name, "CB");
            assert_eq!(world.get::<Config>(config_id).max_orders, 500);
        }
    }

    #[test]
    fn contains_reflects_registration() {
        let mut builder = WorldBuilder::new();
        assert!(!builder.contains::<Price>());

        builder.register::<Price>(Price { value: 0.0 });
        assert!(builder.contains::<Price>());
        assert!(!builder.contains::<Venue>());

        let world = builder.build();
        assert!(world.contains::<Price>());
        assert!(!world.contains::<Venue>());
    }

    #[test]
    fn get_ptr_returns_valid_pointer() {
        let mut builder = WorldBuilder::new();
        builder.register::<Price>(Price { value: 77.7 });
        let world = builder.build();

        let id = world.id::<Price>();
        unsafe {
            let ptr = world.get_ptr(id);
            let price = &*(ptr as *const Price);
            assert_eq!(price.value, 77.7);
        }
    }

    #[test]
    fn send_to_another_thread() {
        let mut builder = WorldBuilder::new();
        builder.register::<Price>(Price { value: 55.5 });
        let world = builder.build();

        let handle = std::thread::spawn(move || {
            let id = world.id::<Price>();
            // SAFETY: sole owner on this thread, no aliasing.
            unsafe { world.get::<Price>(id).value }
        });
        assert_eq!(handle.join().unwrap(), 55.5);
    }

    #[test]
    fn registry_accessible_from_builder() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);

        let registry = builder.registry();
        assert!(registry.contains::<u64>());
        assert!(!registry.contains::<bool>());

        let id = registry.id::<u64>();
        assert_eq!(id, ResourceId(0));
    }

    #[test]
    fn registry_accessible_from_world() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);
        let world = builder.build();

        let registry = world.registry();
        assert!(registry.contains::<u64>());

        // Registry from world and world.id() agree.
        assert_eq!(registry.id::<u64>(), world.id::<u64>());
    }

    // -- Safe accessor tests --------------------------------------------------

    #[test]
    fn resource_reads_value() {
        let mut builder = WorldBuilder::new();
        builder.register::<Price>(Price { value: 42.5 });
        let world = builder.build();

        assert_eq!(world.resource::<Price>().value, 42.5);
    }

    #[test]
    fn resource_mut_modifies_value() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        *world.resource_mut::<u64>() = 99;
        assert_eq!(*world.resource::<u64>(), 99);
    }

    #[test]
    fn register_default_works() {
        let mut builder = WorldBuilder::new();
        let id = builder.register_default::<Vec<u32>>();
        let world = builder.build();

        assert_eq!(id, world.id::<Vec<u32>>());
        let v = world.resource::<Vec<u32>>();
        assert!(v.is_empty());
    }

    #[test]
    fn ensure_registers_new_type() {
        let mut builder = WorldBuilder::new();
        let id = builder.ensure::<u64>(42);
        let world = builder.build();

        assert_eq!(id, world.id::<u64>());
        assert_eq!(*world.resource::<u64>(), 42);
    }

    #[test]
    fn ensure_returns_existing_id() {
        let mut builder = WorldBuilder::new();
        let id1 = builder.register::<u64>(42);
        let id2 = builder.ensure::<u64>(99);
        assert_eq!(id1, id2);

        // Original value preserved, new value dropped.
        let world = builder.build();
        assert_eq!(*world.resource::<u64>(), 42);
    }

    #[test]
    fn ensure_default_registers_new_type() {
        let mut builder = WorldBuilder::new();
        let id = builder.ensure_default::<Vec<u32>>();
        let world = builder.build();

        assert_eq!(id, world.id::<Vec<u32>>());
        assert!(world.resource::<Vec<u32>>().is_empty());
    }

    #[test]
    fn ensure_default_returns_existing_id() {
        let mut builder = WorldBuilder::new();
        builder.register::<Vec<u32>>(vec![1, 2, 3]);
        let id = builder.ensure_default::<Vec<u32>>();
        let world = builder.build();

        assert_eq!(id, world.id::<Vec<u32>>());
        // Original value preserved.
        assert_eq!(*world.resource::<Vec<u32>>(), vec![1, 2, 3]);
    }

    // -- Sequence / change detection tests ----------------------------------------

    #[test]
    fn sequence_default_is_zero() {
        assert_eq!(Sequence::default(), Sequence(0));
    }

    #[test]
    fn next_sequence_increments() {
        let mut world = WorldBuilder::new().build();
        assert_eq!(world.current_sequence(), Sequence(0));
        world.next_sequence();
        assert_eq!(world.current_sequence(), Sequence(1));
        world.next_sequence();
        assert_eq!(world.current_sequence(), Sequence(2));
    }

    #[test]
    fn resource_registered_at_current_sequence() {
        // Resources registered at build time get changed_at=Sequence(0).
        // World starts at current_sequence=Sequence(0). So they match — "changed."
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);
        let world = builder.build();

        let id = world.id::<u64>();
        unsafe {
            assert_eq!(world.changed_at(id), Sequence(0));
            assert_eq!(world.current_sequence(), Sequence(0));
            // changed_at == current_sequence → "changed"
            assert_eq!(world.changed_at(id), world.current_sequence());
        }
    }

    #[test]
    fn resource_mut_stamps_changed_at() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        world.next_sequence(); // tick=1
        let id = world.id::<u64>();

        // changed_at is still 0, current_sequence is 1 → not changed
        unsafe {
            assert_eq!(world.changed_at(id), Sequence(0));
        }

        // resource_mut stamps changed_at to current_sequence
        *world.resource_mut::<u64>() = 99;
        unsafe {
            assert_eq!(world.changed_at(id), Sequence(1));
        }
    }

    // -- run_startup tests ----------------------------------------------------

    #[test]
    fn run_startup_dispatches_handler() {
        use crate::ResMut;

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        builder.register::<bool>(false);
        let mut world = builder.build();

        fn init(mut counter: ResMut<u64>, mut flag: ResMut<bool>, _event: ()) {
            *counter = 42;
            *flag = true;
        }

        world.run_startup(init);

        assert_eq!(*world.resource::<u64>(), 42);
        assert!(*world.resource::<bool>());
    }

    #[test]
    fn run_startup_multiple_phases() {
        use crate::ResMut;

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn phase1(mut counter: ResMut<u64>, _event: ()) {
            *counter += 10;
        }

        fn phase2(mut counter: ResMut<u64>, _event: ()) {
            *counter += 5;
        }

        world.run_startup(phase1);
        world.run_startup(phase2);

        assert_eq!(*world.resource::<u64>(), 15);
    }

    // -- Plugin / Driver tests ------------------------------------------------

    #[test]
    fn plugin_registers_resources() {
        struct TestPlugin;

        impl crate::plugin::Plugin for TestPlugin {
            fn build(self, world: &mut WorldBuilder) {
                world.register::<u64>(42);
                world.register::<bool>(true);
            }
        }

        let mut builder = WorldBuilder::new();
        builder.install_plugin(TestPlugin);
        let world = builder.build();

        assert_eq!(*world.resource::<u64>(), 42);
        assert_eq!(*world.resource::<bool>(), true);
    }

    #[test]
    fn driver_installs_and_returns_handle() {
        struct TestInstaller;
        struct TestHandle {
            counter_id: ResourceId,
        }

        impl crate::driver::Installer for TestInstaller {
            type Poller = TestHandle;

            fn install(self, world: &mut WorldBuilder) -> TestHandle {
                let counter_id = world.register::<u64>(0);
                TestHandle { counter_id }
            }
        }

        let mut builder = WorldBuilder::new();
        let handle = builder.install_driver(TestInstaller);
        let world = builder.build();

        // Handle's pre-resolved ID can access the resource.
        unsafe {
            assert_eq!(*world.get::<u64>(handle.counter_id), 0);
        }
    }

    // -- check_access slow path (>128 resources) ------------------------------

    #[test]
    fn check_access_slow_path_no_conflict() {
        // Register 130 distinct types to force the slow path (>128).
        macro_rules! register_many {
            ($builder:expr, $($i:literal),* $(,)?) => {
                $(
                    $builder.register::<[u8; $i]>([0u8; $i]);
                )*
            };
        }

        let mut builder = WorldBuilder::new();
        register_many!(
            builder, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
            23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
            45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66,
            67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88,
            89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107,
            108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124,
            125, 126, 127, 128, 129, 130
        );
        assert!(builder.len() > 128);

        // Non-conflicting accesses at high indices — exercises slow path.
        let accesses = [(Some(ResourceId(0)), "a"), (Some(ResourceId(129)), "b")];
        builder.registry_mut().check_access(&accesses);
    }

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn check_access_slow_path_detects_conflict() {
        macro_rules! register_many {
            ($builder:expr, $($i:literal),* $(,)?) => {
                $(
                    $builder.register::<[u8; $i]>([0u8; $i]);
                )*
            };
        }

        let mut builder = WorldBuilder::new();
        register_many!(
            builder, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
            23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
            45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66,
            67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88,
            89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107,
            108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124,
            125, 126, 127, 128, 129, 130
        );

        // Duplicate access at index 129 — must panic.
        let accesses = [(Some(ResourceId(129)), "a"), (Some(ResourceId(129)), "b")];
        builder.registry_mut().check_access(&accesses);
    }

    #[test]
    fn sequence_wrapping() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        // Advance to MAX.
        world.current_sequence = Sequence(u64::MAX);
        assert_eq!(world.current_sequence(), Sequence(u64::MAX));

        // Stamp resource at MAX.
        *world.resource_mut::<u64>() = 99;
        let id = world.id::<u64>();
        unsafe {
            assert_eq!(world.changed_at(id), Sequence(u64::MAX));
        }

        // Wrap to 0.
        let seq = world.next_sequence();
        assert_eq!(seq, Sequence(0));
        assert_eq!(world.current_sequence(), Sequence(0));

        // Resource changed at MAX, current is 0 → not changed.
        unsafe {
            assert_ne!(world.changed_at(id), world.current_sequence());
        }
    }
}
