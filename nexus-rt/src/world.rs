//! Type-erased singleton resource storage.
//!
//! [`World`] is a unified store where each resource type gets a direct pointer
//! ([`ResourceId`]) for O(1) dispatch-time access. Registration happens through
//! [`WorldBuilder`], which freezes into an immutable [`World`] container via
//! [`build()`](WorldBuilder::build).
//!
//! The type [`Registry`] maps types to [`ResourceId`] pointers. It is shared
//! between [`WorldBuilder`] and [`World`], and is passed to [`Param::init`] and
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
use std::cell::Cell;
#[cfg(debug_assertions)]
use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;

use rustc_hash::FxHashMap;

// =============================================================================
// Debug-mode aliasing detection
// =============================================================================

/// Tracks resource accesses within a single Param::fetch phase to detect
/// aliasing violations at runtime in debug builds.
///
/// Dispatch macros call [`World::clear_borrows`] then
/// [`World::track_borrow`] for each resource fetched. If the same resource
/// is fetched twice within a phase, we panic with a diagnostic. This catches
/// framework bugs where two params in the same handler resolve to the same
/// resource — something [`Registry::check_access`] catches at construction
/// time, but this catches dynamically for dispatch paths (like [`Opaque`](crate::Opaque)
/// closures) that bypass static analysis.
///
/// Only active during the narrow `Param::fetch` window — safe API methods
/// are not tracked.
///
/// Completely compiled out in release builds — zero bytes, zero branches.
#[cfg(debug_assertions)]
pub(crate) struct BorrowTracker {
    /// Pointer addresses accessed in current phase.
    /// Uses `UnsafeCell` for interior mutability because `Param::fetch` /
    /// `World::track_borrow` operate on `&World`. Single-threaded,
    /// non-reentrant access only.
    accessed: UnsafeCell<Vec<NonNull<u8>>>,
}

#[cfg(debug_assertions)]
impl BorrowTracker {
    fn new() -> Self {
        Self {
            accessed: UnsafeCell::new(Vec::new()),
        }
    }

    /// Reset all tracking state. Called before each `Param::fetch` phase.
    fn clear(&self) {
        // SAFETY: single-threaded, non-reentrant. No other reference to
        // the inner Vec exists during this call.
        let ptrs = unsafe { &mut *self.accessed.get() };
        ptrs.clear();
    }

    /// Record an access. Panics if already accessed in this phase.
    fn track(&self, id: ResourceId) {
        // SAFETY: single-threaded, non-reentrant. No other reference to
        // the inner Vec exists during this call.
        let ptrs = unsafe { &mut *self.accessed.get() };
        assert!(
            !ptrs.contains(&id.0),
            "conflicting access: resource {id} was accessed by more than one parameter \
             in the same dispatch phase",
        );
        ptrs.push(id.0);
    }
}

// =============================================================================
// Core types
// =============================================================================

/// Direct pointer identifying a resource within a [`World`] container.
///
/// Points to a heap-allocated `ResourceCell<T>`. Dispatch-time access is
/// a single deref — no index lookup, no Vec indirection.
///
/// Obtained from [`WorldBuilder::register`], [`WorldBuilder::ensure`],
/// [`Registry::id`], [`World::id`], or their `try_` / `_default` variants.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ResourceId(NonNull<u8>);

impl ResourceId {
    fn as_ptr(self) -> *mut u8 {
        self.0.as_ptr()
    }
}

// SAFETY: `ResourceId` is a thin, copyable handle to a `ResourceCell<T>`
// allocated and pinned for the lifetime of its `World`:
// - every `ResourceCell<T>` is registered with `T: Send`, so the pointee is
//   safe to send between threads,
// - the underlying pointer is stable for the `World`'s entire lifetime, and
// - a `ResourceId` cannot be dereferenced without going through `World`,
//   which enforces the single-threaded dispatch / aliasing invariants.
unsafe impl Send for ResourceId {}

impl std::fmt::Display for ResourceId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:p}", self.0)
    }
}

/// Monotonic event sequence number for event ordering.
///
/// Each event processed by a driver is assigned a unique sequence number
/// via [`World::next_sequence`]. Handlers can read the current sequence
/// via [`Seq`](crate::Seq) or advance it via [`SeqMut`](crate::SeqMut).
///
/// Uses `i64` for wire-format compatibility (FIX/SBE, Protobuf, Avro
/// all have native signed 64-bit; unsigned is awkward or absent) and to
/// support sentinel values ([`NULL`](Self::NULL),
/// [`UNINITIALIZED`](Self::UNINITIALIZED)) without `Option` overhead.
///
/// Wrapping is harmless — at one increment per event, the positive `i64`
/// space takes ~292 years at 1 GHz to exhaust.
///
/// # Sentinels
///
/// | Constant | Value | Meaning |
/// |----------|-------|---------|
/// | [`NULL`](Self::NULL) | `i64::MIN` | No sequence exists (SBE null convention) |
/// | [`UNINITIALIZED`](Self::UNINITIALIZED) | `-1` | Not yet assigned |
/// | [`ZERO`](Self::ZERO) | `0` | Starting point before any events |
///
/// # Examples
///
/// ```
/// use nexus_rt::Sequence;
///
/// let a = Sequence::ZERO;
/// let b = a.next();
///
/// assert!(b > a);
/// assert_eq!(b.as_i64(), 1);
/// assert_eq!(b.elapsed_since(a), 1);
///
/// assert!(Sequence::NULL.is_null());
/// assert!(!Sequence::ZERO.is_null());
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Sequence(pub(crate) i64);

impl Sequence {
    /// SBE-compatible null — `i64::MIN`. Indicates no sequence exists.
    ///
    /// Maps directly to the SBE int64 null sentinel on the wire.
    pub const NULL: Self = Self(i64::MIN);

    /// Uninitialized sentinel — `-1`. Indicates a sequence has not yet
    /// been assigned.
    pub const UNINITIALIZED: Self = Self(-1);

    /// The zero sequence — the starting point before any events.
    pub const ZERO: Self = Self(0);

    /// Create a sequence from a raw `i64` value.
    ///
    /// Use for construction in tests, deserialization, or replay.
    pub const fn new(value: i64) -> Self {
        Self(value)
    }

    /// Create a sequence from a raw `i64` value.
    ///
    /// Symmetric with [`as_i64`](Self::as_i64). Use for wire protocol
    /// deserialization.
    pub const fn from_i64(value: i64) -> Self {
        Self(value)
    }

    /// Returns the raw `i64` value.
    ///
    /// Use for logging, metrics, serialization, or passing to external
    /// systems.
    pub const fn as_i64(self) -> i64 {
        self.0
    }

    /// Returns `true` if this is the [`NULL`](Self::NULL) sentinel.
    pub const fn is_null(self) -> bool {
        self.0 == i64::MIN
    }

    /// Returns `true` if this is the [`UNINITIALIZED`](Self::UNINITIALIZED) sentinel.
    pub const fn is_uninitialized(self) -> bool {
        self.0 == -1
    }

    /// Returns the next sequence number (wrapping).
    ///
    /// This is a pure computation — it does not advance any world state.
    /// Use [`World::next_sequence`] to actually advance the world's
    /// current sequence.
    pub const fn next(self) -> Self {
        Self(self.0.wrapping_add(1))
    }

    /// Returns the number of events between `earlier` and `self`.
    ///
    /// Wrapping-aware: if `self` has wrapped past `earlier`, the result
    /// is the wrapping distance. Returns 0 if `self == earlier`.
    pub const fn elapsed_since(self, earlier: Self) -> i64 {
        self.0.wrapping_sub(earlier.0)
    }
}

impl std::fmt::Display for Sequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Heap-allocated wrapper for a single resource value.
///
/// Resources are individually heap-allocated via `Box::new(ResourceCell { value })`.
/// The `ResourceId` is the raw pointer to this cell — a single deref to reach
/// the value with zero framework overhead.
pub(crate) struct ResourceCell<T> {
    pub(crate) value: T,
}

/// Reconstruct and drop a `Box<ResourceCell<T>>` from a raw pointer.
///
/// # Safety
///
/// `ptr` must have been produced by `Box::into_raw(Box::new(ResourceCell { .. }))`
/// where the value field is `T`. Must only be called once per pointer.
unsafe fn drop_resource<T>(ptr: *mut u8) {
    // SAFETY: ptr was produced by Box::into_raw(Box::new(ResourceCell { .. }))
    // where value: T. Called exactly once in Storage::drop.
    unsafe {
        let _ = Box::from_raw(ptr as *mut ResourceCell<T>);
    }
}

// =============================================================================
// Registry — type-to-pointer mapping
// =============================================================================

/// Type-to-pointer mapping shared between [`WorldBuilder`] and [`World`].
///
/// Contains only the type registry — no storage backing. Passed to
/// [`IntoHandler::into_handler`](crate::IntoHandler::into_handler) and
/// [`Param::init`](crate::Param::init) so handlers can resolve
/// [`ResourceId`]s during driver setup.
///
/// Obtained via [`WorldBuilder::registry()`] or [`World::registry()`].
pub struct Registry {
    indices: FxHashMap<TypeId, ResourceId>,
}

impl Registry {
    pub(crate) fn new() -> Self {
        Self {
            indices: FxHashMap::default(),
        }
    }

    /// Resolve the [`ResourceId`] for a type. Cold path — uses HashMap lookup.
    ///
    /// # Panics
    ///
    /// Panics if the resource type was not registered.
    pub fn id<T: Resource>(&self) -> ResourceId {
        *self
            .indices
            .get(&TypeId::of::<T>())
            .unwrap_or_else(|| {
                panic!(
                    "resource `{}` not registered — call WorldBuilder::register::<{}>(initial_value) during setup",
                    type_name::<T>(),
                    type_name::<T>()
                )
            })
    }

    /// Try to resolve the [`ResourceId`] for a type. Returns `None` if the
    /// type was not registered.
    pub fn try_id<T: Resource>(&self) -> Option<ResourceId> {
        self.indices.get(&TypeId::of::<T>()).copied()
    }

    /// Returns `true` if a resource of type `T` has been registered.
    pub fn contains<T: Resource>(&self) -> bool {
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
    /// Two accesses conflict when they target the same ResourceId (same
    /// pointer). O(n²) pairwise comparison — handler arity is 1-8, so
    /// this is trivially fast at build time.
    ///
    /// # Panics
    ///
    /// Panics if any resource is accessed by more than one parameter.
    #[cold]
    pub fn check_access(&self, accesses: &[(Option<ResourceId>, &str)]) {
        for i in 0..accesses.len() {
            let Some(id_i) = accesses[i].0 else { continue };
            for j in (i + 1)..accesses.len() {
                let Some(id_j) = accesses[j].0 else { continue };
                assert!(
                    id_i != id_j,
                    "conflicting access: resource borrowed by `{}` conflicts with \
                     resource borrowed by `{}` in the same handler",
                    accesses[j].1,
                    accesses[i].1,
                );
            }
        }
    }
}

// =============================================================================
// Storage — shared backing between builder and frozen container
// =============================================================================

/// Pointer + type-erased drop function for a single resource.
struct DropEntry {
    ptr: *mut u8,
    drop_fn: unsafe fn(*mut u8),
}

/// Internal storage for type-erased resource cleanup.
///
/// Only walked during [`World::drop`] — no dispatch-time role. The actual
/// resource data lives in individually heap-allocated `ResourceCell<T>`
/// values, pointed to by [`ResourceId`].
pub(crate) struct Storage {
    drop_entries: Vec<DropEntry>,
}

impl Storage {
    pub(crate) fn new() -> Self {
        Self {
            drop_entries: Vec::new(),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.drop_entries.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.drop_entries.is_empty()
    }
}

// SAFETY: All values stored in Storage were registered via `register<T: Send + 'static>`,
// so every concrete type behind the raw pointers is Send. Storage exclusively owns
// these heap allocations — they are not aliased or shared. Transferring ownership
// to another thread is safe.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl Send for Storage {}

impl Drop for Storage {
    fn drop(&mut self) {
        for entry in &self.drop_entries {
            // SAFETY: each DropEntry was created in WorldBuilder::register().
            // drop_fn is the monomorphized destructor for the concrete
            // ResourceCell<T> behind ptr. Called exactly once here.
            unsafe {
                (entry.drop_fn)(entry.ptr);
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
/// direct [`ResourceId`] pointer.
///
/// The [`registry()`](Self::registry) method exposes the type-to-pointer mapping
/// so that drivers can resolve handlers against the builder before `build()`.
///
/// # Examples
///
/// ```
/// use nexus_rt::{WorldBuilder, Resource};
///
/// #[derive(Resource)]
/// struct Counter(u64);
/// #[derive(Resource)]
/// struct Flag(bool);
///
/// let mut builder = WorldBuilder::new();
/// let id = builder.register(Counter(42));
/// builder.register(Flag(true));
/// let world = builder.build();
///
/// unsafe {
///     assert_eq!(world.get::<Counter>(id).0, 42);
/// }
/// ```
pub struct WorldBuilder {
    registry: Registry,
    storage: Storage,
}

/// Marker trait for types that can be stored in a [`World`].
///
/// Requires `Send + 'static`. Use `#[derive(Resource)]` to implement,
/// or [`new_resource!`](crate::new_resource) for newtype wrappers.
///
/// ```
/// use nexus_rt::Resource;
///
/// #[derive(Resource)]
/// struct OrderBook {
///     bids: Vec<(f64, f64)>,
///     asks: Vec<(f64, f64)>,
/// }
/// ```
///
/// # Why not just `Send + 'static`?
///
/// Without the marker trait, two modules can independently register
/// `u64` and silently collide. The `Resource` bound forces a newtype,
/// making collisions a compile error.
#[diagnostic::on_unimplemented(
    message = "this type cannot be stored as a resource in the World",
    note = "add `#[derive(Resource)]` to your type, or use `new_resource!` for a newtype wrapper"
)]
pub trait Resource: Send + 'static {}

// Test-only impls for primitive types used in unit tests within this crate.
// NOT available to external crates — they should use #[derive(Resource)] or new_resource!.
#[cfg(test)]
mod resource_test_impls {
    use super::Resource;
    impl Resource for bool {}
    impl Resource for u32 {}
    impl Resource for u64 {}
    impl Resource for i64 {}
    impl Resource for f64 {}
    impl Resource for String {}
    impl<T: Send + 'static> Resource for Vec<T> {}
    impl<T: Send + Sync + 'static> Resource for std::sync::Arc<T> {}
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
    /// The value is heap-allocated inside a `ResourceCell<T>` and ownership
    /// is transferred to the container. The pointer is stable for the
    /// lifetime of the resulting [`World`].
    ///
    /// # Panics
    ///
    /// Panics if a resource of the same type is already registered.
    #[cold]
    pub fn register<T: Resource>(&mut self, value: T) -> ResourceId {
        let type_id = TypeId::of::<T>();
        assert!(
            !self.registry.indices.contains_key(&type_id),
            "resource `{}` already registered",
            type_name::<T>(),
        );

        let cell = Box::new(ResourceCell { value });
        let raw = Box::into_raw(cell) as *mut u8;
        // SAFETY: Box::into_raw never returns null.
        let ptr = unsafe { NonNull::new_unchecked(raw) };
        let id = ResourceId(ptr);
        self.registry.indices.insert(type_id, id);
        self.storage.drop_entries.push(DropEntry {
            ptr: raw,
            drop_fn: drop_resource::<T>,
        });
        id
    }

    /// Register a resource using its [`Default`] value and return its
    /// [`ResourceId`].
    ///
    /// Equivalent to `self.register::<T>(T::default())`.
    #[cold]
    pub fn register_default<T: Default + Resource>(&mut self) -> ResourceId {
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
    pub fn ensure<T: Resource>(&mut self, value: T) -> ResourceId {
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
    pub fn ensure_default<T: Default + Resource>(&mut self) -> ResourceId {
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
    /// [`into_step`](crate::pipeline::IntoStep::into_step).
    pub fn registry(&self) -> &Registry {
        &self.registry
    }

    /// Returns a mutable reference to the type registry.
    ///
    /// Rarely needed — [`registry()`](Self::registry) suffices for
    /// construction-time calls. Exists for direct mutation of the
    /// registry if needed.
    #[allow(dead_code)]
    pub(crate) fn registry_mut(&mut self) -> &mut Registry {
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
    pub fn contains<T: Resource>(&self) -> bool {
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
    ///
    /// When the `reactors` feature is enabled, `ReactorNotify`,
    /// `DeferredRemovals`, and
    /// `SourceRegistry` are automatically registered
    /// if not already present.
    #[allow(unused_mut)]
    pub fn build(mut self) -> World {
        #[cfg(feature = "reactors")]
        let (reactor_notify_id, reactor_removals_id) = {
            self.ensure(crate::reactor::ReactorNotify::new(16, 64));
            self.ensure(crate::reactor::DeferredRemovals::default());
            self.ensure(crate::reactor::SourceRegistry::new());
            (
                self.registry.id::<crate::reactor::ReactorNotify>(),
                self.registry.id::<crate::reactor::DeferredRemovals>(),
            )
        };

        World {
            registry: self.registry,
            storage: self.storage,
            current_sequence: Cell::new(Sequence(0)),
            shutdown: Arc::new(AtomicBool::new(false)),
            _not_sync: PhantomData,
            #[cfg(feature = "reactors")]
            reactor_notify_id,
            #[cfg(feature = "reactors")]
            reactor_removals_id,
            #[cfg(feature = "reactors")]
            reactor_events: Some(nexus_notify::Events::with_capacity(256)),
            #[cfg(debug_assertions)]
            borrow_tracker: BorrowTracker::new(),
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
/// Created by [`WorldBuilder::build()`]. Resources are accessed via
/// [`ResourceId`] direct pointers for O(1) dispatch-time access — a single
/// pointer deref per fetch, zero framework overhead.
///
/// # Safe API
///
/// - [`resource`](Self::resource) / [`resource_mut`](Self::resource_mut) —
///   cold-path access via HashMap lookup.
///
/// # Unsafe API (framework internals)
///
/// The low-level `get` / `get_mut` methods are `unsafe` — used by
/// [`Param::fetch`](crate::Param) for zero-overhead dispatch.
/// The caller must ensure no mutable aliasing.
pub struct World {
    /// Type-to-pointer mapping. Same registry used during build.
    registry: Registry,
    /// Type-erased pointer storage. Drop handled by `Storage`.
    storage: Storage,
    /// Current sequence number. `Cell` so handlers can advance it
    /// through `&World` via [`SeqMut`](crate::SeqMut).
    current_sequence: Cell<Sequence>,
    /// Cooperative shutdown flag. Shared with [`ShutdownHandle`](crate::ShutdownHandle)
    /// via `Arc`. Handlers access it through the [`Shutdown`](crate::Shutdown) Param.
    shutdown: Arc<AtomicBool>,
    /// World must not be shared across threads — it holds interior-mutable
    /// `Cell<Sequence>` values accessed through `&self`. `!Sync` enforced by
    /// `PhantomData<Cell<()>>`.
    _not_sync: PhantomData<Cell<()>>,
    /// Pre-resolved pointer to ReactorNotify for O(1) reactor operations.
    #[cfg(feature = "reactors")]
    reactor_notify_id: ResourceId,
    /// Pre-resolved pointer to DeferredRemovals (avoids HashMap lookup per frame).
    #[cfg(feature = "reactors")]
    reactor_removals_id: ResourceId,
    /// Pre-allocated events buffer for dispatch (avoids allocation per frame).
    #[cfg(feature = "reactors")]
    reactor_events: Option<nexus_notify::Events>,
    /// Debug-only aliasing tracker. Detects duplicate resource access within
    /// a single dispatch phase. Compiled out entirely in release builds.
    #[cfg(debug_assertions)]
    borrow_tracker: BorrowTracker,
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
    #[allow(dead_code)]
    pub(crate) fn registry_mut(&mut self) -> &mut Registry {
        &mut self.registry
    }

    /// Resolve the [`ResourceId`] for a type. Cold path — uses HashMap lookup.
    ///
    /// # Panics
    ///
    /// Panics if the resource type was not registered.
    pub fn id<T: Resource>(&self) -> ResourceId {
        self.registry.id::<T>()
    }

    /// Try to resolve the [`ResourceId`] for a type. Returns `None` if the
    /// type was not registered.
    pub fn try_id<T: Resource>(&self) -> Option<ResourceId> {
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
    pub fn contains<T: Resource>(&self) -> bool {
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
    pub fn resource<T: Resource>(&self) -> &T {
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
    pub fn resource_mut<T: Resource>(&mut self) -> &mut T {
        let id = self.registry.id::<T>();
        // SAFETY: id resolved from our own registry. &mut self ensures
        // exclusive access — no other references can exist.
        unsafe { self.get_mut(id) }
    }

    // =========================================================================
    // One-shot dispatch
    // =========================================================================

    /// Run a system once with full Param resolution.
    ///
    /// Intended for one-shot initialization after [`build()`](WorldBuilder::build).
    /// Accepts both void-returning (`fn(params...)`) and bool-returning
    /// (`fn(params...) -> bool`) functions via [`IntoSystem`](crate::IntoSystem).
    /// The return value is always ignored — startup has no DAG to
    /// propagate through. Named functions only (same closure limitation
    /// as [`IntoHandler`](crate::IntoHandler)).
    ///
    /// Can be called multiple times for phased initialization.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// fn startup(
    ///     mut driver: ResMut<MioDriver>,
    ///     mut listener: ResMut<Listener>,
    /// ) {
    ///     // wire drivers to IO sources...
    /// }
    ///
    /// let mut world = wb.build();
    /// world.run_startup(startup);
    /// ```
    pub fn run_startup<F, Params, M>(&mut self, f: F)
    where
        F: crate::IntoSystem<Params, M>,
    {
        use crate::System;
        let mut sys = f.into_system(&self.registry);
        sys.run(self);
    }

    // =========================================================================
    // Shutdown
    // =========================================================================

    /// Returns a [`ShutdownHandle`](crate::shutdown::ShutdownHandle)
    /// sharing the same flag as the world's shutdown state.
    ///
    /// The handle is owned by the event loop and checked each iteration.
    /// Handlers trigger shutdown via the [`Shutdown`](crate::Shutdown) Param.
    pub fn shutdown_handle(&self) -> crate::shutdown::ShutdownHandle {
        crate::shutdown::ShutdownHandle::new(Arc::clone(&self.shutdown))
    }

    /// Returns a reference to the shutdown flag.
    ///
    /// Used by the [`Shutdown`](crate::Shutdown) Param for direct access.
    pub(crate) fn shutdown_flag(&self) -> &AtomicBool {
        &self.shutdown
    }

    /// Run the event loop until shutdown is triggered.
    ///
    /// The closure receives `&mut World` and defines one iteration of
    /// the poll loop — which drivers to poll, in what order, with what
    /// timeout. The loop exits when a handler calls
    /// [`Shutdown::trigger`](crate::Shutdown::trigger) or
    /// an external signal flips the flag (see
    /// `ShutdownHandle::enable_signals` (requires `signals` feature)).
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let mut world = wb.build();
    /// world.run_startup(startup);
    ///
    /// world.run(|world| {
    ///     let now = Instant::now();
    ///     let timeout = timer.next_deadline(world)
    ///         .map(|d| d.saturating_duration_since(now));
    ///     mio.poll(world, timeout).expect("mio poll");
    ///     timer.poll(world, now);
    /// });
    /// ```
    pub fn run(&mut self, mut f: impl FnMut(&mut World)) {
        while !self.shutdown.load(std::sync::atomic::Ordering::Relaxed) {
            f(self);
        }
    }

    // =========================================================================
    // Sequence
    // =========================================================================

    /// Returns the current event sequence number.
    pub fn current_sequence(&self) -> Sequence {
        self.current_sequence.get()
    }

    /// Advance to the next event sequence number and return it.
    ///
    /// Drivers call this before dispatching each event. The returned
    /// sequence number identifies the event being processed.
    pub fn next_sequence(&mut self) -> Sequence {
        let next = Sequence(self.current_sequence.get().0.wrapping_add(1));
        self.current_sequence.set(next);
        next
    }

    /// Returns a reference to the sequence `Cell`.
    ///
    /// Used by [`SeqMut`](crate::SeqMut) Param for direct access.
    pub(crate) fn sequence_cell(&self) -> &Cell<Sequence> {
        &self.current_sequence
    }

    /// Set the current sequence number directly.
    ///
    /// Use for recovery / replay — restores the sequence to a known
    /// checkpoint so that subsequent `next_sequence` calls continue
    /// from the right point.
    pub fn set_sequence(&mut self, seq: Sequence) {
        self.current_sequence.set(seq);
    }

    /// Resets the current sequence number to 0.
    pub fn reset_sequence(&mut self) {
        self.current_sequence.set(Sequence::ZERO);
    }

    // =========================================================================
    // Unsafe resource access (hot path — pre-resolved ResourceId)
    // =========================================================================

    /// Fetch a shared reference to a resource by direct pointer.
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
        // builder that produced this container. T matches the registered type.
        // No mutable alias exists. ResourceId points to a valid ResourceCell<T>.
        unsafe { &(*(id.as_ptr() as *const ResourceCell<T>)).value }
    }

    /// Fetch a mutable reference to a resource by direct pointer.
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
        // builder that produced this container. T matches the registered type.
        // No aliases exist. ResourceId points to a valid ResourceCell<T>.
        unsafe { &mut (*(id.as_ptr() as *mut ResourceCell<T>)).value }
    }

    /// Reset borrow tracking for a new dispatch phase.
    ///
    /// Called before each [`Param::fetch`](crate::Param::fetch) in dispatch
    /// macros. Only exists in debug builds.
    #[cfg(debug_assertions)]
    pub(crate) fn clear_borrows(&self) {
        self.borrow_tracker.clear();
    }

    /// Record a resource access in the debug borrow tracker.
    ///
    /// Called by [`Param::fetch`](crate::Param::fetch) impls for each
    /// resource parameter. Panics if the resource was already accessed
    /// in the current phase (since the last [`clear_borrows`](Self::clear_borrows)).
    /// Only exists in debug builds.
    #[cfg(debug_assertions)]
    pub(crate) fn track_borrow(&self, id: ResourceId) {
        self.borrow_tracker.track(id);
    }

    // =========================================================================
    // Reactor convenience methods (behind `reactors` feature)
    // =========================================================================

    /// Register a new data source for reactor subscriptions.
    ///
    /// Convenience for `world.resource_mut::<ReactorNotify>().register_source()`.
    #[cfg(feature = "reactors")]
    pub fn register_source(&mut self) -> crate::reactor::DataSource {
        self.resource_mut::<crate::reactor::ReactorNotify>()
            .register_source()
    }

    /// Create and register a reactor from a step function + context factory.
    ///
    /// The closure receives the assigned [`Token`](nexus_notify::Token) so
    /// the reactor can store it for wire routing or self-deregistration.
    /// Params are resolved from the internal registry — single pointer
    /// deref at dispatch time.
    ///
    /// This is the primary registration API. It handles the borrow
    /// juggling internally: allocates the token, resolves params from
    /// the registry, and inserts the reactor — all in one call.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let src = world.register_source();
    /// world.spawn_reactor(
    ///     |id| QuotingCtx { reactor_id: id, instrument: BTC, layer: 1 },
    ///     quoting_step,
    /// ).subscribe(src);
    /// ```
    #[cfg(feature = "reactors")]
    pub fn spawn_reactor<C, Params, F: crate::reactor::IntoReactor<C, Params>>(
        &mut self,
        ctx_fn: impl FnOnce(nexus_notify::Token) -> C,
        step: F,
    ) -> crate::reactor::ReactorRegistration<'_> {
        // SAFETY: reactor_notify_id was resolved during build() from the same
        // WorldBuilder. ReactorNotify is heap-allocated via ResourceCell —
        // the pointer is stable for World's lifetime. We access it via raw
        // pointer to simultaneously read the registry (disjoint: registry is
        // an inline field, ReactorNotify is on the heap). &mut self guarantees
        // no other references to any World resource exist.
        let notify_ptr: *mut crate::reactor::ReactorNotify =
            unsafe { self.get_mut::<crate::reactor::ReactorNotify>(self.reactor_notify_id) };
        // SAFETY: notify_ptr is stable (heap-allocated ResourceCell).
        // No other references exist — previous &mut was not retained.
        let token = unsafe { &mut *notify_ptr }.create_reactor();
        let ctx = ctx_fn(token);
        let reactor = step.into_reactor(ctx, &self.registry);
        // SAFETY: notify_ptr is stable (heap-allocated ResourceCell).
        // No other references exist — ctx_fn and into_reactor don't alias.
        let notify = unsafe { &mut *notify_ptr };
        notify.insert_reactor(token, reactor)
    }

    /// Register a pre-built reactor in one step.
    ///
    /// For reactors that don't need their token in the context, or for
    /// [`PipelineReactor`](crate::PipelineReactor) instances.
    #[cfg(feature = "reactors")]
    pub fn spawn_built_reactor(
        &mut self,
        reactor: impl crate::reactor::Reactor + 'static,
    ) -> crate::reactor::ReactorRegistration<'_> {
        // SAFETY: reactor_notify_id was resolved during build() from the
        // same WorldBuilder. &mut self guarantees exclusive access.
        let notify =
            unsafe { self.get_mut::<crate::reactor::ReactorNotify>(self.reactor_notify_id) };
        notify.register_built(reactor)
    }

    /// Dispatch all woken reactors and process deferred removals.
    ///
    /// Call this post-frame after event handlers have called
    /// [`ReactorNotify::mark`](crate::ReactorNotify::mark).
    /// Returns `true` if any reactor ran.
    #[cfg(feature = "reactors")]
    pub fn dispatch_reactors(&mut self) -> bool {
        // SAFETY: reactor_notify_id was resolved during build() from the
        // same WorldBuilder. &mut self guarantees exclusive access. We hold
        // a raw pointer to allow scoped re-borrows across reactor dispatch.
        let notify_ptr: *mut crate::reactor::ReactorNotify =
            unsafe { self.get_mut::<crate::reactor::ReactorNotify>(self.reactor_notify_id) };

        // Poll — scoped &mut, dropped before reactor dispatch.
        let mut events = self
            .reactor_events
            .take()
            .unwrap_or_else(|| nexus_notify::Events::with_capacity(256));
        {
            // SAFETY: notify_ptr is stable (heap-allocated ResourceCell).
            // Scoped — &mut is dropped before any other access.
            let notify = unsafe { &mut *notify_ptr };
            notify.poll(&mut events);
        }
        let ran = !events.is_empty();

        // Dispatch — each reactor is moved out before run(), put back after.
        // &mut ReactorNotify is scoped tightly to avoid aliasing during run().
        for token in events.drain() {
            let idx = token.index();
            let reactor = {
                // SAFETY: notify_ptr is stable. Scoped — &mut is dropped
                // before reactor.run(self) which may re-borrow World.
                let notify = unsafe { &mut *notify_ptr };
                notify.take_reactor(idx)
            }; // &mut dropped here — safe to call run()
            if let Some(mut reactor) = reactor {
                reactor.run(self);
                // SAFETY: notify_ptr is stable. reactor.run() is complete,
                // so no World borrows remain. Safe to re-borrow notify.
                let notify = unsafe { &mut *notify_ptr };
                notify.put_reactor(idx, reactor);
            }
        }

        // Deferred removals — swap the inner Vec out to avoid holding
        // &mut DeferredRemovals and &mut ReactorNotify simultaneously.
        // Zero allocation: the Vec is swapped back and reused next frame.
        // SAFETY: reactor_removals_id was resolved during build() from
        // the same WorldBuilder. No other references to this resource.
        let removals =
            unsafe { self.get_mut::<crate::reactor::DeferredRemovals>(self.reactor_removals_id) };
        let mut pending = removals.take();
        if !pending.is_empty() {
            // SAFETY: notify_ptr is stable. removals &mut was dropped
            // (pending now owns the data). No aliasing.
            let notify = unsafe { &mut *notify_ptr };
            while let Some(token) = pending.pop() {
                notify.remove_reactor(token);
            }
        }
        // Put the (now empty) Vec back for reuse.
        // SAFETY: same removals_id, no other references.
        let removals =
            unsafe { self.get_mut::<crate::reactor::DeferredRemovals>(self.reactor_removals_id) };
        removals.put(pending);

        // Return events buffer for reuse next frame.
        self.reactor_events = Some(events);

        ran
    }

    /// Number of registered reactors.
    #[cfg(feature = "reactors")]
    pub fn reactor_count(&self) -> usize {
        self.resource::<crate::reactor::ReactorNotify>()
            .reactor_count()
    }
}

// SAFETY: All resources are `T: Send` (enforced by `register`). World owns all
// heap-allocated data exclusively — the raw pointers are not aliased or shared.
// Transferring ownership to another thread is safe; the new thread becomes the
// sole accessor.
#[allow(clippy::non_send_fields_in_send_ty)]
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
    impl Resource for Price {}

    struct Venue {
        name: &'static str,
    }
    impl Resource for Venue {}

    struct Config {
        max_orders: usize,
    }
    impl Resource for Config {}

    #[test]
    fn register_and_build() {
        let mut builder = WorldBuilder::new();
        builder.register::<Price>(Price { value: 100.0 });
        builder.register::<Venue>(Venue { name: "test" });
        let world = builder.build();
        #[cfg(not(feature = "reactors"))]
        assert_eq!(world.len(), 2);
        #[cfg(feature = "reactors")]
        assert_eq!(world.len(), 5); // + ReactorNotify + DeferredRemovals + SourceRegistry
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn resource_ids_are_distinct() {
        let mut builder = WorldBuilder::new();
        let id0 = builder.register::<Price>(Price { value: 0.0 });
        let id1 = builder.register::<Venue>(Venue { name: "" });
        let id2 = builder.register::<Config>(Config { max_orders: 0 });
        assert_ne!(id0, id1);
        assert_ne!(id1, id2);
        assert_ne!(id0, id2);

        let world = builder.build();
        // SAFETY: ids obtained from register() on this world; types match the registered types.
        unsafe {
            assert_eq!(world.get::<Price>(id0).value, 0.0);
            assert_eq!(world.get::<Venue>(id1).name, "");
            assert_eq!(world.get::<Config>(id2).max_orders, 0);
        }
    }

    #[test]
    #[allow(clippy::float_cmp)]
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
    #[allow(clippy::float_cmp)]
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
        // With the `reactors` feature, ReactorNotify + DeferredRemovals +
        // SourceRegistry are auto-registered. Without it, the world is truly empty.
        #[cfg(not(feature = "reactors"))]
        assert_eq!(world.len(), 0);
        #[cfg(feature = "reactors")]
        assert_eq!(world.len(), 3);
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
    #[allow(clippy::float_cmp)]
    fn multiple_types_independent() {
        let mut builder = WorldBuilder::new();
        let price_id = builder.register::<Price>(Price { value: 10.0 });
        let venue_id = builder.register::<Venue>(Venue { name: "CB" });
        let config_id = builder.register::<Config>(Config { max_orders: 500 });
        let world = builder.build();

        // SAFETY: ids obtained from register() on this world; types match the registered types.
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
    #[allow(clippy::float_cmp)]
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
        let registered_id = builder.register::<u64>(42);

        let registry = builder.registry();
        assert!(registry.contains::<u64>());
        assert!(!registry.contains::<bool>());

        let id = registry.id::<u64>();
        assert_eq!(id, registered_id);
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
    #[allow(clippy::float_cmp)]
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

    // -- Sequence tests -----------------------------------------------------------

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
        world.reset_sequence();
        assert_eq!(world.current_sequence(), Sequence(0));
    }

    // -- run_startup tests ----------------------------------------------------

    #[test]
    fn run_startup_dispatches_handler() {
        use crate::ResMut;

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        builder.register::<bool>(false);
        let mut world = builder.build();

        fn init(mut counter: ResMut<u64>, mut flag: ResMut<bool>) {
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

        fn phase1(mut counter: ResMut<u64>) {
            *counter += 10;
        }

        fn phase2(mut counter: ResMut<u64>) {
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
        assert!(*world.resource::<bool>());
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
        // SAFETY: counter_id was obtained from register() inside install_driver; type matches.
        unsafe {
            assert_eq!(*world.get::<u64>(handle.counter_id), 0);
        }
    }

    // -- check_access conflict detection ----------------------------------------

    #[test]
    fn check_access_no_conflict() {
        let mut builder = WorldBuilder::new();
        let id_a = builder.register::<u64>(0);
        let id_b = builder.register::<u32>(0);
        builder
            .registry()
            .check_access(&[(Some(id_a), "a"), (Some(id_b), "b")]);
    }

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn check_access_detects_conflict() {
        let mut builder = WorldBuilder::new();
        let id = builder.register::<u64>(0);
        builder
            .registry()
            .check_access(&[(Some(id), "a"), (Some(id), "b")]);
    }

    #[test]
    fn sequence_wrapping() {
        let builder = WorldBuilder::new();
        let mut world = builder.build();

        // Advance to MAX.
        world.current_sequence.set(Sequence(i64::MAX));
        assert_eq!(world.current_sequence(), Sequence(i64::MAX));

        // Wrap to MIN (which is the NULL sentinel, but wrapping is
        // purely mechanical — it doesn't assign semantic meaning).
        let seq = world.next_sequence();
        assert_eq!(seq, Sequence(i64::MIN));
        assert_eq!(world.current_sequence(), Sequence(i64::MIN));
    }

    // -- BorrowTracker tests (debug builds only) ------------------------------

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "conflicting access")]
    fn borrow_tracker_catches_double_access() {
        let mut builder = WorldBuilder::new();
        let id = builder.register::<u64>(42);
        let world = builder.build();
        world.clear_borrows();
        world.track_borrow(id);
        world.track_borrow(id); // same resource, same phase
    }

    #[cfg(debug_assertions)]
    #[test]
    fn borrow_tracker_allows_after_clear() {
        let mut builder = WorldBuilder::new();
        let id = builder.register::<u64>(42);
        let world = builder.build();
        world.clear_borrows();
        world.track_borrow(id);
        world.clear_borrows();
        world.track_borrow(id); // new phase, no conflict
    }

    #[cfg(debug_assertions)]
    #[test]
    fn borrow_tracker_different_resources_ok() {
        let mut builder = WorldBuilder::new();
        let id_a = builder.register::<u64>(1);
        let id_b = builder.register::<u32>(2);
        let world = builder.build();
        world.clear_borrows();
        world.track_borrow(id_a);
        world.track_borrow(id_b); // different resources, no conflict
    }
}
