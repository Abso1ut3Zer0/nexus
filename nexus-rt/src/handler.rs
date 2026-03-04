//! Handler parameter resolution and dispatch primitives.

use std::ops::{Deref, DerefMut};

use crate::callback::Callback;
use crate::resource::{Res, ResMut};
use crate::world::{Registry, ResourceId, World};

// =============================================================================
// Param
// =============================================================================

/// Trait for types that can be resolved from a [`Registry`] at build time
/// and fetched from [`World`] at dispatch time.
///
/// Analogous to Bevy's `SystemParam`.
///
/// Two-phase resolution:
///
/// 1. **Build time** — [`init`](Self::init) resolves opaque state (e.g. a
///    [`ResourceId`]) from the registry. This panics if the required type
///    isn't registered — giving an early build-time error.
/// 2. **Dispatch time** — [`fetch`](Self::fetch) uses the cached state to
///    produce a reference in ~3 cycles.
///
/// # Built-in impls
///
/// | Param | State | Description |
/// |-------|-------|-------------|
/// | [`Res<T>`] | `ResourceId` | Shared read |
/// | [`ResMut<T>`] | `ResourceId` | Exclusive write (stamps on `DerefMut`) |
/// | [`Option<Res<T>>`] | `Option<ResourceId>` | Optional shared read |
/// | [`Option<ResMut<T>>`] | `Option<ResourceId>` | Optional exclusive write |
/// | [`Local<T>`] | `T` | Per-handler state (not in World) |
/// | [`RegistryRef`] | `()` | Read-only registry access |
/// | `()` | `()` | Event-only handlers |
/// | Tuples of params | Tuple of states | Up to 8 params |
pub trait Param {
    /// Opaque state cached at build time (e.g. [`ResourceId`]).
    ///
    /// `Send` is required because state is stored in handler types
    /// ([`Callback`]), and handlers must be `Send` (they live in
    /// [`World`], which is `Send`).
    type State: Send;

    /// The item produced at dispatch time.
    type Item<'w>;

    /// Resolve state from the registry. Called once at build time.
    ///
    /// # Panics
    ///
    /// Panics if the required resource is not registered.
    fn init(registry: &Registry) -> Self::State;

    /// Fetch the item using cached state.
    ///
    /// # Safety
    ///
    /// - `state` must have been produced by [`init`](Self::init) on the
    ///   same registry that built the `world`.
    /// - Caller ensures no aliasing violations.
    unsafe fn fetch<'w>(world: &'w World, state: &'w mut Self::State) -> Self::Item<'w>;

    /// Returns `true` if any resource this param depends on was modified
    /// during the current sequence.
    ///
    /// Used by drivers to skip handlers whose inputs haven't changed.
    fn any_changed(state: &Self::State, world: &World) -> bool;

    /// The ResourceId this param accesses, if any.
    ///
    /// Returns `None` for params that don't access World resources
    /// (e.g. `Local<T>`). Used by [`Registry::check_access`] to enforce
    /// one borrow per resource per handler.
    fn resource_id(state: &Self::State) -> Option<ResourceId> {
        let _ = state;
        None
    }
}

// -- Res<T> ------------------------------------------------------------------

impl<T: 'static> Param for Res<'_, T> {
    type State = ResourceId;
    type Item<'w> = Res<'w, T>;

    fn init(registry: &Registry) -> ResourceId {
        registry.id::<T>()
    }

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, state: &'w mut ResourceId) -> Res<'w, T> {
        let id = *state;
        // SAFETY: state was produced by init() on the same world.
        // Caller ensures no mutable alias exists for T.
        unsafe {
            Res::new(
                world.get::<T>(id),
                world.changed_at(id),
                world.current_sequence(),
            )
        }
    }

    fn any_changed(state: &ResourceId, world: &World) -> bool {
        // SAFETY: state was produced by init() on the same registry.
        unsafe { world.changed_at(*state) == world.current_sequence() }
    }

    fn resource_id(state: &ResourceId) -> Option<ResourceId> {
        Some(*state)
    }
}

// -- ResMut<T> ---------------------------------------------------------------

impl<T: 'static> Param for ResMut<'_, T> {
    type State = ResourceId;
    type Item<'w> = ResMut<'w, T>;

    fn init(registry: &Registry) -> ResourceId {
        registry.id::<T>()
    }

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, state: &'w mut ResourceId) -> ResMut<'w, T> {
        let id = *state;
        // SAFETY: state was produced by init() on the same world.
        // Caller ensures no aliases exist for T.
        unsafe {
            ResMut::new(
                world.get_mut::<T>(id),
                world.changed_at_cell(id),
                world.current_sequence(),
            )
        }
    }

    fn any_changed(state: &ResourceId, world: &World) -> bool {
        // SAFETY: state was produced by init() on the same registry.
        unsafe { world.changed_at(*state) == world.current_sequence() }
    }

    fn resource_id(state: &ResourceId) -> Option<ResourceId> {
        Some(*state)
    }
}

// -- Option<Res<T>> ----------------------------------------------------------

impl<T: 'static> Param for Option<Res<'_, T>> {
    type State = Option<ResourceId>;
    type Item<'w> = Option<Res<'w, T>>;

    fn init(registry: &Registry) -> Option<ResourceId> {
        registry.try_id::<T>()
    }

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, state: &'w mut Option<ResourceId>) -> Option<Res<'w, T>> {
        // SAFETY: state was produced by init() on the same world.
        // Caller ensures no mutable alias exists for T.
        state.map(|id| unsafe {
            Res::new(
                world.get::<T>(id),
                world.changed_at(id),
                world.current_sequence(),
            )
        })
    }

    fn any_changed(state: &Option<ResourceId>, world: &World) -> bool {
        state.is_some_and(|id| {
            // SAFETY: id was produced by init() on the same registry.
            unsafe { world.changed_at(id) == world.current_sequence() }
        })
    }

    fn resource_id(state: &Option<ResourceId>) -> Option<ResourceId> {
        *state
    }
}

// -- Option<ResMut<T>> -------------------------------------------------------

impl<T: 'static> Param for Option<ResMut<'_, T>> {
    type State = Option<ResourceId>;
    type Item<'w> = Option<ResMut<'w, T>>;

    fn init(registry: &Registry) -> Option<ResourceId> {
        registry.try_id::<T>()
    }

    #[inline(always)]
    unsafe fn fetch<'w>(
        world: &'w World,
        state: &'w mut Option<ResourceId>,
    ) -> Option<ResMut<'w, T>> {
        // SAFETY: state was produced by init() on the same world.
        // Caller ensures no aliases exist for T.
        state.map(|id| unsafe {
            ResMut::new(
                world.get_mut::<T>(id),
                world.changed_at_cell(id),
                world.current_sequence(),
            )
        })
    }

    fn any_changed(state: &Option<ResourceId>, world: &World) -> bool {
        state.is_some_and(|id| {
            // SAFETY: id was produced by init() on the same registry.
            unsafe { world.changed_at(id) == world.current_sequence() }
        })
    }

    fn resource_id(state: &Option<ResourceId>) -> Option<ResourceId> {
        *state
    }
}

// =============================================================================
// Tuple impls
// =============================================================================

/// Unit impl — event-only handlers with no resource parameters.
impl Param for () {
    type State = ();
    type Item<'w> = ();

    fn init(_registry: &Registry) {}

    #[inline(always)]
    unsafe fn fetch<'w>(_world: &'w World, _state: &'w mut ()) {}

    fn any_changed(_state: &(), _world: &World) -> bool {
        false
    }
}

macro_rules! impl_param_tuple {
    ($($P:ident),+) => {
        impl<$($P: Param),+> Param for ($($P,)+) {
            type State = ($($P::State,)+);
            type Item<'w> = ($($P::Item<'w>,)+);

            fn init(registry: &Registry) -> Self::State {
                ($($P::init(registry),)+)
            }

            #[inline(always)]
            #[allow(non_snake_case)]
            unsafe fn fetch<'w>(world: &'w World, state: &'w mut Self::State) -> Self::Item<'w> {
                let ($($P,)+) = state;
                // SAFETY: caller upholds aliasing invariants for all params.
                unsafe { ($($P::fetch(world, $P),)+) }
            }

            #[allow(non_snake_case)]
            fn any_changed(state: &Self::State, world: &World) -> bool {
                let ($($P,)+) = state;
                $($P::any_changed($P, world))||+
            }
        }
    };
}

macro_rules! all_tuples {
    ($m:ident) => {
        $m!(P0);
        $m!(P0, P1);
        $m!(P0, P1, P2);
        $m!(P0, P1, P2, P3);
        $m!(P0, P1, P2, P3, P4);
        $m!(P0, P1, P2, P3, P4, P5);
        $m!(P0, P1, P2, P3, P4, P5, P6);
        $m!(P0, P1, P2, P3, P4, P5, P6, P7);
    };
}

all_tuples!(impl_param_tuple);

// =============================================================================
// Local<T> — per-handler state
// =============================================================================

/// Per-handler local state. Stored inside the dispatch wrapper (e.g.
/// [`Callback`] or pipeline [`Stage`](crate::Stage)), not in [`World`].
///
/// Analogous to Bevy's `Local<T>`.
///
/// Initialized with [`Default::default()`] at handler creation time. Mutated
/// freely at dispatch time — each handler/stage instance has its own
/// independent copy.
///
/// # Examples
///
/// ```ignore
/// fn count_events(mut count: Local<u64>, event: u32) {
///     *count += 1;
///     println!("event #{}: {}", *count, event);
/// }
/// ```
pub struct Local<'s, T: Default + Send + 'static> {
    value: &'s mut T,
}

impl<'s, T: Default + Send + 'static> Local<'s, T> {
    pub(crate) fn new(value: &'s mut T) -> Self {
        Self { value }
    }
}

impl<T: Default + Send + std::fmt::Debug + 'static> std::fmt::Debug for Local<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T: Default + Send + 'static> Deref for Local<'_, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        self.value
    }
}

impl<T: Default + Send + 'static> DerefMut for Local<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        self.value
    }
}

impl<T: Default + Send + 'static> Param for Local<'_, T> {
    type State = T;
    type Item<'s> = Local<'s, T>;

    fn init(_registry: &Registry) -> T {
        T::default()
    }

    #[inline(always)]
    unsafe fn fetch<'s>(_world: &'s World, state: &'s mut T) -> Local<'s, T> {
        // SAFETY: The dispatch wrapper (Callback or Stage) owns state
        // exclusively. Single-threaded dispatch ensures no aliasing.
        // Lifetime 's is bounded by the handler/stage's run() call.
        Local::new(state)
    }

    fn any_changed(_state: &T, _world: &World) -> bool {
        // Local state is per-handler, not a World resource — never "changed."
        false
    }
}

// =============================================================================
// RegistryRef — read-only access to the type registry during dispatch
// =============================================================================

/// Read-only access to the [`Registry`] during handler dispatch.
///
/// Allows handlers to create new handlers at runtime by calling
/// [`into_handler`](crate::IntoHandler::into_handler) or
/// [`into_callback`](crate::IntoCallback::into_callback) on the
/// borrowed registry.
///
/// No [`ResourceId`] needed — the registry is part of [`World`]'s
/// structure, not a registered resource.
pub struct RegistryRef<'w> {
    registry: &'w Registry,
}

impl Deref for RegistryRef<'_> {
    type Target = Registry;

    #[inline(always)]
    fn deref(&self) -> &Registry {
        self.registry
    }
}

impl Param for RegistryRef<'_> {
    type State = ();
    type Item<'w> = RegistryRef<'w>;

    fn init(_registry: &Registry) {}

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, _state: &'w mut ()) -> RegistryRef<'w> {
        RegistryRef {
            registry: world.registry(),
        }
    }

    fn any_changed((): &(), _: &World) -> bool {
        false
    }
}

// =============================================================================
// Handler<E> — object-safe dispatch trait
// =============================================================================

/// Object-safe dispatch trait for event handlers.
///
/// Analogous to Bevy's `System` trait.
///
/// Enables `Box<dyn Handler<E>>` for type-erased heterogeneous dispatch.
/// Storage and scheduling are the driver's responsibility — this trait
/// only defines the dispatch interface.
///
/// `Send` is required because handlers live in [`World`] (via driver
/// storage like timer wheels), and `World` is `Send`. All concrete
/// handler types ([`Callback`], [`HandlerFn`]) satisfy this automatically
/// for typical usage (function pointers, `ResourceId` state, `Send` context).
///
/// Takes `&mut World` — drivers call this directly in their poll loop.
pub trait Handler<E>: Send {
    /// Run this handler with the given event.
    fn run(&mut self, world: &mut World, event: E);

    /// Returns `true` if any input resource was modified this sequence.
    ///
    /// Default returns `true` (always run). [`Callback`] overrides
    /// by checking its state via [`Param::any_changed`].
    fn inputs_changed(&self, world: &World) -> bool {
        let _ = world;
        true
    }

    /// Returns the handler's name.
    ///
    /// Default returns `"<unnamed>"`. [`Callback`] captures the
    /// function's [`type_name`](std::any::type_name) at construction time.
    fn name(&self) -> &'static str {
        "<unnamed>"
    }
}

// =============================================================================
// CtxFree<F> — coherence wrapper for context-free handlers
// =============================================================================

/// Wrapper that marks a function as context-free.
///
/// Prevents coherence overlap between the context-owning and context-free
/// [`Handler`] impls on [`Callback`]. `CtxFree<F>` is a plain struct and
/// can never satisfy `FnMut` bounds, so the compiler proves the two impls
/// are disjoint.
///
/// Users don't construct this directly — [`IntoHandler`] wraps the
/// function automatically.
#[doc(hidden)]
pub struct CtxFree<F>(pub(crate) F);

/// Type alias for context-free handlers (no owned context).
///
/// This is `Callback<(), CtxFree<F>, Params>` — the `ctx: ()` field
/// is a ZST (zero bytes), identical codegen.
///
/// Created by [`IntoHandler::into_handler`]. Use [`HandlerFn`] in type
/// annotations when you need to name the concrete type rather than
/// `Box<dyn Handler<E>>`.
pub type HandlerFn<F, Params> = Callback<(), CtxFree<F>, Params>;

// =============================================================================
// IntoHandler — conversion trait
// =============================================================================

/// Converts a plain function into a [`Handler`].
///
/// Analogous to Bevy's `IntoSystem`.
///
/// Event `E` is always the last function parameter. Everything before
/// it is resolved as [`Param`] from a [`Registry`].
///
/// # Named functions only
///
/// Closures do not work with `IntoHandler` due to Rust's HRTB inference
/// limitations with GATs. Use named `fn` items instead. This is the same
/// limitation as Bevy's system registration.
///
/// # Handler templates
///
/// For dispatch-time handler creation without HashMap lookups, use
/// [`resolve`](Self::resolve) at setup to pre-resolve parameter state,
/// then [`with_state`](Self::with_state) on the hot path:
///
/// ```
/// use nexus_rt::{Res, ResMut, IntoHandler, WorldBuilder};
///
/// fn tick(counter: Res<u64>, mut flag: ResMut<bool>, event: u32) {
///     if event > 0 { *flag = true; }
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register::<u64>(0);
/// builder.register::<bool>(false);
///
/// // Pre-resolve once (cold path — HashMap lookups here):
/// let state = tick.resolve(builder.registry());
///
/// // Stamp out handlers (hot path — zero HashMap lookups):
/// let mut handler = tick.with_state(state);
/// ```
///
/// # Examples
///
/// ```
/// use nexus_rt::{Res, ResMut, IntoHandler, WorldBuilder};
///
/// fn tick(counter: Res<u64>, mut flag: ResMut<bool>, event: u32) {
///     if event > 0 {
///         *flag = true;
///     }
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register::<u64>(0);
/// builder.register::<bool>(false);
///
/// let mut handler = tick.into_handler(builder.registry());
/// ```
pub trait IntoHandler<E, Params> {
    /// The concrete handler type produced.
    type Handler: Handler<E> + 'static;

    /// Pre-resolve parameter state from the registry.
    ///
    /// Returns the cached state ([`ResourceId`]s) needed to construct
    /// handlers without HashMap lookups. Validates access conflicts.
    ///
    /// Store the returned state and pass it to
    /// [`with_state`](Self::with_state) to stamp out handlers
    /// on the hot path.
    ///
    /// # Panics
    ///
    /// Panics if any required resource is not registered, or if
    /// parameter accesses conflict (e.g. duplicate borrows).
    fn resolve(&self, registry: &Registry) -> <Params as Param>::State
    where
        Params: Param;

    /// Construct a handler from pre-resolved parameter state.
    ///
    /// Zero HashMap lookups. The `state` must have been produced by
    /// [`resolve`](Self::resolve) on a compatible registry.
    fn with_state(self, state: <Params as Param>::State) -> Self::Handler
    where
        Params: Param;

    /// Convert this function into a handler, resolving parameters from the registry.
    fn into_handler(self, registry: &Registry) -> Self::Handler;
}

// =============================================================================
// Per-arity impls via macro — context-free path (Callback<(), CtxFree<F>, P>)
// =============================================================================

// Arity 0: fn(E) — event-only handler, no resource params.
impl<E, F: FnMut(E) + Send + 'static> IntoHandler<E, ()> for F {
    type Handler = Callback<(), CtxFree<F>, ()>;

    fn resolve(&self, registry: &Registry) -> <() as Param>::State {
        <() as Param>::init(registry);
    }

    fn with_state(self, _state: <() as Param>::State) -> Self::Handler {
        Callback {
            ctx: (),
            f: CtxFree(self),
            state: (),
            name: std::any::type_name::<F>(),
        }
    }

    fn into_handler(self, registry: &Registry) -> Self::Handler {
        self.resolve(registry);
        self.with_state(())
    }
}

impl<E, F: FnMut(E) + Send + 'static> Handler<E> for Callback<(), CtxFree<F>, ()> {
    fn run(&mut self, _world: &mut World, event: E) {
        (self.f.0)(event);
    }

    fn inputs_changed(&self, _world: &World) -> bool {
        // Event-only handler — no resource dependencies to check.
        // Always returns true so drivers never skip it.
        true
    }

    fn name(&self) -> &'static str {
        self.name
    }
}

macro_rules! impl_into_handler {
    ($($P:ident),+) => {
        impl<E, F: Send + 'static, $($P: Param + 'static),+> IntoHandler<E, ($($P,)+)> for F
        where
            // Double-bound pattern (from Bevy):
            // - First bound: compiler uses P directly to infer Param
            //   types from the function signature (GATs aren't injective,
            //   so P::Item<'w> alone can't determine P).
            // - Second bound: verifies the function is callable with the
            //   fetched items at any lifetime.
            for<'a> &'a mut F: FnMut($($P,)+ E) + FnMut($($P::Item<'a>,)+ E),
        {
            type Handler = Callback<(), CtxFree<F>, ($($P,)+)>;

            #[allow(non_snake_case)]
            fn resolve(&self, registry: &Registry) -> <($($P,)+) as Param>::State {
                let state = <($($P,)+) as Param>::init(registry);
                {
                    let ($($P,)+) = &state;
                    registry.check_access(&[
                        $(
                            (<$P as Param>::resource_id($P),
                             std::any::type_name::<$P>()),
                        )+
                    ]);
                }
                state
            }

            fn with_state(self, state: <($($P,)+) as Param>::State) -> Self::Handler {
                Callback {
                    ctx: (),
                    f: CtxFree(self),
                    state,
                    name: std::any::type_name::<F>(),
                }
            }

            fn into_handler(self, registry: &Registry) -> Self::Handler {
                let state = self.resolve(registry);
                self.with_state(state)
            }
        }

        impl<E, F: Send + 'static, $($P: Param + 'static),+> Handler<E>
            for Callback<(), CtxFree<F>, ($($P,)+)>
        where
            for<'a> &'a mut F: FnMut($($P,)+ E) + FnMut($($P::Item<'a>,)+ E),
        {
            #[allow(non_snake_case)]
            fn run(&mut self, world: &mut World, event: E) {
                // Helper binds the HRTB lifetime at a concrete call site.
                #[allow(clippy::too_many_arguments)]
                fn call_inner<$($P,)+ Ev>(
                    mut f: impl FnMut($($P,)+ Ev),
                    $($P: $P,)+
                    event: Ev,
                ) {
                    f($($P,)+ event);
                }

                // SAFETY: state was produced by init() on the same registry
                // that built this world. Single-threaded sequential dispatch
                // ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f.0, $($P,)+ event);
            }

            fn inputs_changed(&self, world: &World) -> bool {
                <($($P,)+) as Param>::any_changed(&self.state, world)
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }
    };
}

all_tuples!(impl_into_handler);

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::WorldBuilder;

    // -- Param tests ----------------------------------------------------

    #[test]
    fn res_param() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);
        let mut world = builder.build();

        let mut state = <Res<u64> as Param>::init(world.registry_mut());
        // SAFETY: state from init on same registry, no aliasing.
        let res = unsafe { <Res<u64> as Param>::fetch(&world, &mut state) };
        assert_eq!(*res, 42);
    }

    #[test]
    fn res_mut_param() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(1);
        let mut world = builder.build();

        let mut state = <ResMut<u64> as Param>::init(world.registry_mut());
        // SAFETY: state from init on same registry, no aliasing.
        unsafe {
            let mut res = <ResMut<u64> as Param>::fetch(&world, &mut state);
            *res = 99;
        }
        unsafe {
            let mut read_state = <Res<u64> as Param>::init(world.registry_mut());
            let res = <Res<u64> as Param>::fetch(&world, &mut read_state);
            assert_eq!(*res, 99);
        }
    }

    #[test]
    fn tuple_param() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(10);
        builder.register::<bool>(true);
        let mut world = builder.build();

        let mut state = <(Res<u64>, ResMut<bool>) as Param>::init(world.registry_mut());
        // SAFETY: different types, no aliasing.
        unsafe {
            let (counter, mut flag) =
                <(Res<u64>, ResMut<bool>) as Param>::fetch(&world, &mut state);
            assert_eq!(*counter, 10);
            assert!(*flag);
            *flag = false;
        }
        unsafe {
            let mut read_state = <Res<bool> as Param>::init(world.registry_mut());
            let res = <Res<bool> as Param>::fetch(&world, &mut read_state);
            assert!(!*res);
        }
    }

    #[test]
    fn empty_tuple_param() {
        let mut world = WorldBuilder::new().build();
        let mut state = <() as Param>::init(world.registry_mut());
        // SAFETY: no params to alias.
        let () = unsafe { <() as Param>::fetch(&world, &mut state) };
    }

    // -- Handler dispatch tests -----------------------------------------------

    fn event_only_handler(event: u32) {
        assert_eq!(event, 42);
    }

    #[test]
    fn event_only_dispatch() {
        let mut world = WorldBuilder::new().build();
        let mut sys = event_only_handler.into_handler(world.registry_mut());
        sys.run(&mut world, 42u32);
    }

    fn one_res_handler(counter: Res<u64>, event: u32) {
        assert_eq!(*counter, 10);
        assert_eq!(event, 5);
    }

    #[test]
    fn one_res_and_event() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(10);
        let mut world = builder.build();

        let mut sys = one_res_handler.into_handler(world.registry_mut());
        sys.run(&mut world, 5u32);
    }

    fn two_res_handler(counter: Res<u64>, flag: Res<bool>, event: u32) {
        assert_eq!(*counter, 10);
        assert!(*flag);
        assert_eq!(event, 7);
    }

    #[test]
    fn two_res_and_event() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(10);
        builder.register::<bool>(true);
        let mut world = builder.build();

        let mut sys = two_res_handler.into_handler(world.registry_mut());
        sys.run(&mut world, 7u32);
    }

    fn accumulate(mut counter: ResMut<u64>, event: u64) {
        *counter += event;
    }

    #[test]
    fn mutation_through_res_mut() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut sys = accumulate.into_handler(world.registry_mut());

        sys.run(&mut world, 10u64);
        sys.run(&mut world, 5u64);

        assert_eq!(*world.resource::<u64>(), 15);
    }

    fn add_handler(mut counter: ResMut<u64>, event: u64) {
        *counter += event;
    }

    fn mul_handler(mut counter: ResMut<u64>, event: u64) {
        *counter *= event;
    }

    #[test]
    fn box_dyn_type_erasure() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let sys_a = add_handler.into_handler(world.registry_mut());
        let sys_b = mul_handler.into_handler(world.registry_mut());

        let mut handlers: Vec<Box<dyn Handler<u64>>> = vec![Box::new(sys_a), Box::new(sys_b)];

        for h in handlers.iter_mut() {
            h.run(&mut world, 3u64);
        }
        // 0 + 3 = 3, then 3 * 3 = 9
        assert_eq!(*world.resource::<u64>(), 9);
    }

    // -- Local<T> tests -------------------------------------------------------

    fn local_counter(mut count: Local<u64>, _event: u32) {
        *count += 1;
    }

    #[test]
    fn local_default_init() {
        let mut world = WorldBuilder::new().build();
        let mut sys = local_counter.into_handler(world.registry_mut());
        // Ran once — count should be 1 (started at 0). No panic means init worked.
        sys.run(&mut world, 1u32);
    }

    #[test]
    fn local_persists_across_runs() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn accumulate_local(mut count: Local<u64>, mut total: ResMut<u64>, _event: u32) {
            *count += 1;
            *total = *count;
        }

        let mut sys = accumulate_local.into_handler(world.registry_mut());
        sys.run(&mut world, 0u32);
        sys.run(&mut world, 0u32);
        sys.run(&mut world, 0u32);

        assert_eq!(*world.resource::<u64>(), 3);
    }

    #[test]
    fn local_independent_per_handler() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn inc_local(mut count: Local<u64>, mut total: ResMut<u64>, _event: u32) {
            *count += 1;
            *total += *count;
        }

        let mut sys_a = inc_local.into_handler(world.registry_mut());
        let mut sys_b = inc_local.into_handler(world.registry_mut());

        sys_a.run(&mut world, 0u32); // local=1, total=0+1=1
        sys_b.run(&mut world, 0u32); // local=1, total=1+1=2
        sys_a.run(&mut world, 0u32); // local=2, total=2+2=4

        assert_eq!(*world.resource::<u64>(), 4);
    }

    // -- Option<Res<T>> / Option<ResMut<T>> tests -----------------------------

    #[test]
    fn option_res_none_when_missing() {
        let mut world = WorldBuilder::new().build();
        let mut state = <Option<Res<u64>> as Param>::init(world.registry_mut());
        let opt = unsafe { <Option<Res<u64>> as Param>::fetch(&world, &mut state) };
        assert!(opt.is_none());
    }

    #[test]
    fn option_res_some_when_present() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);
        let mut world = builder.build();

        let mut state = <Option<Res<u64>> as Param>::init(world.registry_mut());
        let opt = unsafe { <Option<Res<u64>> as Param>::fetch(&world, &mut state) };
        assert_eq!(*opt.unwrap(), 42);
    }

    #[test]
    fn option_res_mut_some_when_present() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(1);
        let mut world = builder.build();

        let mut state = <Option<ResMut<u64>> as Param>::init(world.registry_mut());
        unsafe {
            let opt = <Option<ResMut<u64>> as Param>::fetch(&world, &mut state);
            *opt.unwrap() = 99;
        }
        unsafe {
            let mut read_state = <Res<u64> as Param>::init(world.registry_mut());
            let res = <Res<u64> as Param>::fetch(&world, &mut read_state);
            assert_eq!(*res, 99);
        }
    }

    fn optional_handler(opt: Option<Res<String>>, _event: u32) {
        assert!(opt.is_none());
    }

    #[test]
    fn option_in_handler() {
        let mut world = WorldBuilder::new().build();
        let mut sys = optional_handler.into_handler(world.registry_mut());
        sys.run(&mut world, 0u32);
    }

    // -- Change detection tests -----------------------------------------------

    #[test]
    fn inputs_changed_true_when_resource_stamped() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn reader(val: Res<u64>, _e: ()) {
            let _ = *val;
        }

        let sys = reader.into_handler(world.registry_mut());

        // Tick 0: changed_at=0, current_sequence=0 → inputs changed
        assert!(sys.inputs_changed(&world));

        world.next_sequence(); // tick=1

        // Tick 1: changed_at=0, current_sequence=1 → not changed
        assert!(!sys.inputs_changed(&world));

        // Stamp u64 at tick=1
        *world.resource_mut::<u64>() = 42;
        assert!(sys.inputs_changed(&world));
    }

    #[test]
    fn inputs_changed_false_when_not_stamped() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        builder.register::<bool>(false);
        let mut world = builder.build();

        fn reads_bool(flag: Res<bool>, _e: ()) {
            let _ = *flag;
        }

        let sys = reads_bool.into_handler(world.registry_mut());

        world.next_sequence(); // tick=1

        // Only stamp u64, not bool
        *world.resource_mut::<u64>() = 42;

        // Handler reads bool, which wasn't stamped → not changed
        assert!(!sys.inputs_changed(&world));
    }

    #[test]
    fn inputs_changed_with_optional_none() {
        // Optional param with no resource registered → always false
        let mut world = WorldBuilder::new().build();

        fn optional_sys(opt: Option<Res<String>>, _e: ()) {
            let _ = opt;
        }

        let sys = optional_sys.into_handler(world.registry_mut());
        assert!(!sys.inputs_changed(&world));
    }

    #[test]
    fn inputs_changed_event_only_handler() {
        let mut world = WorldBuilder::new().build();

        fn event_handler(_e: u32) {}

        let sys = event_handler.into_handler(world.registry_mut());
        // Event-only handlers always run — drivers must not skip them.
        assert!(sys.inputs_changed(&world));
    }

    // -- Access conflict detection ----------------------------------------

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn duplicate_res_panics() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn bad(a: Res<u64>, b: Res<u64>, _e: ()) {
            let _ = (*a, *b);
        }

        let _sys = bad.into_handler(world.registry_mut());
    }

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn duplicate_res_mut_panics() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn bad(a: ResMut<u64>, b: ResMut<u64>, _e: ()) {
            let _ = (&*a, &*b);
        }

        let _sys = bad.into_handler(world.registry_mut());
    }

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn duplicate_mixed_panics() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn bad(a: Res<u64>, b: ResMut<u64>, _e: ()) {
            let _ = (*a, &*b);
        }

        let _sys = bad.into_handler(world.registry_mut());
    }

    #[test]
    fn different_types_no_conflict() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        builder.register::<u32>(0);
        let mut world = builder.build();

        fn ok(a: Res<u64>, b: ResMut<u32>, _e: ()) {
            let _ = (*a, &*b);
        }

        let _sys = ok.into_handler(world.registry_mut());
    }

    #[test]
    fn local_no_conflict() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn ok(local: Local<u64>, val: ResMut<u64>, _e: ()) {
            let _ = (&*local, &*val);
        }

        let _sys = ok.into_handler(world.registry_mut());
    }

    #[test]
    fn end_to_end_change_detection() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        builder.register::<bool>(false);
        let mut world = builder.build();

        // Tick 0: all resources changed_at=0, current_sequence=0 → changed.
        fn writer(mut val: ResMut<u64>, _e: ()) {
            *val = 42;
        }
        fn observer(val: Res<u64>, flag: Res<bool>, _e: ()) {
            // On tick 0: both are "changed" (changed_at == current_sequence == 0).
            // After next_sequence: only u64 should be changed (writer stamps it).
            let _ = (*val, *flag);
        }

        let mut writer_sys = writer.into_handler(world.registry_mut());
        let mut observer_sys = observer.into_handler(world.registry_mut());

        // Tick 0: everything is "changed"
        writer_sys.run(&mut world, ());
        observer_sys.run(&mut world, ());

        world.next_sequence(); // tick=1

        // Tick 1: writer runs → stamps u64 to tick=1.
        // bool was not written → still at tick=0.
        writer_sys.run(&mut world, ());

        let u64_id = world.id::<u64>();
        let bool_id = world.id::<bool>();
        unsafe {
            assert_eq!(world.changed_at(u64_id), world.current_sequence());
            assert_ne!(world.changed_at(bool_id), world.current_sequence());
        }
    }
}
