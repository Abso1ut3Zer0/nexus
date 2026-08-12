//! Handler parameter resolution and dispatch primitives.

// Handler arity is architecturally required by the Param trait — handlers
// take N typed parameters and the macro-generated dispatch impls expand
// per-arity into call_inner functions with N + Input arguments. Module-level
// allow rather than one inline attribute per arity expansion.
#![allow(clippy::too_many_arguments)]

use std::ops::{Deref, DerefMut};

use crate::Resource;
use crate::callback::Callback;
use crate::resource::{Res, ResMut, Seq, SeqMut};
use crate::shutdown::Shutdown;
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
///    produce a reference via a single pointer deref — zero framework overhead.
///
/// # Built-in impls
///
/// | Param | State | Description |
/// |-------|-------|-------------|
/// | [`Res<T>`] | `ResourceId` | Shared read |
/// | [`ResMut<T>`] | `ResourceId` | Exclusive write |
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

impl<T: Resource> Param for Res<'_, T> {
    type State = ResourceId;
    type Item<'w> = Res<'w, T>;

    fn init(registry: &Registry) -> ResourceId {
        registry.id::<T>()
    }

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, state: &'w mut ResourceId) -> Res<'w, T> {
        let id = *state;
        #[cfg(debug_assertions)]
        world.track_borrow(id);
        // SAFETY: state was produced by init() on the same world.
        // Caller ensures no mutable alias exists for T.
        unsafe { Res::new(world.get::<T>(id)) }
    }

    fn resource_id(state: &ResourceId) -> Option<ResourceId> {
        Some(*state)
    }
}

// -- ResMut<T> ---------------------------------------------------------------

impl<T: Resource> Param for ResMut<'_, T> {
    type State = ResourceId;
    type Item<'w> = ResMut<'w, T>;

    fn init(registry: &Registry) -> ResourceId {
        registry.id::<T>()
    }

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, state: &'w mut ResourceId) -> ResMut<'w, T> {
        let id = *state;
        #[cfg(debug_assertions)]
        world.track_borrow(id);
        // SAFETY: state was produced by init() on the same world.
        // Caller ensures no aliases exist for T.
        unsafe { ResMut::new(world.get_mut::<T>(id)) }
    }

    fn resource_id(state: &ResourceId) -> Option<ResourceId> {
        Some(*state)
    }
}

// -- Option<Res<T>> ----------------------------------------------------------

impl<T: Resource> Param for Option<Res<'_, T>> {
    type State = Option<ResourceId>;
    type Item<'w> = Option<Res<'w, T>>;

    fn init(registry: &Registry) -> Option<ResourceId> {
        registry.try_id::<T>()
    }

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, state: &'w mut Option<ResourceId>) -> Option<Res<'w, T>> {
        state.map(|id| {
            #[cfg(debug_assertions)]
            world.track_borrow(id);
            // SAFETY: state was produced by init() on the same world.
            // Caller ensures no mutable alias exists for T.
            unsafe { Res::new(world.get::<T>(id)) }
        })
    }

    fn resource_id(state: &Option<ResourceId>) -> Option<ResourceId> {
        *state
    }
}

// -- Option<ResMut<T>> -------------------------------------------------------

impl<T: Resource> Param for Option<ResMut<'_, T>> {
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
        state.map(|id| {
            #[cfg(debug_assertions)]
            world.track_borrow(id);
            // SAFETY: state was produced by init() on the same world.
            // Caller ensures no aliases exist for T.
            unsafe { ResMut::new(world.get_mut::<T>(id)) }
        })
    }

    fn resource_id(state: &Option<ResourceId>) -> Option<ResourceId> {
        *state
    }
}

// -- Seq (read-only sequence) ------------------------------------------------

impl Param for Seq {
    type State = ();
    type Item<'w> = Seq;

    fn init(_registry: &Registry) {}

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, _state: &'w mut ()) -> Seq {
        Seq(world.current_sequence())
    }
}

// -- SeqMut (mutable sequence) -----------------------------------------------

impl Param for SeqMut<'_> {
    type State = ();
    type Item<'w> = SeqMut<'w>;

    fn init(_registry: &Registry) {}

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, _state: &'w mut ()) -> SeqMut<'w> {
        SeqMut(world.sequence_cell())
    }
}

// -- Shutdown ----------------------------------------------------------------

impl Param for Shutdown<'_> {
    type State = ();
    type Item<'w> = Shutdown<'w>;

    fn init(_registry: &Registry) {}

    #[inline(always)]
    unsafe fn fetch<'w>(world: &'w World, _state: &'w mut ()) -> Shutdown<'w> {
        // Borrow the AtomicBool directly — lifetime-bound to World.
        // No Arc::clone, no raw pointer. Safe by construction.
        Shutdown(world.shutdown_flag())
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
        }
    };
}

all_tuples!(impl_param_tuple);

// =============================================================================
// Local<T> — per-handler state
// =============================================================================

/// Per-handler local state. Stored inside the dispatch wrapper (e.g.
/// [`Callback`] or pipeline step), not in [`World`].
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

    /// Returns the handler's name.
    ///
    /// Default returns `"<unnamed>"`. [`Callback`] captures the
    /// function's [`type_name`](std::any::type_name) at construction time.
    fn name(&self) -> &'static str {
        "<unnamed>"
    }
}

impl<E> Handler<E> for Box<dyn Handler<E>> {
    fn run(&mut self, world: &mut World, event: E) {
        (**self).run(world, event);
    }

    fn name(&self) -> &'static str {
        (**self).name()
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

/// Wrapper that marks a function as taking no event parameter.
///
/// Used in the `F` position of [`Callback`] and [`Step`](crate::pipeline::Step)
/// to add `Handler<()>` / `StepCall<()>` impls that don't pass `()` to the
/// user function. Same coherence trick as [`CtxFree`]: `NoEvent<F>` is a
/// plain struct and never satisfies `FnMut`, so the new impls are provably
/// disjoint from the existing ones.
///
/// For arity-0 functions (`fn()` with no parameters), the compiler can
/// distinguish `FnMut()` from `FnMut(())` and picks the no-event impl
/// automatically. For arities 1+, wrap the function with [`no_event()`]
/// to disambiguate from the event-taking impls:
///
/// ```ignore
/// // Arity 0 — works directly:
/// fn standalone() { }
/// let h = standalone.into_handler(reg);
///
/// // Arities 1+ — wrap with no_event():
/// fn tick(mut counter: ResMut<Counter>) { counter.0 += 1; }
/// let h = no_event(tick).into_handler(reg);
/// ```
pub struct NoEvent<F>(pub(crate) F);

/// Wrap a function for use as a no-event handler, callback, or pipeline step.
///
/// When `E = ()`, functions with 1+ parameters are ambiguous: the compiler
/// can't tell if the last parameter is the event or a [`Param`]. Wrapping
/// with `no_event()` resolves this — the function receives only its
/// [`Param`] parameters, no event.
///
/// Arity-0 functions (`fn()`) don't need this wrapper — the compiler can
/// distinguish `FnMut()` from `FnMut(())` automatically.
///
/// # Examples
///
/// ```
/// use nexus_rt::{no_event, ResMut, IntoHandler, Handler, WorldBuilder, Resource};
///
/// #[derive(Resource)]
/// struct Counter(u64);
///
/// fn tick(mut counter: ResMut<Counter>) {
///     counter.0 += 1;
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register(Counter(0));
/// let mut world = builder.build();
///
/// let mut h = no_event(tick).into_handler(world.registry());
/// h.run(&mut world, ());
///
/// assert_eq!(world.resource::<Counter>().0, 1);
/// ```
pub fn no_event<F>(f: F) -> NoEvent<F> {
    NoEvent(f)
}

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
/// # Factory functions and `use<>` (Rust 2024)
///
/// If you write a function that takes `&Registry` and returns
/// `impl Handler<E>`, Rust 2024 captures the registry borrow in the
/// return type. Add `+ use<...>` listing only the type parameters the
/// handler actually holds:
///
/// ```ignore
/// fn build_handler<C: Config>(
///     reg: &Registry,
/// ) -> impl Handler<Order> + use<C> {
///     process_order::<C>.into_handler(reg)
/// }
/// ```
///
/// See the [crate-level docs](crate#returning-impl-handler-from-functions-rust-2024)
/// for details.
///
/// # Examples
///
/// ```
/// use nexus_rt::{Res, ResMut, IntoHandler, WorldBuilder, Resource};
///
/// #[derive(Resource)]
/// struct Counter(u64);
/// #[derive(Resource)]
/// struct Flag(bool);
///
/// fn tick(counter: Res<Counter>, mut flag: ResMut<Flag>, event: u32) {
///     if event > 0 {
///         flag.0 = true;
///     }
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register(Counter(0));
/// builder.register(Flag(false));
///
/// let mut handler = tick.into_handler(builder.registry());
/// ```
#[diagnostic::on_unimplemented(
    message = "this function cannot be converted into a handler",
    note = "handler signature: `fn(Res<A>, ResMut<B>, ..., Event)` — resources first, event last",
    note = "for Handler<()> with params, wrap with `no_event(fn_name)` to omit the event parameter",
    note = "closures with resource parameters (Res<T>, ResMut<T>) are not supported — use a named `fn`",
    note = "arity-0 closures (`fn(Event)` with no resources) ARE supported"
)]
pub trait IntoHandler<E, Params> {
    /// The concrete handler type produced.
    type Handler: Handler<E> + 'static;

    /// Convert this function into a handler, resolving parameters from the registry.
    #[must_use = "the handler must be stored or dispatched — discarding it does nothing"]
    fn into_handler(self, registry: &Registry) -> Self::Handler;
}

// =============================================================================
// Per-arity impls via macro — context-free path (Callback<(), CtxFree<F>, P>)
// =============================================================================

// Arity 0: fn(E) — event-only handler, no resource params.
impl<E, F: FnMut(E) + Send + 'static> IntoHandler<E, ()> for F {
    type Handler = Callback<(), CtxFree<F>, ()>;

    fn into_handler(self, registry: &Registry) -> Self::Handler {
        Callback {
            ctx: (),
            f: CtxFree(self),
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

impl<E, F: FnMut(E) + Send + 'static> Handler<E> for Callback<(), CtxFree<F>, ()> {
    fn run(&mut self, _world: &mut World, event: E) {
        (self.f.0)(event);
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

            fn into_handler(self, registry: &Registry) -> Self::Handler {
                let state = <($($P,)+) as Param>::init(registry);
                {
                    #[allow(non_snake_case)]
                    let ($($P,)+) = &state;
                    registry.check_access(&[
                        $(
                            (<$P as Param>::resource_id($P),
                             std::any::type_name::<$P>()),
                        )+
                    ]);
                }
                Callback {
                    ctx: (),
                    f: CtxFree(self),
                    state,
                    name: std::any::type_name::<F>(),
                }
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
                fn call_inner<$($P,)+ Ev>(
                    mut f: impl FnMut($($P,)+ Ev),
                    $($P: $P,)+
                    event: Ev,
                ) {
                    f($($P,)+ event);
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by init() on the same registry
                // that built this world. Single-threaded sequential dispatch
                // ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f.0, $($P,)+ event);
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }
    };
}

all_tuples!(impl_into_handler);

// =============================================================================
// No-event impls — Handler<()> without trailing `_: ()` parameter
// =============================================================================

// Arity 0: fn() → Handler<()>
impl<F: FnMut() + Send + 'static> IntoHandler<(), NoEvent<F>> for F {
    type Handler = Callback<(), CtxFree<NoEvent<F>>, ()>;

    fn into_handler(self, registry: &Registry) -> Self::Handler {
        Callback {
            ctx: (),
            f: CtxFree(NoEvent(self)),
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

impl<F: FnMut() + Send + 'static> Handler<()> for Callback<(), CtxFree<NoEvent<F>>, ()> {
    fn run(&mut self, _world: &mut World, _event: ()) {
        (self.f.0.0)();
    }

    fn name(&self) -> &'static str {
        self.name
    }
}

macro_rules! impl_into_handler_no_event {
    ($($P:ident),+) => {
        impl<F: Send + 'static, $($P: Param + 'static),+>
            IntoHandler<(), ($($P,)+)> for NoEvent<F>
        where
            for<'a> &'a mut F: FnMut($($P,)+) + FnMut($($P::Item<'a>,)+),
        {
            type Handler = Callback<(), CtxFree<NoEvent<F>>, ($($P,)+)>;

            fn into_handler(self, registry: &Registry) -> Self::Handler {
                let state = <($($P,)+) as Param>::init(registry);
                {
                    #[allow(non_snake_case)]
                    let ($($P,)+) = &state;
                    registry.check_access(&[
                        $(
                            (<$P as Param>::resource_id($P),
                             std::any::type_name::<$P>()),
                        )+
                    ]);
                }
                Callback {
                    ctx: (),
                    f: CtxFree(self),
                    state,
                    name: std::any::type_name::<F>(),
                }
            }
        }

        impl<F: Send + 'static, $($P: Param + 'static),+> Handler<()>
            for Callback<(), CtxFree<NoEvent<F>>, ($($P,)+)>
        where
            for<'a> &'a mut F: FnMut($($P,)+) + FnMut($($P::Item<'a>,)+),
        {
            #[allow(non_snake_case)]
            fn run(&mut self, world: &mut World, _event: ()) {
                fn call_inner<$($P),+>(
                    mut f: impl FnMut($($P),+),
                    $($P: $P,)+
                ) {
                    f($($P),+)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by init() on the same registry
                // that built this world. Single-threaded sequential dispatch
                // ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f.0 .0, $($P,)+);
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }
    };
}

all_tuples!(impl_into_handler_no_event);

// =============================================================================
// IntoHandlerIgnoringEvent — build a handler that drops the event (any E)
// =============================================================================

/// Handler produced by
/// [`into_handler_event_ignored`](IntoHandlerIgnoringEvent::into_handler_event_ignored).
///
/// Implements [`Handler<E>`] for **every** `E`: it fetches its [`Param`]s,
/// calls the function, and drops the event. It stores no `E`, so it carries no
/// event lifetime — borrowed / non-`'static` events (e.g. wire buffers) work.
pub struct IgnoreEventHandler<F, P: Param> {
    f: F,
    state: P::State,
    name: &'static str,
}

/// Convert a function that omits the event parameter into a [`Handler<E>`] that
/// drops the event — for **any** event type `E`.
///
/// The event-ignoring counterpart of [`IntoHandler`]. Use it when a handler
/// reads only resources and doesn't need the event (e.g. a timer handler that
/// ignores the `Instant`):
///
/// ```
/// use nexus_rt::{Handler, IntoHandlerIgnoringEvent, ResMut, Resource, WorldBuilder};
///
/// #[derive(Resource)]
/// struct Count(u64);
///
/// fn on_tick(mut c: ResMut<Count>) {
///     c.0 += 1;
/// } // no `_: Event` parameter
///
/// let mut wb = WorldBuilder::new();
/// wb.register(Count(0));
/// let mut world = wb.build();
///
/// // `E` (here `u32`) is inferred from the storage type; the event is dropped.
/// let mut h: Box<dyn Handler<u32>> =
///     Box::new(on_tick.into_handler_event_ignored(world.registry()));
/// h.run(&mut world, 42);
/// assert_eq!(world.resource::<Count>().0, 1);
/// ```
///
/// This trait is deliberately **not** generic over the event type — that is
/// what lets the produced handler support non-`'static` events. The method name
/// is what disambiguates it from the event-taking
/// [`into_handler`](IntoHandler::into_handler); no wrapper is needed.
pub trait IntoHandlerIgnoringEvent<Params> {
    /// The concrete handler type produced.
    type Handler: Send + 'static;

    /// Build the event-ignoring handler, resolving params from the registry.
    #[must_use = "the handler must be stored or dispatched — discarding it does nothing"]
    fn into_handler_event_ignored(self, registry: &Registry) -> Self::Handler;
}

macro_rules! impl_into_handler_ignoring_event {
    ($($P:ident),+) => {
        impl<F: Send + 'static, $($P: Param + 'static),+>
            IntoHandlerIgnoringEvent<($($P,)+)> for F
        where
            for<'a> &'a mut F: FnMut($($P,)+) + FnMut($($P::Item<'a>,)+),
        {
            type Handler = IgnoreEventHandler<F, ($($P,)+)>;

            fn into_handler_event_ignored(self, registry: &Registry) -> Self::Handler {
                let state = <($($P,)+) as Param>::init(registry);
                {
                    #[allow(non_snake_case)]
                    let ($($P,)+) = &state;
                    registry.check_access(&[
                        $(
                            (<$P as Param>::resource_id($P),
                             std::any::type_name::<$P>()),
                        )+
                    ]);
                }
                IgnoreEventHandler {
                    f: self,
                    state,
                    name: std::any::type_name::<F>(),
                }
            }
        }

        impl<E, F: Send + 'static, $($P: Param + 'static),+> Handler<E>
            for IgnoreEventHandler<F, ($($P,)+)>
        where
            for<'a> &'a mut F: FnMut($($P,)+) + FnMut($($P::Item<'a>,)+),
        {
            #[allow(non_snake_case)]
            fn run(&mut self, world: &mut World, _event: E) {
                fn call_inner<$($P),+>(
                    mut f: impl FnMut($($P),+),
                    $($P: $P,)+
                ) {
                    f($($P),+)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by init() on the same registry that
                // built this world. Single-threaded sequential dispatch ensures
                // no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+);
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }
    };
}

all_tuples!(impl_into_handler_ignoring_event);

// =============================================================================
// Opaque — marker for closures with unresolved dependencies
// =============================================================================

/// Marker occupying the `Params` position in step and handler traits to
/// indicate that a closure manages its own resource access via
/// `world.resource::<T>()` rather than through [`Param`] resolution.
///
/// `Opaque` is **not** a [`Param`]. It exists solely so the compiler can
/// distinguish three disjoint impl tiers without coherence conflicts:
///
/// | `Params` type | Function shape | Resolution |
/// |---|---|---|
/// | `()` | `FnMut(E)` | No resources needed |
/// | `(P0,)` … `(P0..P7,)` | `fn(Res<A>, ResMut<B>, E)` | Build-time [`Param::init`], dispatch-time [`Param::fetch`] |
/// | `Opaque` | `FnMut(&mut World, E)` | None — caller owns all access |
///
/// Because `&mut World` does not implement `Param`, the `Opaque` impls
/// are always disjoint from the arity-based impls — the compiler infers
/// `Params` unambiguously from the closure/function signature.
///
/// # When to use
///
/// Prefer named functions with [`Param`] parameters — they resolve to a
/// direct pointer dereference per resource (single deref, no HashMap
/// lookup). Use `Opaque` closures as an escape hatch when:
///
/// - You need **conditional** resource access (different resources
///   depending on runtime state).
/// - You need access to a resource whose type isn't known at build time.
/// - You're prototyping and want to defer the named-function refactor.
///
/// # Example
///
/// ```ignore
/// // Named function — preferred, hot path:
/// pipeline.guard(check_risk, &reg)    // fn(Res<Config>, &Order) -> bool
///
/// // Arity-0 closure — no World access:
/// pipeline.guard(|o: &Order| o.price > 100.0, &reg)
///
/// // Opaque closure — escape hatch, HashMap lookups:
/// pipeline.guard(|w: &mut World, o: &Order| {
///     let cfg = w.resource::<Config>();
///     o.price > cfg.threshold
/// }, &reg)
/// ```
pub struct Opaque;

/// Marker type for handlers whose parameters are already resolved.
///
/// Used by the blanket [`IntoHandler`] impl for any [`Handler<E>`].
/// Enables passing already-built pipelines, templates, callbacks, and
/// `Box<dyn Handler<E>>` where `IntoHandler` is expected.
///
/// The `registry` argument to [`IntoHandler::into_handler`] is ignored —
/// the handler's parameters were resolved against the registry it was
/// originally built with. Callers must ensure the handler is run against
/// the same [`World`] it was resolved for.
///
/// When returning a resolved handler from a factory function, the Rust
/// 2024 `+ use<...>` annotation applies — see [`IntoHandler`] docs.
///
/// Users never need to name this type — it's inferred automatically.
pub struct Resolved;

impl<E, H: Handler<E> + 'static> IntoHandler<E, Resolved> for H {
    type Handler = H;

    fn into_handler(self, _registry: &Registry) -> H {
        self
    }
}

// =============================================================================
// OpaqueHandler — Handler<E> for FnMut(&mut World, E) closures
// =============================================================================

/// Wrapper for closures that receive `&mut World` directly as a [`Handler`].
///
/// Created by [`IntoHandler::into_handler`] when the function signature is
/// `FnMut(&mut World, E)`. The closure handles its own resource access —
/// no [`Param`] resolution occurs.
///
/// Prefer named functions with [`Param`] resolution for hot-path handlers.
/// `OpaqueHandler` is an escape hatch for cases where dynamic or conditional
/// resource access is needed.
pub struct OpaqueHandler<F> {
    f: F,
    name: &'static str,
}

impl<E, F: FnMut(&mut World, E) + Send + 'static> Handler<E> for OpaqueHandler<F> {
    fn run(&mut self, world: &mut World, event: E) {
        (self.f)(world, event);
    }

    fn name(&self) -> &'static str {
        self.name
    }
}

impl<E, F: FnMut(&mut World, E) + Send + 'static> IntoHandler<E, Opaque> for F {
    type Handler = OpaqueHandler<F>;

    fn into_handler(self, _registry: &Registry) -> Self::Handler {
        OpaqueHandler {
            f: self,
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::WorldBuilder;
    use crate::world::Sequence;

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
        // New dispatch phase — previous borrows dropped above.
        #[cfg(debug_assertions)]
        world.clear_borrows();
        // SAFETY: state from init on same registry; previous mutable borrow was dropped.
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
        // New dispatch phase — previous borrows dropped above.
        #[cfg(debug_assertions)]
        world.clear_borrows();
        // SAFETY: state from init on same registry; previous mutable borrow was dropped.
        unsafe {
            let mut read_state = <Res<bool> as Param>::init(world.registry_mut());
            let res = <Res<bool> as Param>::fetch(&world, &mut read_state);
            assert!(!*res);
        }
    }

    #[test]
    fn empty_tuple_param() {
        let mut world = WorldBuilder::new().build();
        <() as Param>::init(world.registry_mut());
        // SAFETY: no params to alias.
        unsafe { <() as Param>::fetch(&world, &mut ()) };
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

        for h in &mut handlers {
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
        // SAFETY: state from init on same registry; no mutable alias.
        let opt = unsafe { <Option<Res<u64>> as Param>::fetch(&world, &mut state) };
        assert!(opt.is_none());
    }

    #[test]
    fn option_res_some_when_present() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);
        let mut world = builder.build();

        let mut state = <Option<Res<u64>> as Param>::init(world.registry_mut());
        // SAFETY: state from init on same registry; no mutable alias.
        let opt = unsafe { <Option<Res<u64>> as Param>::fetch(&world, &mut state) };
        assert_eq!(*opt.unwrap(), 42);
    }

    #[test]
    fn option_res_mut_some_when_present() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(1);
        let mut world = builder.build();

        let mut state = <Option<ResMut<u64>> as Param>::init(world.registry_mut());
        // SAFETY: state from init on same registry; exclusive access.
        unsafe {
            let opt = <Option<ResMut<u64>> as Param>::fetch(&world, &mut state);
            *opt.unwrap() = 99;
        }
        #[cfg(debug_assertions)]
        world.clear_borrows();
        // SAFETY: state from init on same registry; previous mutable borrow was dropped.
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

    // -- Access conflict detection ----------------------------------------

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn duplicate_res_panics() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn bad(a: Res<u64>, b: Res<u64>) {
            let _ = (*a, *b);
        }

        let _sys = no_event(bad).into_handler(world.registry_mut());
    }

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn duplicate_res_mut_panics() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn bad(a: ResMut<u64>, b: ResMut<u64>) {
            let _ = (&*a, &*b);
        }

        let _sys = no_event(bad).into_handler(world.registry_mut());
    }

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn duplicate_mixed_panics() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn bad(a: Res<u64>, b: ResMut<u64>) {
            let _ = (*a, &*b);
        }

        let _sys = no_event(bad).into_handler(world.registry_mut());
    }

    #[test]
    fn different_types_no_conflict() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        builder.register::<u32>(0);
        let mut world = builder.build();

        fn ok(a: Res<u64>, b: ResMut<u32>) {
            let _ = (*a, &*b);
        }

        let _sys = no_event(ok).into_handler(world.registry_mut());
    }

    #[test]
    fn local_no_conflict() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn ok(local: Local<u64>, val: ResMut<u64>) {
            let _ = (&*local, &*val);
        }

        let _sys = no_event(ok).into_handler(world.registry_mut());
    }

    // -- OpaqueHandler tests --------------------------------------------------

    #[test]
    fn opaque_handler_dispatch() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let opaque_fn = |w: &mut World, event: u64| {
            let current = *w.resource::<u64>();
            *w.resource_mut::<u64>() = current + event;
        };

        let mut h = opaque_fn.into_handler(world.registry_mut());
        h.run(&mut world, 10u64);
        h.run(&mut world, 5u64);

        assert_eq!(*world.resource::<u64>(), 15);
    }

    #[test]
    fn opaque_handler_boxed() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let opaque_fn = |w: &mut World, event: u64| {
            *w.resource_mut::<u64>() += event;
        };

        let mut h: Box<dyn Handler<u64>> = Box::new(opaque_fn.into_handler(world.registry_mut()));
        h.run(&mut world, 7u64);

        assert_eq!(*world.resource::<u64>(), 7);
    }

    // -- Seq / SeqMut tests ------------------------------------------------

    #[test]
    fn seq_reads_current() {
        fn check(seq: Seq, mut out: ResMut<i64>) {
            *out = seq.get().as_i64();
        }

        let mut builder = WorldBuilder::new();
        builder.register::<i64>(0);
        let mut world = builder.build();
        world.next_sequence(); // seq=1

        let mut handler = no_event(check).into_handler(world.registry_mut());
        handler.run(&mut world, ());
        assert_eq!(*world.resource::<i64>(), 1);
    }

    #[test]
    fn seq_mut_advances() {
        fn stamp(mut seq: SeqMut, mut counter: ResMut<u64>) {
            let a = seq.advance();
            let b = seq.advance();
            *counter = a.as_i64() as u64 * 100 + b.as_i64() as u64;
        }

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();
        // seq starts at 0, handler advances twice → 1, 2
        let mut handler = no_event(stamp).into_handler(world.registry_mut());
        handler.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 100 + 2);
        // World sequence is now 2
        assert_eq!(world.current_sequence(), Sequence(2));
    }

    #[test]
    fn seq_mut_persistent_across_dispatches() {
        fn advance(mut seq: SeqMut) {
            seq.advance();
        }

        let builder = WorldBuilder::new();
        let mut world = builder.build();
        let mut handler = no_event(advance).into_handler(world.registry_mut());
        handler.run(&mut world, ());
        handler.run(&mut world, ());
        handler.run(&mut world, ());
        assert_eq!(world.current_sequence(), Sequence(3));
    }

    // -- Seq position / arity coverage ------------------------------------

    #[test]
    fn seq_only_param() {
        fn handle(seq: Seq) {
            assert!(seq.get().as_i64() >= 0);
        }

        let builder = WorldBuilder::new();
        let mut world = builder.build();
        let mut h = no_event(handle).into_handler(world.registry_mut());
        h.run(&mut world, ());
    }

    #[test]
    fn seq_first_with_res() {
        fn handle(seq: Seq, config: Res<u64>, mut out: ResMut<i64>) {
            *out = seq.get().as_i64() + *config as i64;
        }

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(100);
        builder.register::<i64>(0);
        let mut world = builder.build();
        world.next_sequence();
        let mut h = no_event(handle).into_handler(world.registry_mut());
        h.run(&mut world, ());
        assert_eq!(*world.resource::<i64>(), 101);
    }

    #[test]
    fn seq_middle_position() {
        fn handle(config: Res<u64>, seq: Seq, mut out: ResMut<i64>) {
            *out = *config as i64 + seq.get().as_i64();
        }

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(50);
        builder.register::<i64>(0);
        let mut world = builder.build();
        world.next_sequence(); // seq=1
        let mut h = no_event(handle).into_handler(world.registry_mut());
        h.run(&mut world, ());
        assert_eq!(*world.resource::<i64>(), 51);
    }

    #[test]
    fn seq_last_position() {
        fn handle(mut out: ResMut<i64>, seq: Seq) {
            *out = seq.get().as_i64();
        }

        let mut builder = WorldBuilder::new();
        builder.register::<i64>(0);
        let mut world = builder.build();
        world.next_sequence();
        world.next_sequence(); // seq=2
        let mut h = no_event(handle).into_handler(world.registry_mut());
        h.run(&mut world, ());
        assert_eq!(*world.resource::<i64>(), 2);
    }

    #[test]
    fn seq_mut_only_param() {
        fn handle(mut seq: SeqMut) {
            seq.advance();
        }

        let builder = WorldBuilder::new();
        let mut world = builder.build();
        let mut h = no_event(handle).into_handler(world.registry_mut());
        h.run(&mut world, ());
        assert_eq!(world.current_sequence(), Sequence(1));
    }

    #[test]
    fn seq_mut_first_with_res() {
        fn handle(mut seq: SeqMut, mut out: ResMut<i64>) {
            let s = seq.advance();
            *out = s.0;
        }

        let mut builder = WorldBuilder::new();
        builder.register::<i64>(0);
        let mut world = builder.build();
        let mut h = no_event(handle).into_handler(world.registry_mut());
        h.run(&mut world, ());
        assert_eq!(*world.resource::<i64>(), 1);
    }

    #[test]
    fn seq_mut_middle_position() {
        fn handle(config: Res<u64>, mut seq: SeqMut, mut out: ResMut<i64>) {
            let s = seq.advance();
            *out = s.0 + *config as i64;
        }

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(10);
        builder.register::<i64>(0);
        let mut world = builder.build();
        let mut h = no_event(handle).into_handler(world.registry_mut());
        h.run(&mut world, ());
        assert_eq!(*world.resource::<i64>(), 11);
    }

    #[test]
    fn seq_mut_last_position() {
        fn handle(mut out: ResMut<i64>, mut seq: SeqMut) {
            let s = seq.advance();
            *out = s.0;
        }

        let mut builder = WorldBuilder::new();
        builder.register::<i64>(0);
        let mut world = builder.build();
        let mut h = no_event(handle).into_handler(world.registry_mut());
        h.run(&mut world, ());
        assert_eq!(*world.resource::<i64>(), 1);
    }

    #[test]
    fn seq_mut_multiple_advances_in_one_dispatch() {
        fn handle(mut seq: SeqMut, mut out: ResMut<Vec<i64>>) {
            out.push(seq.advance().0);
            out.push(seq.advance().0);
            out.push(seq.advance().0);
        }

        let mut builder = WorldBuilder::new();
        builder.register::<Vec<i64>>(Vec::new());
        let mut world = builder.build();
        let mut h = no_event(handle).into_handler(world.registry_mut());
        h.run(&mut world, ());
        assert_eq!(*world.resource::<Vec<i64>>(), vec![1, 2, 3]);
        assert_eq!(world.current_sequence(), Sequence(3));
    }

    // =========================================================================
    // Resolved — blanket IntoHandler for Handler<E>
    // =========================================================================

    #[test]
    fn concrete_handler_satisfies_into_handler() {
        // A concrete Handler<E> type should satisfy IntoHandler<E, Resolved>
        fn accept_into_handler<E, P>(h: impl IntoHandler<E, P>, reg: &Registry) -> impl Handler<E> {
            h.into_handler(reg)
        }

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let world = builder.build();

        fn bump(mut val: ResMut<u64>, event: u64) {
            *val += event;
        }

        // Build a concrete handler, pass it where IntoHandler is expected
        let handler = bump.into_handler(world.registry());
        let _resolved = accept_into_handler(handler, world.registry());
    }

    #[test]
    fn handler_impl_into_handler_dispatches() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);

        fn add_event(mut val: ResMut<u64>, event: u64) {
            *val += event;
        }

        // Build handler from function, then re-pass as IntoHandler via Resolved
        let handler = add_event.into_handler(builder.registry());
        let mut resolved = handler.into_handler(builder.registry());
        let mut world = builder.build();

        resolved.run(&mut world, 42);
        assert_eq!(*world.resource::<u64>(), 42);
    }

    // =========================================================================
    // NoEvent — Handler<()> without trailing `_: ()`
    // =========================================================================

    fn no_event_standalone() {}

    #[test]
    fn no_event_arity_0() {
        let mut world = WorldBuilder::new().build();
        let mut h = no_event_standalone.into_handler(world.registry_mut());
        h.run(&mut world, ());
    }

    fn no_event_tick(mut counter: ResMut<u64>) {
        *counter += 1;
    }

    #[test]
    fn no_event_arity_1() {
        use crate::no_event;

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut h = no_event(no_event_tick).into_handler(world.registry_mut());
        h.run(&mut world, ());
        h.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 2);
    }

    fn no_event_two_params(src: Res<u32>, mut dst: ResMut<u64>) {
        *dst += *src as u64;
    }

    #[test]
    fn no_event_arity_2() {
        use crate::no_event;

        let mut builder = WorldBuilder::new();
        builder.register::<u32>(7);
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut h = no_event(no_event_two_params).into_handler(world.registry_mut());
        h.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 7);
    }

    #[test]
    fn no_event_boxed() {
        use crate::no_event;

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let h = no_event(no_event_tick).into_handler(world.registry_mut());
        let mut boxed: Box<dyn Handler<()>> = Box::new(h);
        boxed.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 1);
    }

    #[test]
    fn no_event_coexists_with_event_handler() {
        use crate::no_event;

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        // No-event handler
        let mut h1 = no_event(no_event_tick).into_handler(world.registry_mut());
        h1.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 1);

        // Event handler on same resource — still works
        fn add_event(mut val: ResMut<u64>, event: u64) {
            *val += event;
        }
        let mut h2 = add_event.into_handler(world.registry_mut());
        h2.run(&mut world, 10);
        assert_eq!(*world.resource::<u64>(), 11);
    }
}
