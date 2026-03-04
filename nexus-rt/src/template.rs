//! Pre-resolved handler templates for zero-lookup instantiation.
//!
//! Templates solve the "resolve once, stamp many" pattern: pre-resolve
//! [`Param`] state (ResourceIds) once at setup, then stamp out handlers
//! at dispatch time via memcpy — zero HashMap lookups, zero heap
//! allocations.
//!
//! Use case: move-out-fire patterns where handlers are created during
//! dispatch (accept → per-connection handler, timer schedule → fire
//! callback).
//!
//! # Architecture
//!
//! ```text
//! Setup (cold):   HandlerTemplate::new(fn, registry)
//!                   └── resolve() + store prototype state
//!
//! Dispatch (hot):  template.instantiate()
//!                   └── memcpy prototype → TemplatedHandler (~5 cycles)
//!                         └── impl Handler<E> via fn-ptr delegation
//! ```
//!
//! # Examples
//!
//! ```
//! use nexus_rt::{
//!     WorldBuilder, Res, ResMut, Handler,
//!     HandlerTemplate, Blueprint, handler_blueprint,
//! };
//!
//! handler_blueprint!(OnTick, u32);
//!
//! fn on_tick(counter: Res<u64>, mut flag: ResMut<bool>, _event: u32) {
//!     if *counter > 0 { *flag = true; }
//! }
//!
//! let mut builder = WorldBuilder::new();
//! builder.register::<u64>(42);
//! builder.register::<bool>(false);
//!
//! let template = HandlerTemplate::<OnTick>::new(on_tick, builder.registry());
//! builder.register(template);
//! let mut world = builder.build();
//!
//! // Instantiate on the hot path — zero HashMap lookups:
//! let mut handler = world.resource::<HandlerTemplate<OnTick>>().instantiate();
//! handler.run(&mut world, 1u32);
//!
//! assert!(*world.resource::<bool>());
//! ```

use std::marker::PhantomData;
use std::mem::MaybeUninit;

use crate::handler::Param;
use crate::world::{Registry, World};
use crate::{Handler, IntoCallback, IntoHandler};

// =============================================================================
// Inline buffer
// =============================================================================

/// Max inline storage for type-erased handler state.
///
/// Fits: 8 ResourceIds (64 bytes) + &'static str name (16 bytes) +
/// ZST function + ZST context = 80 bytes for the largest handler.
/// 128 bytes leaves headroom for callback contexts up to ~48 bytes.
const MAX_INLINE: usize = 128;

/// 16-byte aligned inline buffer for type-erased Callback storage.
#[repr(C, align(16))]
struct InlineBuf {
    bytes: [MaybeUninit<u8>; MAX_INLINE],
}

// =============================================================================
// Blueprint traits
// =============================================================================

/// Marker binding a key type to an event type.
///
/// Each handler template is keyed by a unique ZST that implements
/// `Blueprint`. This makes [`HandlerTemplate<K>`] nameable and
/// distinguishable in [`World`] — multiple templates for the same
/// event type coexist by using different keys.
///
/// Use [`handler_blueprint!`] to generate the key + impl in one line.
///
/// # Examples
///
/// ```
/// use nexus_rt::Blueprint;
///
/// struct OnEcho;
/// impl Blueprint for OnEcho { type Event = u32; }
/// ```
pub trait Blueprint: Send + 'static {
    /// The event type that handlers from this template will handle.
    type Event;
}

/// Extension of [`Blueprint`] that also binds a per-instance context type.
///
/// Use [`callback_blueprint!`] to generate the key + impls in one line.
///
/// # Examples
///
/// ```
/// use nexus_rt::{Blueprint, CallbackBlueprint};
///
/// struct ConnState { token: u64 }
///
/// struct OnConn;
/// impl Blueprint for OnConn { type Event = u32; }
/// impl CallbackBlueprint for OnConn { type Context = ConnState; }
/// ```
pub trait CallbackBlueprint: Blueprint {
    /// The per-instance context type owned by the callback.
    type Context: Send;
}

// =============================================================================
// TemplatedHandler<E> — type-erased output
// =============================================================================

/// Type-erased handler produced by template instantiation.
///
/// Dispatches via monomorphized function pointers that delegate to
/// the existing [`Handler`] impl on [`Callback`]. The internal blob
/// stores a real `Callback` struct — no duplicated dispatch logic.
///
/// # Size
///
/// Fixed at `MAX_INLINE` (128) + fn ptrs + name = ~168 bytes on 64-bit.
/// Zero heap allocations — state is stored inline.
///
/// # Guarantees
///
/// - Implements [`Handler<E>`] with ~1 cycle fn-ptr overhead
/// - Zero heap allocations to create
/// - [`Drop`] calls the monomorphized drop function (no-op for
///   context-free handlers, drops `C` for callbacks)
pub struct TemplatedHandler<E> {
    /// Inline Callback<C, F, P> (type-erased).
    buf: InlineBuf,
    run_fn: unsafe fn(*mut u8, &mut World, E),
    inputs_changed_fn: unsafe fn(*const u8, &World) -> bool,
    drop_fn: unsafe fn(*mut u8),
    name: &'static str,
    _event: PhantomData<E>,
}

// SAFETY: The buf contains a Callback<C, F, P> where all components
// satisfy Send (enforced by IntoHandler/IntoCallback bounds: F: Send,
// C: Send, Param::State: Send). Function pointers are Send + Sync.
unsafe impl<E> Send for TemplatedHandler<E> {}

impl<E> Drop for TemplatedHandler<E> {
    fn drop(&mut self) {
        // SAFETY: buf contains a Callback written by instantiate_handler/
        // instantiate_callback. drop_fn is monomorphized for the same type.
        unsafe { (self.drop_fn)(self.buf.bytes.as_mut_ptr().cast()) }
    }
}

impl<E> Handler<E> for TemplatedHandler<E> {
    fn run(&mut self, world: &mut World, event: E) {
        // SAFETY: buf contains a properly initialized Callback,
        // run_fn is monomorphized for the same concrete type.
        unsafe { (self.run_fn)(self.buf.bytes.as_mut_ptr().cast(), world, event) }
    }

    fn inputs_changed(&self, world: &World) -> bool {
        // SAFETY: buf contains a properly initialized Callback,
        // inputs_changed_fn is monomorphized for the same concrete type.
        unsafe { (self.inputs_changed_fn)(self.buf.bytes.as_ptr().cast(), world) }
    }

    fn name(&self) -> &'static str {
        self.name
    }
}

// =============================================================================
// HandlerTemplate<K> — pre-resolved prototype
// =============================================================================

/// Pre-resolved handler template stored as a [`World`] resource.
///
/// Created once at setup via [`new`](Self::new). Each [`instantiate`](Self::instantiate)
/// stamps out a [`TemplatedHandler`] by cloning the pre-resolved state —
/// zero HashMap lookups.
///
/// # Guarantees
///
/// - [`new`](Self::new) resolves all params and checks access conflicts
///   (panics on error — cold path)
/// - [`instantiate`](Self::instantiate) is a memcpy (zero heap allocations)
/// - Template is immutable after creation
///
/// # Panics
///
/// [`new`](Self::new) panics if:
/// - Any required resource is not registered in the [`Registry`]
/// - Parameter accesses conflict (e.g. duplicate mutable borrows)
///
/// # Examples
///
/// ```
/// use nexus_rt::{
///     WorldBuilder, Res, Handler,
///     HandlerTemplate, handler_blueprint,
/// };
///
/// handler_blueprint!(OnPing, u32);
///
/// fn on_ping(val: Res<u64>, _event: u32) {}
///
/// let mut builder = WorldBuilder::new();
/// builder.register::<u64>(42);
/// let template = HandlerTemplate::<OnPing>::new(on_ping, builder.registry());
///
/// let mut handler = template.instantiate();
/// builder.register(template);
/// ```
pub struct HandlerTemplate<K: Blueprint> {
    /// Inline prototype: P::State (type-erased, Copy).
    prototype: InlineBuf,
    instantiate_fn: unsafe fn(*const u8) -> TemplatedHandler<K::Event>,
    name: &'static str,
    _key: PhantomData<K>,
}

// SAFETY: prototype contains P::State which is Send (Param trait bound).
// Function pointers are Send + Sync. PhantomData<K> is Send since K: Send
// (Blueprint bound).
unsafe impl<K: Blueprint> Send for HandlerTemplate<K> {}

// No Drop needed — prototype is P::State: Copy (no destructors).

impl<K: Blueprint> HandlerTemplate<K> {
    /// Create a template from a named function.
    ///
    /// Resolves all [`Param`] state and checks for access conflicts.
    /// The function must be `Copy` (named function items are zero-sized
    /// and always `Copy`).
    ///
    /// # Panics
    ///
    /// Panics if any required resource is not registered, or if
    /// parameter accesses conflict. Also panics if `P::State` exceeds
    /// the inline buffer size (128 bytes).
    pub fn new<F, P>(f: F, registry: &Registry) -> Self
    where
        F: IntoHandler<K::Event, P> + Copy,
        P: Param,
        P::State: Copy,
    {
        assert!(
            std::mem::size_of::<P::State>() <= MAX_INLINE,
            "Param state ({} bytes) exceeds inline buffer ({MAX_INLINE} bytes)",
            std::mem::size_of::<P::State>(),
        );

        let state = f.resolve(registry);
        let name = std::any::type_name::<F>();

        // Store prototype state inline.
        let mut prototype = InlineBuf {
            bytes: [MaybeUninit::uninit(); MAX_INLINE],
        };
        // SAFETY: we just verified P::State fits. Buffer is aligned to 16.
        unsafe { std::ptr::write(prototype.bytes.as_mut_ptr().cast(), state) };

        Self {
            prototype,
            instantiate_fn: instantiate_handler::<K::Event, F, P>,
            name,
            _key: PhantomData,
        }
    }

    /// Stamp out a new handler from the pre-resolved prototype.
    ///
    /// Zero HashMap lookups. Zero heap allocations.
    pub fn instantiate(&self) -> TemplatedHandler<K::Event> {
        // SAFETY: prototype was initialized in new() with the concrete
        // P::State type that instantiate_fn expects.
        unsafe { (self.instantiate_fn)(self.prototype.bytes.as_ptr().cast()) }
    }

    /// Returns the handler function's name.
    pub fn name(&self) -> &'static str {
        self.name
    }
}

// =============================================================================
// CallbackTemplate<K> — pre-resolved prototype with context injection
// =============================================================================

/// Pre-resolved callback template stored as a [`World`] resource.
///
/// Same as [`HandlerTemplate`] but injects a per-instance context at
/// instantiation time.
///
/// # Guarantees
///
/// - [`new`](Self::new) resolves params and checks conflicts (cold path)
/// - [`instantiate`](Self::instantiate) is a memcpy + context write
///   (zero heap allocations)
/// - Template is immutable after creation
///
/// # Panics
///
/// [`new`](Self::new) panics if:
/// - Any required resource is not registered
/// - Parameter accesses conflict
///
/// # Examples
///
/// ```
/// use nexus_rt::{
///     WorldBuilder, ResMut, Handler,
///     CallbackTemplate, callback_blueprint,
/// };
///
/// struct ConnCtx { id: u64 }
///
/// callback_blueprint!(OnConn, ConnCtx, u32);
///
/// fn on_conn(ctx: &mut ConnCtx, mut val: ResMut<u64>, _event: u32) {
///     *val += ctx.id;
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register::<u64>(0);
/// let template = CallbackTemplate::<OnConn>::new(on_conn, builder.registry());
///
/// let mut handler = template.instantiate(ConnCtx { id: 42 });
/// builder.register(template);
/// ```
pub struct CallbackTemplate<K: CallbackBlueprint> {
    /// Inline prototype: P::State (type-erased, Copy).
    prototype: InlineBuf,
    instantiate_fn: unsafe fn(*const u8, K::Context) -> TemplatedHandler<K::Event>,
    name: &'static str,
    _key: PhantomData<K>,
}

// SAFETY: same reasoning as HandlerTemplate.
unsafe impl<K: CallbackBlueprint> Send for CallbackTemplate<K> {}

// No Drop needed — prototype is P::State: Copy (no destructors).

impl<K: CallbackBlueprint> CallbackTemplate<K> {
    /// Create a callback template from a named function.
    ///
    /// Same as [`HandlerTemplate::new`] but for context-owning callbacks.
    ///
    /// # Panics
    ///
    /// Panics if any required resource is not registered, if parameter
    /// accesses conflict, or if `P::State` exceeds the inline buffer
    /// size (128 bytes).
    pub fn new<F, P>(f: F, registry: &Registry) -> Self
    where
        F: IntoCallback<K::Context, K::Event, P> + Copy,
        P: Param,
        P::State: Copy,
    {
        assert!(
            std::mem::size_of::<P::State>() <= MAX_INLINE,
            "Param state ({} bytes) exceeds inline buffer ({MAX_INLINE} bytes)",
            std::mem::size_of::<P::State>(),
        );

        let state = f.resolve(registry);
        let name = std::any::type_name::<F>();

        let mut prototype = InlineBuf {
            bytes: [MaybeUninit::uninit(); MAX_INLINE],
        };
        // SAFETY: we just verified P::State fits. Buffer is aligned to 16.
        unsafe { std::ptr::write(prototype.bytes.as_mut_ptr().cast(), state) };

        Self {
            prototype,
            instantiate_fn: instantiate_callback::<K::Context, K::Event, F, P>,
            name,
            _key: PhantomData,
        }
    }

    /// Stamp out a callback with per-instance context.
    ///
    /// Zero HashMap lookups. Zero heap allocations.
    pub fn instantiate(&self, ctx: K::Context) -> TemplatedHandler<K::Event> {
        // SAFETY: prototype was initialized in new() with the concrete
        // P::State type that instantiate_fn expects.
        unsafe { (self.instantiate_fn)(self.prototype.bytes.as_ptr().cast(), ctx) }
    }

    /// Returns the callback function's name.
    pub fn name(&self) -> &'static str {
        self.name
    }
}

// =============================================================================
// Monomorphized fn ptrs — handler
// =============================================================================

/// Clones the prototype state and constructs a TemplatedHandler.
///
/// Uses `IntoHandler::with_state` to construct the handler, then
/// writes it into an inline buffer. The associated type
/// `<F as IntoHandler>::Handler: Handler<E>` guarantees dispatch works.
///
/// # Safety
///
/// `proto` must point to a valid `P::State` produced by `HandlerTemplate::new`.
unsafe fn instantiate_handler<E, F, P>(proto: *const u8) -> TemplatedHandler<E>
where
    F: IntoHandler<E, P> + Copy,
    P: Param,
    P::State: Copy,
{
    // SAFETY: proto points to a valid P::State, and P::State: Copy.
    let state: P::State = unsafe { *(proto as *const P::State) };

    // SAFETY: F is Copy and a named function item (ZST). Creating a ZST
    // from zeroed memory is safe — there are no bytes to be invalid.
    assert!(
        std::mem::size_of::<F>() == 0,
        "templates require named functions (zero-sized types), got size {}",
        std::mem::size_of::<F>(),
    );
    let f: F = unsafe { std::mem::zeroed() };

    // Construct the handler via the trait — no coupling to Callback internals.
    let handler = f.with_state(state);

    // Write into inline buffer — zero heap allocations.
    assert!(
        std::mem::size_of::<<F as IntoHandler<E, P>>::Handler>() <= MAX_INLINE,
        "Handler ({} bytes) exceeds inline buffer ({MAX_INLINE} bytes)",
        std::mem::size_of::<<F as IntoHandler<E, P>>::Handler>(),
    );
    let mut buf = InlineBuf {
        bytes: [MaybeUninit::uninit(); MAX_INLINE],
    };
    // SAFETY: size verified above. Buffer aligned to 16.
    unsafe {
        std::ptr::write(buf.bytes.as_mut_ptr().cast(), handler);
    }

    TemplatedHandler {
        buf,
        run_fn: run_handler::<E, F, P>,
        inputs_changed_fn: inputs_changed_handler::<E, F, P>,
        drop_fn: drop_handler::<E, F, P>,
        name: std::any::type_name::<F>(),
        _event: PhantomData,
    }
}

/// # Safety
///
/// `blob` must point to a valid `<F as IntoHandler<E, P>>::Handler`.
unsafe fn run_handler<E, F, P>(blob: *mut u8, world: &mut World, event: E)
where
    F: IntoHandler<E, P> + Copy,
    P: Param,
{
    // SAFETY: blob was allocated as <F as IntoHandler<E, P>>::Handler
    // in instantiate_handler.
    let handler = unsafe { &mut *(blob as *mut <F as IntoHandler<E, P>>::Handler) };
    handler.run(world, event);
}

/// # Safety
///
/// `blob` must point to a valid `<F as IntoHandler<E, P>>::Handler`.
unsafe fn inputs_changed_handler<E, F, P>(blob: *const u8, world: &World) -> bool
where
    F: IntoHandler<E, P> + Copy,
    P: Param,
{
    // SAFETY: blob was allocated as <F as IntoHandler<E, P>>::Handler.
    let handler = unsafe { &*(blob as *const <F as IntoHandler<E, P>>::Handler) };
    handler.inputs_changed(world)
}

// =============================================================================
// Monomorphized fn ptrs — callback
// =============================================================================

/// # Safety
///
/// `proto` must point to a valid `P::State`.
unsafe fn instantiate_callback<C, E, F, P>(proto: *const u8, ctx: C) -> TemplatedHandler<E>
where
    C: Send + 'static,
    F: IntoCallback<C, E, P> + Copy,
    P: Param,
    P::State: Copy,
{
    let state: P::State = unsafe { *(proto as *const P::State) };

    assert!(
        std::mem::size_of::<F>() == 0,
        "templates require named functions (zero-sized types), got size {}",
        std::mem::size_of::<F>(),
    );
    let f: F = unsafe { std::mem::zeroed() };

    let handler = f.with_state(ctx, state);

    // Write into inline buffer — zero heap allocations.
    assert!(
        std::mem::size_of::<<F as IntoCallback<C, E, P>>::Callback>() <= MAX_INLINE,
        "Callback ({} bytes) exceeds inline buffer ({MAX_INLINE} bytes)",
        std::mem::size_of::<<F as IntoCallback<C, E, P>>::Callback>(),
    );
    let mut buf = InlineBuf {
        bytes: [MaybeUninit::uninit(); MAX_INLINE],
    };
    // SAFETY: size verified above. Buffer aligned to 16.
    unsafe {
        std::ptr::write(buf.bytes.as_mut_ptr().cast(), handler);
    }

    TemplatedHandler {
        buf,
        run_fn: run_callback::<C, E, F, P>,
        inputs_changed_fn: inputs_changed_callback::<C, E, F, P>,
        drop_fn: drop_callback::<C, E, F, P>,
        name: std::any::type_name::<F>(),
        _event: PhantomData,
    }
}

/// # Safety
///
/// `blob` must point to a valid `<F as IntoCallback<C, E, P>>::Callback`.
unsafe fn run_callback<C, E, F, P>(blob: *mut u8, world: &mut World, event: E)
where
    C: Send + 'static,
    F: IntoCallback<C, E, P> + Copy,
    P: Param,
{
    let handler = unsafe { &mut *(blob as *mut <F as IntoCallback<C, E, P>>::Callback) };
    handler.run(world, event);
}

/// # Safety
///
/// `blob` must point to a valid `<F as IntoCallback<C, E, P>>::Callback`.
unsafe fn inputs_changed_callback<C, E, F, P>(blob: *const u8, world: &World) -> bool
where
    C: Send + 'static,
    F: IntoCallback<C, E, P> + Copy,
    P: Param,
{
    let handler = unsafe { &*(blob as *const <F as IntoCallback<C, E, P>>::Callback) };
    handler.inputs_changed(world)
}

// =============================================================================
// Drop helpers
// =============================================================================

/// Drop a handler blob in place.
///
/// # Safety
///
/// `ptr` must point to a valid `<F as IntoHandler<E, P>>::Handler`.
unsafe fn drop_handler<E, F, P>(ptr: *mut u8)
where
    F: IntoHandler<E, P> + Copy,
    P: Param,
{
    unsafe { std::ptr::drop_in_place(ptr as *mut <F as IntoHandler<E, P>>::Handler) };
}

/// Drop a callback blob in place.
///
/// # Safety
///
/// `ptr` must point to a valid `<F as IntoCallback<C, E, P>>::Callback`.
unsafe fn drop_callback<C, E, F, P>(ptr: *mut u8)
where
    C: Send + 'static,
    F: IntoCallback<C, E, P> + Copy,
    P: Param,
{
    unsafe { std::ptr::drop_in_place(ptr as *mut <F as IntoCallback<C, E, P>>::Callback) };
}

// =============================================================================
// Macros
// =============================================================================

/// Generate a handler blueprint key type.
///
/// Creates a ZST struct and implements [`Blueprint`] for it.
/// Accepts an optional visibility specifier.
///
/// # Examples
///
/// ```
/// use nexus_rt::handler_blueprint;
///
/// handler_blueprint!(pub OnEcho, u32);
/// // Generates:
/// //   pub struct OnEcho;
/// //   impl Blueprint for OnEcho { type Event = u32; }
///
/// handler_blueprint!(OnPrivate, u32);  // private (default)
/// ```
#[macro_export]
macro_rules! handler_blueprint {
    ($vis:vis $name:ident, $event:ty) => {
        /// Handler template key generated by [`handler_blueprint!`].
        $vis struct $name;
        impl $crate::Blueprint for $name {
            type Event = $event;
        }
    };
}

/// Generate a callback blueprint key type.
///
/// Creates a ZST struct and implements both [`Blueprint`] and
/// [`CallbackBlueprint`] for it. Accepts an optional visibility specifier.
///
/// # Examples
///
/// ```
/// use nexus_rt::callback_blueprint;
///
/// pub struct ConnState { id: u64 }
///
/// callback_blueprint!(pub OnConn, ConnState, u32);
/// // Generates:
/// //   pub struct OnConn;
/// //   impl Blueprint for OnConn { type Event = u32; }
/// //   impl CallbackBlueprint for OnConn { type Context = ConnState; }
///
/// callback_blueprint!(OnPrivate, ConnState, u32);  // private (default)
/// ```
#[macro_export]
macro_rules! callback_blueprint {
    ($vis:vis $name:ident, $ctx:ty, $event:ty) => {
        /// Callback template key generated by [`callback_blueprint!`].
        $vis struct $name;
        impl $crate::Blueprint for $name {
            type Event = $event;
        }
        impl $crate::CallbackBlueprint for $name {
            type Context = $ctx;
        }
    };
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Res, ResMut, WorldBuilder};

    // -- Blueprint definitions ------------------------------------------------

    handler_blueprint!(TestHandler1P, ());
    handler_blueprint!(TestHandler2P, ());
    handler_blueprint!(TestHandlerEventOnly, u32);

    struct TimerCtx {
        order_id: u64,
        fires: u64,
    }

    callback_blueprint!(TestCallback, TimerCtx, ());
    callback_blueprint!(TestCallbackEventOnly, TimerCtx, u32);

    // -- Handler functions ----------------------------------------------------

    fn sys_event_only(_event: u32) {}

    fn sys_1p(_a: Res<u64>, _event: ()) {}

    fn sys_2p(mut a: ResMut<u64>, b: Res<bool>, _event: ()) {
        if *b {
            *a += 1;
        }
    }

    fn cb_1p(ctx: &mut TimerCtx, mut counter: ResMut<u64>, _event: ()) {
        ctx.fires += 1;
        *counter += ctx.order_id;
    }

    fn cb_event_only(ctx: &mut TimerCtx, _event: u32) {
        ctx.fires += 1;
    }

    // -- HandlerTemplate tests ------------------------------------------------

    #[test]
    fn instantiate_produces_working_handler() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(42);
        wb.register::<bool>(true);
        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());
        let mut world = wb.build();

        let mut handler = template.instantiate();
        handler.run(&mut world, ());

        assert_eq!(*world.resource::<u64>(), 43);
    }

    #[test]
    fn multiple_instantiations_independent() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(true);
        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());
        let mut world = wb.build();

        let mut h1 = template.instantiate();
        let mut h2 = template.instantiate();

        h1.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 1);

        h2.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 2);
    }

    #[test]
    fn template_with_single_param() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(99);
        let template = HandlerTemplate::<TestHandler1P>::new(sys_1p, wb.registry());

        let mut handler = template.instantiate();
        let mut world = wb.build();
        handler.run(&mut world, ()); // should not panic
    }

    #[test]
    fn event_only_template() {
        let wb = WorldBuilder::new();
        let template = HandlerTemplate::<TestHandlerEventOnly>::new(sys_event_only, wb.registry());
        let mut handler = template.instantiate();
        let mut world = wb.build();
        handler.run(&mut world, 42u32); // should not panic
    }

    #[test]
    fn name_returns_fn_name() {
        let wb = WorldBuilder::new();
        let template = HandlerTemplate::<TestHandlerEventOnly>::new(sys_event_only, wb.registry());
        assert!(template.name().contains("sys_event_only"));

        let handler = template.instantiate();
        assert!(handler.name().contains("sys_event_only"));
    }

    #[test]
    fn handler_as_box_dyn() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(true);
        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());
        let mut world = wb.build();

        let mut boxed: Box<dyn Handler<()>> = Box::new(template.instantiate());
        boxed.run(&mut world, ());

        assert_eq!(*world.resource::<u64>(), 1);
    }

    #[test]
    fn inputs_changed_delegates() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(false);
        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());
        let mut world = wb.build();

        let handler = template.instantiate();
        // Resources registered at sequence 0, world starts at 0 → changed.
        assert!(handler.inputs_changed(&world));

        // Advance sequence — resources now stale.
        world.next_sequence();
        assert!(!handler.inputs_changed(&world));
    }

    #[test]
    fn handler_drop_no_leak() {
        use std::sync::Arc;

        handler_blueprint!(TestDropKey, ());

        fn sys_arc(_a: Res<Arc<()>>, _event: ()) {}

        let mut wb = WorldBuilder::new();
        let arc = Arc::new(());
        wb.register(arc.clone());
        let template = HandlerTemplate::<TestDropKey>::new(sys_arc, wb.registry());

        // Template holds prototype (P::State = ResourceId, no Arc ref).
        // Each instantiation creates a Callback that doesn't hold the Arc
        // either (Res<Arc<()>> only borrows at dispatch time).
        let handler = template.instantiate();
        drop(handler);
        drop(template);
        // If drop is broken, the Arc won't be released properly.
        // But here P::State is ResourceId (Copy, no drop) so this
        // mainly verifies the drop path doesn't panic or double-free.
    }

    // -- CallbackTemplate tests -----------------------------------------------

    #[test]
    fn callback_instantiate_with_context() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let template = CallbackTemplate::<TestCallback>::new(cb_1p, wb.registry());
        let mut world = wb.build();

        let mut handler = template.instantiate(TimerCtx {
            order_id: 10,
            fires: 0,
        });
        handler.run(&mut world, ());

        assert_eq!(*world.resource::<u64>(), 10);
    }

    #[test]
    fn callback_multiple_contexts() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let template = CallbackTemplate::<TestCallback>::new(cb_1p, wb.registry());
        let mut world = wb.build();

        let mut h1 = template.instantiate(TimerCtx {
            order_id: 5,
            fires: 0,
        });
        let mut h2 = template.instantiate(TimerCtx {
            order_id: 7,
            fires: 0,
        });

        h1.run(&mut world, ());
        h2.run(&mut world, ());

        assert_eq!(*world.resource::<u64>(), 12); // 5 + 7
    }

    #[test]
    fn callback_event_only() {
        let wb = WorldBuilder::new();
        let template = CallbackTemplate::<TestCallbackEventOnly>::new(cb_event_only, wb.registry());
        let mut handler = template.instantiate(TimerCtx {
            order_id: 0,
            fires: 0,
        });
        let mut world = wb.build();
        handler.run(&mut world, 42u32); // should not panic
    }

    #[test]
    fn callback_inputs_changed() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let template = CallbackTemplate::<TestCallback>::new(cb_1p, wb.registry());
        let mut world = wb.build();

        let handler = template.instantiate(TimerCtx {
            order_id: 1,
            fires: 0,
        });
        // Resources registered at sequence 0, world starts at 0 → changed.
        assert!(handler.inputs_changed(&world));

        world.next_sequence();
        assert!(!handler.inputs_changed(&world));
    }

    #[test]
    fn callback_as_box_dyn() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let template = CallbackTemplate::<TestCallback>::new(cb_1p, wb.registry());
        let mut world = wb.build();

        let mut boxed: Box<dyn Handler<()>> = Box::new(template.instantiate(TimerCtx {
            order_id: 99,
            fires: 0,
        }));
        boxed.run(&mut world, ());

        assert_eq!(*world.resource::<u64>(), 99);
    }

    // -- Panic tests ----------------------------------------------------------

    #[test]
    #[should_panic(expected = "not registered")]
    fn panics_on_missing_resource() {
        let wb = WorldBuilder::new();
        // u64 not registered — should panic in resolve.
        HandlerTemplate::<TestHandler1P>::new(sys_1p, wb.registry());
    }

    #[test]
    #[should_panic]
    fn panics_on_conflicting_access() {
        handler_blueprint!(TestConflict, ());
        fn conflicting(mut _a: ResMut<u64>, mut _b: ResMut<u64>, _e: ()) {}

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        HandlerTemplate::<TestConflict>::new(conflicting, wb.registry());
    }

    // -- Template stored in World ---------------------------------------------

    #[test]
    fn template_as_world_resource() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(true);

        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());
        wb.register(template);

        let mut world = wb.build();

        let mut handler = world
            .resource::<HandlerTemplate<TestHandler2P>>()
            .instantiate();
        handler.run(&mut world, ());

        assert_eq!(*world.resource::<u64>(), 1);
    }
}
