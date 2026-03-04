//! Pre-resolved handler templates for zero-lookup generation.
//!
//! # Motivation
//!
//! In move-out-fire patterns (mio accept → per-connection, timer →
//! one-shot), handlers are created *during dispatch*. Each call to
//! [`IntoHandler::into_handler`] or [`IntoCallback::into_callback`]
//! resolves params via `HashMap<TypeId, ResourceId>` — one lookup per
//! parameter. This is fine for cold-path setup but costs 20–75 cycles
//! on the hot path, delaying processing of the next event.
//!
//! Templates eliminate this cost by front-loading the resolution:
//!
//! - **Setup (cold):** resolve params once, store as prototype
//! - **Dispatch (hot):** memcpy prototype → handler (~5 cycles)
//!
//! The trade-off is type erasure via function pointers (~1 cycle per
//! dispatch), making [`TemplatedHandler`] marginally slower than a
//! concrete [`HandlerFn`](crate::HandlerFn) at dispatch time. For the
//! creation-heavy move-out-fire pattern, the 15–70 cycle savings per
//! creation far outweigh the ~1 cycle dispatch overhead.
//!
//! Templates also eliminate the need for [`RegistryRef`](crate::RegistryRef)
//! in handler signatures — instead of passing the registry through to
//! create handlers at dispatch time, handlers access pre-resolved
//! templates via `Res<HandlerTemplate<K>>`.
//!
//! # Architecture
//!
//! ```text
//! Setup (cold):   HandlerTemplate::new(fn, registry)
//!                   └── resolve() + store prototype state
//!
//! Dispatch (hot):  template.generate::<B>()
//!                   └── write-into buffer → TemplatedHandler (~5 cycles)
//!                         └── impl Handler<E> via fn-ptr delegation
//! ```
//!
//! # Buffer sizing
//!
//! [`TemplatedHandler`] is generic over `B: Buffer` from `nexus-smartptr`.
//! The default `B64` fits all handlers through arity 8 with contexts up
//! to ~24 bytes. Use `B128` for larger contexts or when the handler
//! doesn't fit — [`generate`](HandlerTemplate::generate) panics with
//! a clear message if the buffer is too small.
//!
//! See the [crate-level capacity planning docs](crate#capacity-planning)
//! for a full reference table.
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
//! // Generate on the hot path — zero HashMap lookups:
//! let mut handler = world.resource::<HandlerTemplate<OnTick>>().generate();
//! handler.run(&mut world, 1u32);
//!
//! assert!(*world.resource::<bool>());
//! ```

use std::marker::PhantomData;
use std::mem::MaybeUninit;

use nexus_smartptr::{B64, Buffer};

use crate::handler::Param;
use crate::world::{Registry, World};
use crate::{Handler, IntoCallback, IntoHandler};

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
// TemplatedHandler<E, B> — type-erased output
// =============================================================================

/// Type-erased handler produced by template instantiation.
///
/// Dispatches via monomorphized function pointers that delegate to
/// the existing [`Handler`] impl on [`Callback`]. The internal buffer
/// stores a real `Callback` struct — no duplicated dispatch logic.
///
/// # Buffer sizing
///
/// `B` controls inline capacity. The default [`B64`] fits all
/// [`HandlerFn`](crate::HandlerFn) and [`Callback`](crate::Callback)
/// types through arity 8 with contexts up to ~24 bytes. Use [`B128`]
/// for larger callbacks.
///
/// [`generate`](HandlerTemplate::generate) panics if the concrete
/// handler doesn't fit in `B`.
///
/// [`B128`]: nexus_smartptr::B128
///
/// # Guarantees
///
/// - Implements [`Handler<E>`] with ~1 cycle fn-ptr overhead
/// - Zero heap allocations to create
/// - [`Drop`] calls the monomorphized drop function (no-op for
///   context-free handlers, drops `C` for callbacks)
pub struct TemplatedHandler<E, B: Buffer + Send = B64> {
    /// Inline Callback<C, F, P> (type-erased).
    buf: MaybeUninit<B>,
    run_fn: unsafe fn(*mut u8, &mut World, E),
    inputs_changed_fn: unsafe fn(*const u8, &World) -> bool,
    drop_fn: unsafe fn(*mut u8),
    name: &'static str,
    _event: PhantomData<E>,
}

// SAFETY: The buf contains a Callback<C, F, P> where all components
// satisfy Send (enforced by IntoHandler/IntoCallback bounds: F: Send,
// C: Send, Param::State: Send). Function pointers are Send + Sync.
unsafe impl<E, B: Buffer + Send> Send for TemplatedHandler<E, B> {}

impl<E, B: Buffer + Send> Drop for TemplatedHandler<E, B> {
    fn drop(&mut self) {
        // SAFETY: buf contains a Callback written by generate_handler/
        // generate_callback. drop_fn is monomorphized for the same type.
        unsafe { (self.drop_fn)(self.buf.as_mut_ptr().cast()) }
    }
}

impl<E, B: Buffer + Send> Handler<E> for TemplatedHandler<E, B> {
    fn run(&mut self, world: &mut World, event: E) {
        // SAFETY: buf contains a properly initialized Callback,
        // run_fn is monomorphized for the same concrete type.
        unsafe { (self.run_fn)(self.buf.as_mut_ptr().cast(), world, event) }
    }

    fn inputs_changed(&self, world: &World) -> bool {
        // SAFETY: buf contains a properly initialized Callback,
        // inputs_changed_fn is monomorphized for the same concrete type.
        unsafe { (self.inputs_changed_fn)(self.buf.as_ptr().cast(), world) }
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
/// Created once at setup via [`new`](Self::new). Each [`generate`](Self::generate)
/// call stamps out a [`TemplatedHandler`] by writing the pre-resolved
/// state into a caller-provided buffer — zero HashMap lookups.
///
/// # Guarantees
///
/// - [`new`](Self::new) resolves all params and checks access conflicts
///   (panics on error — cold path)
/// - [`generate`](Self::generate) is a memcpy (zero heap allocations)
/// - Template is immutable after creation
///
/// # Panics
///
/// [`new`](Self::new) panics if:
/// - Any required resource is not registered in the [`Registry`]
/// - Parameter accesses conflict (e.g. duplicate mutable borrows)
/// - `F` is not a zero-sized type (closures are not supported)
///
/// [`generate`](Self::generate) panics if:
/// - The handler doesn't fit in the chosen buffer `B`
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
/// // Default B64 buffer:
/// let mut handler = template.generate();
/// builder.register(template);
/// ```
pub struct HandlerTemplate<K: Blueprint> {
    /// Inline prototype: P::State (type-erased, Copy).
    prototype: MaybeUninit<B64>,
    /// Write-into: reads prototype, checks capacity, writes Callback into dst.
    generate_fn: unsafe fn(proto: *const u8, dst: *mut u8, buf_capacity: usize),
    /// Dispatch: Handler::run on the Callback.
    run_fn: unsafe fn(*mut u8, &mut World, K::Event),
    /// Dispatch: Handler::inputs_changed on the Callback.
    inputs_changed_fn: unsafe fn(*const u8, &World) -> bool,
    /// Drop: drop_in_place on the Callback.
    drop_fn: unsafe fn(*mut u8),
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
    /// Panics if:
    /// - Any required resource is not registered
    /// - Parameter accesses conflict
    /// - `F` is not a zero-sized type (closures not supported)
    /// - `P::State` exceeds the prototype buffer (64 bytes)
    /// - Handler alignment exceeds 8
    pub fn new<F, P>(f: F, registry: &Registry) -> Self
    where
        F: IntoHandler<K::Event, P> + Copy,
        P: Param,
        P::State: Copy,
    {
        assert!(
            std::mem::size_of::<F>() == 0,
            "templates require named functions (zero-sized types), got size {}",
            std::mem::size_of::<F>(),
        );

        assert!(
            std::mem::size_of::<P::State>() <= B64::CAPACITY,
            "Param state ({} bytes) exceeds prototype buffer ({} bytes)",
            std::mem::size_of::<P::State>(),
            B64::CAPACITY,
        );

        assert!(
            std::mem::align_of::<<F as IntoHandler<K::Event, P>>::Handler>() <= 8,
            "Handler alignment ({}) exceeds buffer alignment (8)",
            std::mem::align_of::<<F as IntoHandler<K::Event, P>>::Handler>(),
        );

        let state = f.resolve(registry);
        let name = std::any::type_name::<F>();

        // Store prototype state inline.
        let mut prototype = MaybeUninit::<B64>::uninit();
        // SAFETY: we just verified P::State fits. B64 is align(8).
        unsafe { std::ptr::write(prototype.as_mut_ptr().cast(), state) };

        Self {
            prototype,
            generate_fn: generate_handler::<K::Event, F, P>,
            run_fn: run_handler::<K::Event, F, P>,
            inputs_changed_fn: inputs_changed_handler::<K::Event, F, P>,
            drop_fn: drop_handler::<K::Event, F, P>,
            name,
            _key: PhantomData,
        }
    }

    /// Stamp out a new handler from the pre-resolved prototype.
    ///
    /// Zero HashMap lookups. Zero heap allocations. Uses the default
    /// [`B64`] buffer, which fits all handlers through arity 8.
    ///
    /// For larger handlers, use [`generate_sized`](Self::generate_sized).
    pub fn generate(&self) -> TemplatedHandler<K::Event> {
        self.generate_sized()
    }

    /// Stamp out a handler into a specific buffer size class.
    ///
    /// Same as [`generate`](Self::generate) but with an explicit buffer.
    /// Panics if the handler doesn't fit.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_rt::{WorldBuilder, Res, HandlerTemplate, handler_blueprint, B128};
    ///
    /// handler_blueprint!(K, u32);
    /// fn sys(a: Res<u64>, _e: u32) {}
    ///
    /// let mut wb = WorldBuilder::new();
    /// wb.register::<u64>(0);
    /// let tpl = HandlerTemplate::<K>::new(sys, wb.registry());
    /// let handler = tpl.generate_sized::<B128>();
    /// ```
    pub fn generate_sized<B: Buffer + Send>(&self) -> TemplatedHandler<K::Event, B> {
        let mut buf = MaybeUninit::<B>::uninit();
        // SAFETY: prototype was initialized in new() with the concrete
        // P::State type that generate_fn expects. generate_fn checks
        // that the handler fits in B::CAPACITY. B is align(8), handler
        // alignment <= 8 (verified in new()).
        unsafe {
            (self.generate_fn)(
                self.prototype.as_ptr().cast(),
                buf.as_mut_ptr().cast(),
                B::CAPACITY,
            );
        }

        TemplatedHandler {
            buf,
            run_fn: self.run_fn,
            inputs_changed_fn: self.inputs_changed_fn,
            drop_fn: self.drop_fn,
            name: self.name,
            _event: PhantomData,
        }
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
/// generation time.
///
/// # Guarantees
///
/// - [`new`](Self::new) resolves params and checks conflicts (cold path)
/// - [`generate`](Self::generate) is a memcpy + context write (zero
///   heap allocations)
/// - Template is immutable after creation
///
/// # Panics
///
/// [`new`](Self::new) panics if:
/// - Any required resource is not registered
/// - Parameter accesses conflict
/// - `F` is not a zero-sized type
/// - Handler alignment exceeds 8
///
/// [`generate`](Self::generate) panics if:
/// - The callback doesn't fit in the chosen buffer `B`
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
/// let mut handler = template.generate(ConnCtx { id: 42 });
/// builder.register(template);
/// ```
pub struct CallbackTemplate<K: CallbackBlueprint> {
    /// Inline prototype: P::State (type-erased, Copy).
    prototype: MaybeUninit<B64>,
    /// Write-into: reads prototype + context, checks capacity, writes Callback into dst.
    generate_fn: unsafe fn(proto: *const u8, ctx: K::Context, dst: *mut u8, buf_capacity: usize),
    /// Dispatch: Handler::run on the Callback.
    run_fn: unsafe fn(*mut u8, &mut World, K::Event),
    /// Dispatch: Handler::inputs_changed on the Callback.
    inputs_changed_fn: unsafe fn(*const u8, &World) -> bool,
    /// Drop: drop_in_place on the Callback.
    drop_fn: unsafe fn(*mut u8),
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
    /// Panics if:
    /// - Any required resource is not registered
    /// - Parameter accesses conflict
    /// - `F` is not a zero-sized type (closures not supported)
    /// - `P::State` exceeds the prototype buffer (64 bytes)
    /// - Callback alignment exceeds 8
    pub fn new<F, P>(f: F, registry: &Registry) -> Self
    where
        F: IntoCallback<K::Context, K::Event, P> + Copy,
        P: Param,
        P::State: Copy,
    {
        assert!(
            std::mem::size_of::<F>() == 0,
            "templates require named functions (zero-sized types), got size {}",
            std::mem::size_of::<F>(),
        );

        assert!(
            std::mem::size_of::<P::State>() <= B64::CAPACITY,
            "Param state ({} bytes) exceeds prototype buffer ({} bytes)",
            std::mem::size_of::<P::State>(),
            B64::CAPACITY,
        );

        assert!(
            std::mem::align_of::<<F as IntoCallback<K::Context, K::Event, P>>::Callback>() <= 8,
            "Callback alignment ({}) exceeds buffer alignment (8)",
            std::mem::align_of::<<F as IntoCallback<K::Context, K::Event, P>>::Callback>(),
        );

        let state = f.resolve(registry);
        let name = std::any::type_name::<F>();

        let mut prototype = MaybeUninit::<B64>::uninit();
        // SAFETY: we just verified P::State fits. B64 is align(8).
        unsafe { std::ptr::write(prototype.as_mut_ptr().cast(), state) };

        Self {
            prototype,
            generate_fn: generate_callback::<K::Context, K::Event, F, P>,
            run_fn: run_callback::<K::Context, K::Event, F, P>,
            inputs_changed_fn: inputs_changed_callback::<K::Context, K::Event, F, P>,
            drop_fn: drop_callback::<K::Context, K::Event, F, P>,
            name,
            _key: PhantomData,
        }
    }

    /// Stamp out a callback with per-instance context.
    ///
    /// Zero HashMap lookups. Zero heap allocations. Uses the default
    /// [`B64`] buffer, which fits most callbacks.
    ///
    /// For larger callbacks, use [`generate_sized`](Self::generate_sized).
    pub fn generate(&self, ctx: K::Context) -> TemplatedHandler<K::Event> {
        self.generate_sized(ctx)
    }

    /// Stamp out a callback into a specific buffer size class.
    ///
    /// Same as [`generate`](Self::generate) but with an explicit buffer.
    /// Panics if the callback doesn't fit.
    pub fn generate_sized<B: Buffer + Send>(
        &self,
        ctx: K::Context,
    ) -> TemplatedHandler<K::Event, B> {
        let mut buf = MaybeUninit::<B>::uninit();
        // SAFETY: prototype was initialized in new() with the concrete
        // P::State type that generate_fn expects. generate_fn checks
        // that the callback fits in B::CAPACITY. B is align(8), callback
        // alignment <= 8 (verified in new()).
        unsafe {
            (self.generate_fn)(
                self.prototype.as_ptr().cast(),
                ctx,
                buf.as_mut_ptr().cast(),
                B::CAPACITY,
            );
        }

        TemplatedHandler {
            buf,
            run_fn: self.run_fn,
            inputs_changed_fn: self.inputs_changed_fn,
            drop_fn: self.drop_fn,
            name: self.name,
            _event: PhantomData,
        }
    }

    /// Returns the callback function's name.
    pub fn name(&self) -> &'static str {
        self.name
    }
}

// =============================================================================
// Monomorphized fn ptrs — handler
// =============================================================================

/// Writes a handler (Callback) into the destination buffer.
///
/// Reads the prototype state, constructs a Callback via
/// `IntoHandler::with_state`, and writes it to `dst`. The capacity
/// check is inside this monomorphized function so LLVM can
/// constant-fold `size_of::<Handler>() <= buf_capacity` — the branch
/// compiles away entirely in release builds when the handler fits.
///
/// # Safety
///
/// - `proto` must point to a valid `P::State` produced by `HandlerTemplate::new`.
/// - `dst` must point to a buffer with at least `buf_capacity` bytes
///   and alignment >= 8 (verified at template construction time).
unsafe fn generate_handler<E, F, P>(proto: *const u8, dst: *mut u8, buf_capacity: usize)
where
    F: IntoHandler<E, P> + Copy,
    P: Param,
    P::State: Copy,
{
    // Both sides are const-known after monomorphization — LLVM folds
    // this to an unconditional pass or an unconditional panic.
    assert!(
        std::mem::size_of::<<F as IntoHandler<E, P>>::Handler>() <= buf_capacity,
        "Handler ({} bytes) exceeds buffer capacity ({} bytes). \
         Use a larger buffer, e.g. generate_sized::<B128>()",
        std::mem::size_of::<<F as IntoHandler<E, P>>::Handler>(),
        buf_capacity,
    );

    // SAFETY: proto points to a valid P::State, and P::State: Copy.
    let state: P::State = unsafe { *(proto as *const P::State) };

    // SAFETY: F is Copy and a named function item (ZST). Creating a ZST
    // from zeroed memory is safe — there are no bytes to be invalid.
    // ZST check was performed in HandlerTemplate::new().
    let f: F = unsafe { std::mem::zeroed() };

    // Construct the handler via the trait — no coupling to Callback internals.
    let handler = f.with_state(state);

    // SAFETY: dst has sufficient size (checked above) and alignment
    // (checked at new()). Ownership transfers to the TemplatedHandler
    // which will call drop_fn.
    unsafe { std::ptr::write(dst.cast(), handler) };
}

/// # Safety
///
/// `ptr` must point to a valid `<F as IntoHandler<E, P>>::Handler`.
unsafe fn run_handler<E, F, P>(ptr: *mut u8, world: &mut World, event: E)
where
    F: IntoHandler<E, P> + Copy,
    P: Param,
{
    // SAFETY: ptr points to a valid <F as IntoHandler<E, P>>::Handler
    // written by generate_handler.
    let handler = unsafe { &mut *(ptr as *mut <F as IntoHandler<E, P>>::Handler) };
    handler.run(world, event);
}

/// # Safety
///
/// `ptr` must point to a valid `<F as IntoHandler<E, P>>::Handler`.
unsafe fn inputs_changed_handler<E, F, P>(ptr: *const u8, world: &World) -> bool
where
    F: IntoHandler<E, P> + Copy,
    P: Param,
{
    // SAFETY: ptr points to a valid <F as IntoHandler<E, P>>::Handler.
    let handler = unsafe { &*(ptr as *const <F as IntoHandler<E, P>>::Handler) };
    handler.inputs_changed(world)
}

// =============================================================================
// Monomorphized fn ptrs — callback
// =============================================================================

/// Writes a callback (Callback with context) into the destination buffer.
///
/// Capacity check is inside this monomorphized function — LLVM
/// constant-folds it away in release builds when the callback fits.
///
/// # Safety
///
/// - `proto` must point to a valid `P::State`.
/// - `dst` must point to a buffer with at least `buf_capacity` bytes
///   and alignment >= 8.
unsafe fn generate_callback<C, E, F, P>(proto: *const u8, ctx: C, dst: *mut u8, buf_capacity: usize)
where
    C: Send + 'static,
    F: IntoCallback<C, E, P> + Copy,
    P: Param,
    P::State: Copy,
{
    assert!(
        std::mem::size_of::<<F as IntoCallback<C, E, P>>::Callback>() <= buf_capacity,
        "Callback ({} bytes) exceeds buffer capacity ({} bytes). \
         Use a larger buffer, e.g. generate_sized::<B128>(ctx)",
        std::mem::size_of::<<F as IntoCallback<C, E, P>>::Callback>(),
        buf_capacity,
    );

    let state: P::State = unsafe { *(proto as *const P::State) };

    // SAFETY: F is a ZST (verified in CallbackTemplate::new()).
    let f: F = unsafe { std::mem::zeroed() };

    let handler = f.with_state(ctx, state);

    // SAFETY: dst has sufficient size (checked above) and alignment
    // (checked at new()). Ownership transfers to TemplatedHandler.
    unsafe { std::ptr::write(dst.cast(), handler) };
}

/// # Safety
///
/// `ptr` must point to a valid `<F as IntoCallback<C, E, P>>::Callback`.
unsafe fn run_callback<C, E, F, P>(ptr: *mut u8, world: &mut World, event: E)
where
    C: Send + 'static,
    F: IntoCallback<C, E, P> + Copy,
    P: Param,
{
    // SAFETY: ptr points to a valid <F as IntoCallback<C, E, P>>::Callback
    // written by generate_callback.
    let handler = unsafe { &mut *(ptr as *mut <F as IntoCallback<C, E, P>>::Callback) };
    handler.run(world, event);
}

/// # Safety
///
/// `ptr` must point to a valid `<F as IntoCallback<C, E, P>>::Callback`.
unsafe fn inputs_changed_callback<C, E, F, P>(ptr: *const u8, world: &World) -> bool
where
    C: Send + 'static,
    F: IntoCallback<C, E, P> + Copy,
    P: Param,
{
    // SAFETY: ptr points to a valid <F as IntoCallback<C, E, P>>::Callback.
    let handler = unsafe { &*(ptr as *const <F as IntoCallback<C, E, P>>::Callback) };
    handler.inputs_changed(world)
}

// =============================================================================
// Drop helpers
// =============================================================================

/// Drop a handler inline buffer in place.
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

/// Drop a callback inline buffer in place.
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
    fn generate_produces_working_handler() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(42);
        wb.register::<bool>(true);
        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());
        let mut world = wb.build();

        let mut handler = template.generate();
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

        let mut h1 = template.generate();
        let mut h2 = template.generate();

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

        let mut handler = template.generate();
        let mut world = wb.build();
        handler.run(&mut world, ()); // should not panic
    }

    #[test]
    fn event_only_template() {
        let wb = WorldBuilder::new();
        let template = HandlerTemplate::<TestHandlerEventOnly>::new(sys_event_only, wb.registry());
        let mut handler = template.generate();
        let mut world = wb.build();
        handler.run(&mut world, 42u32); // should not panic
    }

    #[test]
    fn name_returns_fn_name() {
        let wb = WorldBuilder::new();
        let template = HandlerTemplate::<TestHandlerEventOnly>::new(sys_event_only, wb.registry());
        assert!(template.name().contains("sys_event_only"));

        let handler: TemplatedHandler<u32> = template.generate();
        assert!(handler.name().contains("sys_event_only"));
    }

    #[test]
    fn handler_as_box_dyn() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(true);
        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());
        let mut world = wb.build();

        let mut boxed: Box<dyn Handler<()>> = Box::new(template.generate_sized::<B64>());
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

        let handler = template.generate();
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
        let handler = template.generate();
        drop(handler);
        drop(template);
        // If drop is broken, the Arc won't be released properly.
        // But here P::State is ResourceId (Copy, no drop) so this
        // mainly verifies the drop path doesn't panic or double-free.
    }

    // -- CallbackTemplate tests -----------------------------------------------

    #[test]
    fn callback_generate_with_context() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let template = CallbackTemplate::<TestCallback>::new(cb_1p, wb.registry());
        let mut world = wb.build();

        let mut handler = template.generate(TimerCtx {
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

        let mut h1 = template.generate(TimerCtx {
            order_id: 5,
            fires: 0,
        });
        let mut h2 = template.generate(TimerCtx {
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
        let mut handler = template.generate(TimerCtx {
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

        let handler = template.generate(TimerCtx {
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

        let mut boxed: Box<dyn Handler<()>> = Box::new(template.generate_sized::<B64>(TimerCtx {
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
            .generate();
        handler.run(&mut world, ());

        assert_eq!(*world.resource::<u64>(), 1);
    }

    // -- Buffer size-class tests ----------------------------------------------

    #[test]
    fn generate_with_explicit_b64() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(true);
        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());
        let mut world = wb.build();

        let mut handler = template.generate_sized::<B64>();
        handler.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 1);
    }

    #[test]
    fn generate_with_b128() {
        use nexus_smartptr::B128;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(true);
        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());
        let mut world = wb.build();

        let mut handler = template.generate_sized::<B128>();
        handler.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 1);
    }

    #[test]
    #[should_panic(expected = "exceeds buffer capacity")]
    fn generate_panics_on_undersized_buffer() {
        use nexus_smartptr::B16;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(true);
        let template = HandlerTemplate::<TestHandler2P>::new(sys_2p, wb.registry());

        // Handler is 24 bytes, B16 only holds 16.
        let _ = template.generate_sized::<B16>();
    }

    #[test]
    fn callback_generate_with_b128() {
        use nexus_smartptr::B128;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let template = CallbackTemplate::<TestCallback>::new(cb_1p, wb.registry());
        let mut world = wb.build();

        let mut handler = template.generate_sized::<B128>(TimerCtx {
            order_id: 42,
            fires: 0,
        });
        handler.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 42);
    }
}
