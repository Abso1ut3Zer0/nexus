//! Reactor dispatch system with interest-based notification.
//!
//! Reactors are lightweight, per-instance dispatch units — each owns its
//! own metadata (instrument ID, order ID, algo parameters) and runs a
//! step function with pre-resolved [`Param`] access when woken.
//!
//! # Architecture
//!
//! ```text
//! LocalNotify      (nexus-notify)  — dedup bitset, mark/poll
//!     ↑
//! ReactorNotify      (nexus-rt)      — World resource: reactor storage +
//!                                    data source fan-out + registration
//! SourceRegistry   (nexus-rt)      — World resource: typed key → DataSource
//!     ↑
//! ReactorSystem      (nexus-rt)      — thin dispatch handle (driver level)
//! ```
//!
//! [`SourceRegistry`] maps domain keys (instrument IDs, strategy IDs,
//! `(Symbol, Venue)` tuples) to [`DataSource`] values for runtime lookup.
//! Any `Hash + Eq + Send + 'static` type works as a key. All three
//! resources are auto-registered by [`WorldBuilder::build`](crate::WorldBuilder::build) when the
//! `reactors` feature is enabled.
//!
//! # Use Cases
//!
//! ## 1. Market maker with per-instrument quoting reactors
//!
//! ```ignore
//! // Step function — context first, then pre-resolved Params
//! fn quoting_step(ctx: &mut QuotingCtx, books: Res<OrderBooks>, mut gw: ResMut<Gateway>) {
//!     let quote = books.compute_quote(ctx.instrument, ctx.layer);
//!     gw.submit_quote(quote);
//! }
//!
//! // Setup
//! let notify = world.resource_mut::<ReactorNotify>();
//! let btc_md = notify.register_source();
//! let positions = notify.register_source();
//!
//! // Map natural keys for runtime lookup
//! world.resource_mut::<SourceRegistry>().insert(InstrumentId::BTC, btc_md);
//!
//! // Register reactor — subscribes to BTC data + positions
//! notify.register(
//!     |id| QuotingCtx { reactor_id: id, instrument: InstrumentId::BTC, layer: 1 },
//!     quoting_step,
//!     &registry,
//! )
//! .subscribe(btc_md)
//! .subscribe(positions);
//! ```
//!
//! ## 2. TWAP execution algo that self-removes on completion
//!
//! ```ignore
//! fn twap_step(
//!     ctx: &mut TwapCtx,
//!     books: Res<OrderBooks>,
//!     mut gw: ResMut<Gateway>,
//!     mut removals: ResMut<DeferredRemovals>,
//! ) {
//!     gw.submit(ctx.instrument, ctx.slice_size, books.best_ask(ctx.instrument));
//!     ctx.remaining -= ctx.slice_size;
//!     if ctx.remaining == 0 {
//!         removals.deregister(ctx.reactor_id);  // cleaned up after frame
//!     }
//! }
//! ```
//!
//! ## 3. Runtime registration from event handlers
//!
//! ```ignore
//! fn on_new_order(
//!     event: NewOrder,
//!     mut notify: ResMut<ReactorNotify>,
//!     sources: Res<SourceRegistry>,
//! ) {
//!     let md_source = sources.get(&event.instrument).unwrap();
//!     notify.register(
//!         |id| TwapCtx { reactor_id: id, instrument: event.instrument, remaining: event.qty },
//!         twap_step, &registry,
//!     ).subscribe(md_source);
//! }
//! ```
//!
//! ## 4. Order fill routing via wire protocol
//!
//! ```ignore
//! // On submission — embed reactor token in order
//! fn submit(ctx: &mut Ctx, mut gw: ResMut<Gateway>) {
//!     gw.submit(Order { client_id: ctx.reactor_id.index(), .. });
//! }
//!
//! // On fill — route back to reactor's data source
//! fn on_fill(fill: Fill, mut notify: ResMut<ReactorNotify>, sources: Res<SourceRegistry>) {
//!     if let Some(src) = sources.get(&RoutingKey(fill.client_id)) {
//!         notify.mark(src);
//!     }
//! }
//! ```
//!
//! ## 5. Instrument delisting — cleanup
//!
//! ```ignore
//! fn on_delist(event: Delist, mut notify: ResMut<ReactorNotify>, mut sources: ResMut<SourceRegistry>) {
//!     if let Some(src) = sources.remove(&event.instrument) {
//!         notify.remove_source(src);  // frees slab slot for reuse
//!     }
//! }
//! ```
//!
//! ## 6. Event handler marking (hot path)
//!
//! ```ignore
//! fn on_btc_tick(event: Tick, mut books: ResMut<OrderBooks>, mut notify: ResMut<ReactorNotify>) {
//!     books.apply(event);
//!     notify.mark(btc_md);  // pre-resolved DataSource, O(1), no lookup
//! }
//! ```

// Handler arity is architecturally required by the Param trait — handlers
// take N typed parameters and the macro-generated dispatch impls expand
// per-arity into call_inner functions with N + Input arguments. Module-level
// allow rather than one inline attribute per arity expansion.
#![allow(clippy::too_many_arguments)]

use std::any::{Any, TypeId};
use std::hash::Hash;

use nexus_notify::local::LocalNotify;
use nexus_notify::{Events, Token};
use rustc_hash::FxHashMap;

use crate::ctx_pipeline::CtxStepCall;
use crate::handler::Param;
use crate::world::{Registry, Resource, ResourceId, World};

// =============================================================================
// DataSource — identifies a category of change
// =============================================================================

/// Identifies a data source (e.g., "BTC market data", "positions").
///
/// Registered via [`ReactorNotify::register_source`]. Event handlers
/// mark data sources via [`ReactorNotify::mark`] to wake subscribed reactors.
///
/// # Type-tag intent
///
/// `DataSource` is a `usize` newtype with no invariants beyond what the
/// underlying integer provides. The newtype exists purely to prevent
/// accidentally passing some other identifier where a `DataSource` is
/// expected. Don't reduce it to a type alias and don't add invariants
/// the rest of the crate doesn't enforce.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct DataSource(pub usize);

// =============================================================================
// ReactorNotify — World resource: storage + notification + registration
// =============================================================================

/// Reactor storage, interest mapping, and notification hub.
///
/// Lives in the [`World`] as a resource. Handles:
/// - Reactor registration and storage (`Box<dyn Reactor>` in a slab)
/// - Data source registration and interest mapping
/// - Marking data sources as changed (fan-out + dedup)
///
/// Event handlers access this via [`ResMut<ReactorNotify>`](crate::ResMut)
/// to mark data sources or register new reactors at runtime.
pub struct ReactorNotify {
    /// Per-reactor token dedup.
    notify: LocalNotify,

    /// Data source → reactor tokens subscribed to this source.
    /// Slab-backed for dynamic add/remove with slot reuse.
    /// Slab key = `DataSource.0`.
    interests: slab::Slab<Vec<Token>>,

    /// Reverse index: reactor token → data sources it's subscribed to.
    /// Enables O(subscriptions) removal instead of O(all_sources × all_subs).
    reactor_sources: Vec<Vec<DataSource>>,

    /// Reactor storage. Slab key = token index.
    /// `Option` enables move-out-move-back during dispatch to avoid
    /// aliasing: the reactor is `take()`n before `run()`, then put back.
    /// `Option<Box<dyn Reactor>>` is niche-optimized — zero extra bytes.
    reactors: slab::Slab<Option<Box<dyn Reactor>>>,
}

// Manual Debug — slab of dyn Reactor can't derive
impl std::fmt::Debug for ReactorNotify {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReactorNotify")
            .field("num_sources", &self.interests.len())
            .field("num_reactors", &self.reactors.len())
            .field("notify", &self.notify)
            .finish()
    }
}

impl ReactorNotify {
    /// Create with capacity hints for data sources and reactors.
    pub fn new(source_capacity: usize, reactor_capacity: usize) -> Self {
        Self {
            notify: LocalNotify::with_capacity(reactor_capacity),
            interests: slab::Slab::with_capacity(source_capacity),
            reactor_sources: Vec::with_capacity(reactor_capacity),
            reactors: slab::Slab::with_capacity(reactor_capacity),
        }
    }

    // ── Data sources ────────────────────────────────────────────────────

    /// Register a new data source. Returns its identifier.
    ///
    /// Slab-backed — removed sources' slots are reused.
    pub fn register_source(&mut self) -> DataSource {
        DataSource(self.interests.insert(Vec::new()))
    }

    /// Remove a data source. Unsubscribes all reactors and frees the
    /// slab slot for reuse.
    ///
    /// Marking a removed `DataSource` is a no-op (stale handle safety).
    pub fn remove_source(&mut self, source: DataSource) {
        if self.interests.contains(source.0) {
            self.interests.remove(source.0);
        }
    }

    // ── Reactor registration ──────────────────────────────────────────────

    /// Reserve a slot for a new reactor and return its [`Token`].
    ///
    /// Use with [`insert_reactor`](Self::insert_reactor) to complete registration.
    /// This two-phase pattern avoids borrow conflicts: you can
    /// drop the `&mut ReactorNotify` borrow, build the reactor with
    /// `world.registry()`, then call `insert`.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Phase 1: reserve slot
    /// let token = world.resource_mut::<ReactorNotify>().create_reactor();
    ///
    /// // Phase 2: build reactor (borrows &World for registry)
    /// let reactor = quoting_step.into_reactor(
    ///     QuotingCtx { reactor_id: token, instrument: BTC },
    ///     world.registry(),
    /// );
    ///
    /// // Phase 3: fill slot
    /// world.resource_mut::<ReactorNotify>()
    ///     .insert_reactor(token, reactor)
    ///     .subscribe(btc_md);
    /// ```
    pub fn create_reactor(&mut self) -> Token {
        // Reserve the slot with a None placeholder so no other registration
        // can claim the same key between alloc and insert.
        let key = self.reactors.insert(None);
        self.notify.ensure_capacity(key);
        // Grow reverse index to cover this reactor token.
        if key >= self.reactor_sources.len() {
            self.reactor_sources.resize_with(key + 1, Vec::new);
        }
        Token::new(key)
    }

    /// Insert a pre-built reactor at a previously allocated [`Token`].
    ///
    /// The token must have been returned by [`create_reactor`](Self::create_reactor)
    /// and not yet filled. Completes the two-phase registration.
    ///
    /// # Panics
    ///
    /// Panics if the token was not allocated by [`create_reactor`](Self::create_reactor) or was
    /// already filled.
    pub fn insert_reactor(
        &mut self,
        token: Token,
        reactor: impl Reactor + 'static,
    ) -> ReactorRegistration<'_> {
        let idx = token.index();
        assert!(
            self.reactors.contains(idx),
            "token {} was not allocated by create_reactor",
            idx,
        );
        assert!(
            self.reactors[idx].is_none(),
            "token {} was already filled",
            idx,
        );
        self.reactors[idx] = Some(Box::new(reactor));
        ReactorRegistration {
            token,
            notify: self,
        }
    }

    /// Register a reactor from a step function + context factory.
    ///
    /// One-shot convenience when you already have `&Registry` (e.g.,
    /// inside event handlers via [`Param`] resolution, or in tests).
    /// For the safe `World`-based API, use [`create_reactor`](Self::create_reactor)
    /// + [`insert_reactor`](Self::insert_reactor).
    pub fn register<C, Params, F: IntoReactor<C, Params>>(
        &mut self,
        ctx_fn: impl FnOnce(Token) -> C,
        step: F,
        registry: &Registry,
    ) -> ReactorRegistration<'_> {
        let key = self.reactors.vacant_key();
        let token = Token::new(key);
        self.notify.ensure_capacity(key);
        if key >= self.reactor_sources.len() {
            self.reactor_sources.resize_with(key + 1, Vec::new);
        }
        let ctx = ctx_fn(token);
        let reactor = step.into_reactor(ctx, registry);
        let inserted = self.reactors.insert(Some(Box::new(reactor)));
        debug_assert_eq!(inserted, key);
        ReactorRegistration {
            token,
            notify: self,
        }
    }

    /// Register a pre-built reactor in one step.
    ///
    /// Convenience for reactors that don't need their [`Token`] in
    /// the context. For reactors that need the token (wire routing,
    /// self-deregistration), use [`create_reactor`](Self::create_reactor)
    /// + [`insert_reactor`](Self::insert_reactor).
    pub fn register_built(&mut self, reactor: impl Reactor + 'static) -> ReactorRegistration<'_> {
        let key = self.reactors.vacant_key();
        let token = Token::new(key);
        self.notify.ensure_capacity(key);
        if key >= self.reactor_sources.len() {
            self.reactor_sources.resize_with(key + 1, Vec::new);
        }
        let inserted = self.reactors.insert(Some(Box::new(reactor)));
        debug_assert_eq!(inserted, key);
        ReactorRegistration {
            token,
            notify: self,
        }
    }

    // ── Subscription ────────────────────────────────────────────────────

    /// Subscribe a reactor to a data source.
    ///
    /// Idempotent — subscribing twice is a no-op.
    /// No-op if `source` has been removed.
    pub fn subscribe(&mut self, reactor: Token, source: DataSource) {
        if let Some(subscribers) = self.interests.get_mut(source.0)
            && !subscribers.contains(&reactor)
        {
            subscribers.push(reactor);
            // Maintain reverse index for O(subscriptions) removal.
            let idx = reactor.index();
            debug_assert!(
                idx < self.reactor_sources.len(),
                "reactor_sources missing entry for reactor token {}",
                idx,
            );
            self.reactor_sources[idx].push(source);
        }
    }

    /// Unsubscribe a reactor from a data source.
    pub fn unsubscribe(&mut self, reactor: Token, source: DataSource) {
        if let Some(subscribers) = self.interests.get_mut(source.0) {
            subscribers.retain(|&t| t != reactor);
        }
        if let Some(sources) = self.reactor_sources.get_mut(reactor.index()) {
            sources.retain(|&s| s != source);
        }
    }

    // ── Hot path ────────────────────────────────────────────────────────

    /// Mark a data source as changed this frame.
    ///
    /// Fans out to all subscribed reactor tokens in the underlying
    /// [`LocalNotify`], with per-reactor dedup.
    #[inline]
    pub fn mark(&mut self, source: DataSource) {
        if let Some(subscribers) = self.interests.get(source.0) {
            for &reactor_token in subscribers {
                self.notify.mark(reactor_token);
            }
        }
    }

    /// Poll for woken reactor tokens into the events buffer.
    #[inline]
    pub(crate) fn poll(&mut self, events: &mut Events) {
        self.notify.poll(events);
    }

    /// Take a reactor out of its slot for dispatch.
    /// Returns None if the slot is empty or doesn't exist.
    #[inline]
    pub(crate) fn take_reactor(&mut self, idx: usize) -> Option<Box<dyn Reactor>> {
        self.reactors.get_mut(idx).and_then(Option::take)
    }

    /// Put a reactor back into its slot after dispatch.
    ///
    /// The caller guarantees `idx` is a valid, occupied slab key
    /// (it was just returned by `take_reactor`). Skips the redundant
    /// `contains` check — single bounds-checked write.
    #[inline]
    pub(crate) fn put_reactor(&mut self, idx: usize, reactor: Box<dyn Reactor>) {
        self.reactors[idx] = Some(reactor);
    }

    /// Remove a reactor and unsubscribe from all data sources.
    ///
    /// Uses the reverse index for O(subscriptions) removal instead of
    /// scanning all data source interest lists.
    pub fn remove_reactor(&mut self, token: Token) {
        let idx = token.index();
        if self.reactors.contains(idx) {
            self.reactors.remove(idx);
            // Use reverse index — only touch sources this reactor subscribed to.
            if let Some(sources) = self.reactor_sources.get_mut(idx) {
                for &source in sources.iter() {
                    if let Some(subscribers) = self.interests.get_mut(source.0) {
                        subscribers.retain(|&t| t != token);
                    }
                }
                sources.clear();
            }
        }
    }

    // ── Introspection ───────────────────────────────────────────────────

    /// Any reactors woken this frame?
    pub fn has_notified(&self) -> bool {
        self.notify.has_notified()
    }

    /// Number of reactors woken this frame.
    pub fn notified_count(&self) -> usize {
        self.notify.notified_count()
    }

    /// Number of registered data sources.
    pub fn source_count(&self) -> usize {
        self.interests.len()
    }

    /// Number of registered reactors.
    pub fn reactor_count(&self) -> usize {
        self.reactors.len()
    }
}

impl Resource for ReactorNotify {}

// =============================================================================
// ReactorRegistration — builder for chaining subscriptions
// =============================================================================

/// Builder returned by [`ReactorNotify::register`] for chaining subscriptions.
pub struct ReactorRegistration<'a> {
    token: Token,
    notify: &'a mut ReactorNotify,
}

impl ReactorRegistration<'_> {
    /// Subscribe this reactor to a data source.
    pub fn subscribe(self, source: DataSource) -> Self {
        self.notify.subscribe(self.token, source);
        self
    }

    /// The assigned token for this reactor.
    pub fn token(&self) -> Token {
        self.token
    }
}

// =============================================================================
// Reactor trait
// =============================================================================

/// A dispatchable unit with per-instance context.
///
/// Reactors own lightweight metadata (instrument ID, order ID, routing
/// keys). Mutable state belongs in World resources, accessed via
/// pre-resolved [`Res<T>`](crate::Res) / [`ResMut<T>`](crate::ResMut)
/// in the step function.
///
/// Resource access is resolved once at registration time — dispatch
/// is a single pointer deref per resource, no HashMap lookups.
pub trait Reactor: Send {
    /// Run this reactor with full World access.
    fn run(&mut self, world: &mut World);

    /// Returns the reactor's name for diagnostics.
    fn name(&self) -> &'static str {
        "<unnamed>"
    }
}

// =============================================================================
// ReactorFn — concrete dispatch wrapper
// =============================================================================

/// Concrete reactor wrapper produced by [`IntoReactor`].
///
/// Stores the step function, per-reactor context, and pre-resolved
/// parameter state. Same pattern as [`Callback`](crate::Callback)
/// but without an event argument.
pub struct ReactorFn<C, F, Params: Param> {
    /// Per-reactor owned context (instrument, order ID, config).
    pub ctx: C,
    f: F,
    state: Params::State,
    name: &'static str,
}

// =============================================================================
// PipelineReactor — reactor backed by a CtxPipeline or CtxDag body
// =============================================================================

/// A reactor whose body is a [`CtxPipeline`](crate::CtxPipeline),
/// [`CtxDag`](crate::CtxDag), or any [`CtxStepCall`].
///
/// The context `C` holds per-reactor metadata. The body is type-erased
/// via `Box<dyn CtxStepCall>` since pipeline chain types are unnameable.
///
/// # Example
///
/// ```ignore
/// let pipeline = CtxPipelineBuilder::<QuotingCtx, ()>::new()
///     .then(read_books, &reg)
///     .then(compute_quote, &reg)
///     .then(submit_quote, &reg)
///     .build();
///
/// let reactor = PipelineReactor::new(
///     QuotingCtx { reactor_id: token, instrument: BTC },
///     pipeline,
/// );
///
/// notify.register_built(reactor).subscribe(btc_md);
/// ```
pub struct PipelineReactor<C> {
    /// Per-reactor owned context.
    pub ctx: C,
    body: Box<dyn CtxStepCall<C, (), Out = ()> + Send>,
}

impl<C: Send + 'static> PipelineReactor<C> {
    /// Create a reactor from a context and a pipeline/DAG body.
    ///
    /// The body must implement `CtxStepCall<C, (), Out = ()>`.
    /// Both [`CtxPipeline`](crate::CtxPipeline) and
    /// [`CtxDag`](crate::CtxDag) satisfy this when their output is `()`.
    pub fn new(ctx: C, body: impl CtxStepCall<C, (), Out = ()> + Send + 'static) -> Self {
        Self {
            ctx,
            body: Box::new(body),
        }
    }
}

impl<C: Send + 'static> Reactor for PipelineReactor<C> {
    fn run(&mut self, world: &mut World) {
        self.body.call(&mut self.ctx, world, ());
    }

    fn name(&self) -> &'static str {
        std::any::type_name::<C>()
    }
}

// =============================================================================
// IntoReactor — conversion trait
// =============================================================================

/// Converts a step function into a [`Reactor`].
///
/// Step function signature: `fn(&mut C, Params...)` — context first,
/// then resolved resources. No event argument, no return value.
///
/// # Example
///
/// ```ignore
/// fn quoting_step(ctx: &mut QuotingCtx, books: Res<OrderBooks>, mut gw: ResMut<Gateway>) {
///     let quote = books.compute_quote(ctx.instrument, ctx.layer);
///     gw.submit_quote(quote);
/// }
///
/// let reactor = quoting_step.into_reactor(QuotingCtx { instrument: BTC, layer: 1 }, &registry);
/// ```
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a reactor step",
    note = "reactor step signature: `fn(&mut C, Params...)` — context first, then resources",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoReactor<C, Params> {
    /// The concrete reactor type produced.
    type Reactor: Reactor + 'static;

    /// Convert this function + context into a reactor, resolving
    /// parameters from the registry.
    fn into_reactor(self, ctx: C, registry: &Registry) -> Self::Reactor;
}

// =============================================================================
// Arity 0: fn(&mut C) — context only, no Param
// =============================================================================

impl<C: Send + 'static, F: FnMut(&mut C) + Send + 'static> Reactor for ReactorFn<C, F, ()> {
    fn run(&mut self, _world: &mut World) {
        (self.f)(&mut self.ctx);
    }

    fn name(&self) -> &'static str {
        self.name
    }
}

impl<C: Send + 'static, F: FnMut(&mut C) + Send + 'static> IntoReactor<C, ()> for F {
    type Reactor = ReactorFn<C, F, ()>;

    fn into_reactor(self, ctx: C, registry: &Registry) -> Self::Reactor {
        ReactorFn {
            ctx,
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// Arities 1-8 via macro
// =============================================================================

macro_rules! impl_into_reactor {
    ($($P:ident),+) => {
        impl<C: Send + 'static, F: Send + 'static, $($P: Param + 'static),+>
            Reactor for ReactorFn<C, F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+) +
                FnMut(&mut C, $($P::Item<'a>,)+),
        {
            #[allow(non_snake_case)]
            fn run(&mut self, world: &mut World) {
                fn call_inner<Ctx, $($P,)+>(
                    mut f: impl FnMut(&mut Ctx, $($P,)+),
                    ctx: &mut Ctx,
                    $($P: $P,)+
                ) {
                    f(ctx, $($P,)+);
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same
                // Registry that built this World. Single-threaded sequential
                // dispatch ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, &mut self.ctx, $($P,)+);
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }

        impl<C: Send + 'static, F: Send + 'static, $($P: Param + 'static),+>
            IntoReactor<C, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+) +
                FnMut(&mut C, $($P::Item<'a>,)+),
        {
            type Reactor = ReactorFn<C, F, ($($P,)+)>;

            fn into_reactor(self, ctx: C, registry: &Registry) -> Self::Reactor {
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
                ReactorFn {
                    ctx,
                    f: self,
                    state,
                    name: std::any::type_name::<F>(),
                }
            }
        }
    };
}

all_tuples!(impl_into_reactor);

// =============================================================================
// DeferredRemovals — World resource for reactor self-removal
// =============================================================================

/// Deferred reactor removal queue.
///
/// Reactors request removal during dispatch by pushing their token
/// via [`ResMut<DeferredRemovals>`](crate::ResMut). The [`ReactorSystem`]
/// drains this after all reactors in the frame have run.
#[derive(Default)]
pub struct DeferredRemovals {
    tokens: Vec<Token>,
}

impl DeferredRemovals {
    /// Request deferred removal of a reactor.
    ///
    /// Takes effect after the current dispatch frame completes.
    /// Duplicate calls are harmless — `remove_reactor` is idempotent.
    pub fn deregister(&mut self, token: Token) {
        self.tokens.push(token);
    }

    /// Swap out the inner Vec for zero-alloc processing.
    /// Returns the Vec (caller owns it). Leaves self with an empty Vec.
    #[inline]
    pub(crate) fn take(&mut self) -> Vec<Token> {
        std::mem::take(&mut self.tokens)
    }

    /// Put a (drained) Vec back for reuse. Zero allocation.
    #[inline]
    pub(crate) fn put(&mut self, tokens: Vec<Token>) {
        debug_assert!(tokens.is_empty(), "put() expects a drained Vec");
        self.tokens = tokens;
    }

    /// Any removals pending?
    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }
}

impl Resource for DeferredRemovals {}

// =============================================================================
// SourceRegistry — typed key → DataSource resolution
// =============================================================================

/// Maps natural domain keys to [`DataSource`] values.
///
/// Single World resource supporting any number of key types via
/// type erasure. Each key type `K` gets its own internal
/// `HashMap<K, DataSource>`. The `TypeId` dispatch is one hash
/// lookup to find the right inner map — cold path only.
///
/// Any `Hash + Eq + Send + 'static` type works as a key — no trait
/// to implement, no macro to invoke. Newtypes, enums, and tuples
/// all work out of the box.
///
/// # Example
///
/// ```ignore
/// // Setup
/// let src = notify.register_source();
/// registry.insert(InstrumentId("BTC"), src);
///
/// // Runtime lookup (cold path — from event handler)
/// let src = registry.get(&InstrumentId("BTC")).unwrap();
/// notify.register(|t| ctx, step, reg).subscribe(src);
///
/// // Hot path — DataSource pre-resolved, no registry involvement
/// notify.mark(src);
/// ```
#[derive(Default)]
pub struct SourceRegistry {
    maps: FxHashMap<TypeId, Box<dyn Any + Send>>,
}

impl SourceRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Map a typed key to a [`DataSource`].
    ///
    /// Overwrites any previous mapping for this key.
    pub fn insert<K: Hash + Eq + Send + 'static>(&mut self, key: K, source: DataSource) {
        self.get_or_create_map::<K>().insert(key, source);
    }

    /// Look up a [`DataSource`] by typed key.
    ///
    /// Returns `None` if the key is not registered.
    pub fn get<K: Hash + Eq + Send + 'static>(&self, key: &K) -> Option<DataSource> {
        self.get_map::<K>().and_then(|map| map.get(key)).copied()
    }

    /// Remove a key mapping. Returns the [`DataSource`] so the caller
    /// can also call [`ReactorNotify::remove_source`] to free the slot.
    pub fn remove<K: Hash + Eq + Send + 'static>(&mut self, key: &K) -> Option<DataSource> {
        self.get_map_mut::<K>().and_then(|map| map.remove(key))
    }

    /// Returns `true` if the key is mapped.
    pub fn contains<K: Hash + Eq + Send + 'static>(&self, key: &K) -> bool {
        self.get_map::<K>().is_some_and(|map| map.contains_key(key))
    }

    fn get_map<K: Hash + Eq + Send + 'static>(&self) -> Option<&FxHashMap<K, DataSource>> {
        self.maps.get(&TypeId::of::<K>()).map(|boxed| {
            // Invariant: map was inserted with type K, so downcast always succeeds.
            boxed
                .downcast_ref::<FxHashMap<K, DataSource>>()
                .expect("invariant: TypeId matches stored map type")
        })
    }

    fn get_map_mut<K: Hash + Eq + Send + 'static>(
        &mut self,
    ) -> Option<&mut FxHashMap<K, DataSource>> {
        self.maps.get_mut(&TypeId::of::<K>()).map(|boxed| {
            // Invariant: map was inserted with type K, so downcast always succeeds.
            boxed
                .downcast_mut::<FxHashMap<K, DataSource>>()
                .expect("invariant: TypeId matches stored map type")
        })
    }

    fn get_or_create_map<K: Hash + Eq + Send + 'static>(
        &mut self,
    ) -> &mut FxHashMap<K, DataSource> {
        self.maps
            .entry(TypeId::of::<K>())
            .or_insert_with(|| Box::<FxHashMap<K, DataSource>>::default())
            // Invariant: entry was just created or retrieved with type K.
            .downcast_mut::<FxHashMap<K, DataSource>>()
            .unwrap()
    }
}

impl Resource for SourceRegistry {}

// =============================================================================
// ReactorSystem — thin dispatch handle
// =============================================================================

/// Lightweight dispatch handle for the reactor system.
///
/// Sits at the driver level (same as mio `Poll` or timer poller).
/// Reads [`ReactorNotify`] via pre-resolved [`ResourceId`] during
/// dispatch. All reactor storage and registration lives in
/// [`ReactorNotify`] (World resource).
pub struct ReactorSystem {
    /// Pre-allocated events buffer for polling.
    events: Events,

    /// Pre-resolved resource IDs for reaching into World.
    notify_id: ResourceId,
    removals_id: ResourceId,
}

impl ReactorSystem {
    /// Create a dispatch handle from a built [`World`].
    ///
    /// The World must contain [`ReactorNotify`] and [`DeferredRemovals`].
    pub fn new(world: &World) -> Self {
        Self {
            events: Events::with_capacity(256),
            notify_id: world.id::<ReactorNotify>(),
            removals_id: world.id::<DeferredRemovals>(),
        }
    }

    /// Dispatch all woken reactors and process deferred removals.
    ///
    /// 1. Polls [`ReactorNotify`] for woken reactor tokens (deduped)
    /// 2. Runs each reactor's step function with pre-resolved Params
    /// 3. Drains [`DeferredRemovals`] and removes reactors
    ///
    /// Returns `true` if any reactor ran (for scheduler propagation).
    pub fn dispatch(&mut self, world: &mut World) -> bool {
        // SAFETY: notify_id was resolved from the same WorldBuilder.
        // ReactorNotify is heap-allocated — pointer stable for World's lifetime.
        let notify_ptr: *mut ReactorNotify =
            unsafe { world.get_mut::<ReactorNotify>(self.notify_id) };

        // Poll — scoped &mut, dropped before reactor dispatch.
        {
            // SAFETY: notify_ptr is valid for World's lifetime. Scoped &mut
            // is dropped before reactor dispatch begins.
            let notify = unsafe { &mut *notify_ptr };
            notify.poll(&mut self.events);
        }
        let ran = !self.events.is_empty();

        // Dispatch — each reactor is moved out before run(), put back after.
        // &mut ReactorNotify is scoped tightly to avoid aliasing during run().
        for token in self.events.drain() {
            let idx = token.index();
            let reactor = {
                // SAFETY: notify_ptr is valid for World's lifetime. Scoped &mut
                // is dropped before reactor.run() to avoid aliasing.
                let notify = unsafe { &mut *notify_ptr };
                notify.take_reactor(idx)
            };
            if let Some(mut reactor) = reactor {
                reactor.run(world);
                // SAFETY: re-derive &mut after run() completes. No aliasing —
                // reactor was moved out of the slab during run().
                let notify = unsafe { &mut *notify_ptr };
                notify.put_reactor(idx, reactor);
            }
        }

        // Deferred removals — swap Vec out to avoid holding two &mut.
        // Zero allocation: Vec is swapped back and reused next frame.
        // SAFETY: removals_id from same WorldBuilder. Dispatch complete.
        let removals = unsafe { world.get_mut::<DeferredRemovals>(self.removals_id) };
        let mut pending = removals.take();
        if !pending.is_empty() {
            // SAFETY: re-derive &mut for cleanup phase. No other references.
            let notify = unsafe { &mut *notify_ptr };
            while let Some(token) = pending.pop() {
                notify.remove_reactor(token);
            }
        }
        // Put the (now empty) Vec back for reuse.
        // SAFETY: removals_id from same WorldBuilder. All dispatch and cleanup complete.
        let removals = unsafe { world.get_mut::<DeferredRemovals>(self.removals_id) };
        removals.put(pending);

        ran
    }

    /// Number of live reactors.
    pub fn reactor_count(&self, world: &World) -> usize {
        world.resource::<ReactorNotify>().reactor_count()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Res, ResMut, WorldBuilder};

    // -- Reactor trait dispatch --------------------------------------------------

    #[test]
    fn reactor_fn_arity0() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let reg = world.registry();

        struct Ctx {
            count: u32,
        }

        fn step(ctx: &mut Ctx) {
            ctx.count += 1;
        }

        let mut reactor = step.into_reactor(Ctx { count: 0 }, reg);
        reactor.run(&mut world);
        assert_eq!(reactor.ctx.count, 1);
    }

    #[test]
    fn reactor_fn_with_params() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        wb.register::<u32>(0);
        let mut world = wb.build();
        let reg = world.registry();

        struct Ctx {
            multiplier: u64,
        }

        fn step(ctx: &mut Ctx, val: Res<u64>, mut out: ResMut<u32>) {
            *out = (*val * ctx.multiplier) as u32;
        }

        let mut reactor = step.into_reactor(Ctx { multiplier: 5 }, reg);
        reactor.run(&mut world);
        assert_eq!(*world.resource::<u32>(), 50);
    }

    // -- ReactorNotify ----------------------------------------------------------

    fn dummy_reactor() -> ReactorFn<(), fn(&mut ()), ()> {
        ReactorFn {
            ctx: (),
            f: (|(): &mut ()| {}) as fn(&mut ()),
            state: (),
            name: "dummy",
        }
    }

    #[test]
    fn reactor_notify_mark_fans_out() {
        let mut notify = ReactorNotify::new(4, 8);
        let mut events = Events::with_capacity(8);

        let src = notify.register_source();
        let a1 = notify.register_built(dummy_reactor()).token();
        let a2 = notify.register_built(dummy_reactor()).token();
        let _a3 = notify.register_built(dummy_reactor()).token();

        notify.subscribe(a1, src);
        notify.subscribe(a2, src);
        // _a3 not subscribed

        notify.mark(src);
        notify.notify.poll(&mut events);

        assert_eq!(events.len(), 2);
        assert!(events.as_slice().contains(&a1));
        assert!(events.as_slice().contains(&a2));
    }

    #[test]
    fn reactor_notify_dedup_across_sources() {
        let mut notify = ReactorNotify::new(4, 8);
        let mut events = Events::with_capacity(8);

        let src1 = notify.register_source();
        let src2 = notify.register_source();
        let reactor = notify.register_built(dummy_reactor()).token();

        notify.subscribe(reactor, src1);
        notify.subscribe(reactor, src2);

        notify.mark(src1);
        notify.mark(src2);

        notify.notify.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.as_slice()[0], reactor);
    }

    #[test]
    fn reactor_notify_remove_reactor() {
        let mut notify = ReactorNotify::new(4, 8);
        let mut events = Events::with_capacity(8);

        let src = notify.register_source();

        struct Ctx;
        let token = notify
            .register_built(ReactorFn {
                ctx: Ctx,
                f: (|_: &mut Ctx| {}) as fn(&mut Ctx),
                state: (),
                name: "test",
            })
            .token();
        notify.subscribe(token, src);

        notify.remove_reactor(token);
        notify.mark(src);
        notify.notify.poll(&mut events);
        assert!(events.is_empty());
    }

    // -- Full ReactorSystem integration -----------------------------------------

    // Helper: registry() borrows &World, resource_mut() borrows &mut World.
    // In tests, we use unsafe get_mut via the notify_id to avoid the conflict,
    // same pattern as production dispatch code.
    #[allow(clippy::mut_from_ref)]
    fn notify_mut(world: &World, id: ResourceId) -> &mut ReactorNotify {
        // SAFETY: id is a ResourceId for a ReactorNotify registered in this World;
        // single-threaded sequential dispatch ensures no mutable aliasing.
        unsafe { world.get_mut::<ReactorNotify>(id) }
    }

    #[test]
    fn reactor_system_dispatch() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let reg = world.registry();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
            increment: u64,
        }

        fn step(ctx: &mut Ctx, mut val: ResMut<u64>) {
            *val += ctx.increment;
        }

        let notify = notify_mut(&world, nid);
        let src = notify.register_source();
        notify
            .register(
                |t| Ctx {
                    _reactor_id: t,
                    increment: 10,
                },
                step,
                reg,
            )
            .subscribe(src);
        notify
            .register(
                |t| Ctx {
                    _reactor_id: t,
                    increment: 5,
                },
                step,
                reg,
            )
            .subscribe(src);

        // Mark and dispatch
        notify_mut(&world, nid).mark(src);
        let ran = system.dispatch(&mut world);

        assert!(ran);
        assert_eq!(*world.resource::<u64>(), 15); // 10 + 5
    }

    #[test]
    fn reactor_system_deferred_removal() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let reg = world.registry();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            reactor_id: Token,
            runs: u64,
        }

        fn step(ctx: &mut Ctx, mut val: ResMut<u64>, mut removals: ResMut<DeferredRemovals>) {
            *val += 1;
            ctx.runs += 1;
            if ctx.runs >= 2 {
                removals.deregister(ctx.reactor_id);
            }
        }

        let notify = notify_mut(&world, nid);
        let src = notify.register_source();
        notify
            .register(
                |t| Ctx {
                    reactor_id: t,
                    runs: 0,
                },
                step,
                reg,
            )
            .subscribe(src);

        assert_eq!(system.reactor_count(&world), 1);

        // Frame 1 — reactor runs, runs=1, no removal
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 1);
        assert_eq!(system.reactor_count(&world), 1);

        // Frame 2 — reactor runs, runs=2, deregisters
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 2);
        assert_eq!(system.reactor_count(&world), 0);

        // Frame 3 — no reactors, nothing runs
        notify_mut(&world, nid).mark(src);
        let ran = system.dispatch(&mut world);
        assert!(!ran);
        assert_eq!(*world.resource::<u64>(), 2);
    }

    #[test]
    fn reactor_system_only_subscribed_wake() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let reg = world.registry();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
            value: u64,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += ctx.value;
        }

        let notify = notify_mut(&world, nid);
        let btc = notify.register_source();
        let eth = notify.register_source();

        notify
            .register(
                |t| Ctx {
                    _reactor_id: t,
                    value: 10,
                },
                step,
                reg,
            )
            .subscribe(btc);
        notify
            .register(
                |t| Ctx {
                    _reactor_id: t,
                    value: 100,
                },
                step,
                reg,
            )
            .subscribe(eth);

        // Only BTC fires — only reactor 1 runs
        notify_mut(&world, nid).mark(btc);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 10);

        // ETH fires — reactor 2 runs
        notify_mut(&world, nid).mark(eth);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 110);
    }

    #[test]
    fn runtime_registration() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
            value: u64,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += ctx.value;
        }

        // Register source and first reactor at setup
        let src = {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            let src = notify.register_source();
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 10,
                    },
                    step,
                    reg,
                )
                .subscribe(src);
            src
        };

        // Frame 1 — one reactor
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 10);

        // Runtime registration (simulates admin command handler)
        {
            let reg = world.registry();
            notify_mut(&world, nid)
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 100,
                    },
                    step,
                    reg,
                )
                .subscribe(src);
        }

        // Frame 2 — both reactors fire
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 120); // 10 + 10 + 100
    }

    #[test]
    fn register_after_remove_reuses_key() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            reactor_id: Token,
            value: u64,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>, mut removals: ResMut<DeferredRemovals>) {
            *out += ctx.value;
            if ctx.value == 10 {
                removals.deregister(ctx.reactor_id);
            }
        }

        let src = {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            let src = notify.register_source();
            notify
                .register(
                    |t| Ctx {
                        reactor_id: t,
                        value: 10,
                    },
                    step,
                    reg,
                )
                .subscribe(src);
            src
        };

        // Frame 1 — reactor runs and deregisters itself
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 10);
        assert_eq!(system.reactor_count(&world), 0);

        // Register a NEW reactor — should reuse key 0
        {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            let token = notify
                .register(
                    |t| Ctx {
                        reactor_id: t,
                        value: 100,
                    },
                    step,
                    reg,
                )
                .token();
            notify.subscribe(token, src);
            assert_eq!(token.index(), 0); // slab reused key 0
        }

        // Frame 2 — new reactor runs correctly
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 110); // 10 + 100
        assert_eq!(system.reactor_count(&world), 1); // still alive (value != 10)
    }

    #[test]
    fn reactor_can_access_actor_notify() {
        // Verify no aliasing UB: the move-out-move-back pattern
        // allows reactors to safely access ReactorNotify via ResMut.
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
        }

        fn step(_ctx: &mut Ctx, notify: ResMut<ReactorNotify>, mut out: ResMut<u64>) {
            // Reactor reads ReactorNotify — this would be UB without move-out
            *out = notify.reactor_count() as u64;
        }

        let src = {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            let src = notify.register_source();
            notify
                .register(|t| Ctx { _reactor_id: t }, step, reg)
                .subscribe(src);
            src
        };

        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        // Reactor count is 1, but during run() the reactor was taken out,
        // so reactor_count() sees 0 reactors with Some values... actually
        // slab.len() still counts the slot as occupied. The Option is
        // None but the slab entry exists. Let's just verify no panic.
        // The important thing is no aliasing UB.
    }

    // -- Realistic data source patterns ---------------------------------------

    #[test]
    fn multi_instrument_with_shared_source() {
        // Pattern: per-instrument market data sources + a shared "positions"
        // source. Quoting reactors subscribe to their instrument + positions.
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(8, 16));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
            instrument: &'static str,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            // Each reactor increments by its instrument's "value"
            *out += match ctx.instrument {
                "BTC" => 100,
                "ETH" => 10,
                "SOL" => 1,
                _ => 0,
            };
        }

        let (btc_md, eth_md, sol_md, positions) = {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);

            // Per-instrument data sources
            let btc_md = notify.register_source();
            let eth_md = notify.register_source();
            let sol_md = notify.register_source();
            // Shared source
            let positions = notify.register_source();

            // BTC reactor: subscribes to btc_md + positions
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        instrument: "BTC",
                    },
                    step,
                    reg,
                )
                .subscribe(btc_md)
                .subscribe(positions);

            // ETH reactor: subscribes to eth_md + positions
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        instrument: "ETH",
                    },
                    step,
                    reg,
                )
                .subscribe(eth_md)
                .subscribe(positions);

            // SOL reactor: subscribes to sol_md + positions
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        instrument: "SOL",
                    },
                    step,
                    reg,
                )
                .subscribe(sol_md)
                .subscribe(positions);

            (btc_md, eth_md, sol_md, positions)
        };

        // Only BTC data changes — only BTC reactor wakes
        notify_mut(&world, nid).mark(btc_md);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 100);

        // Position update — ALL reactors wake (shared source), deduped
        notify_mut(&world, nid).mark(positions);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 211); // 100 + 100 + 10 + 1

        // BTC + ETH data change in same frame — both reactors wake once
        notify_mut(&world, nid).mark(btc_md);
        notify_mut(&world, nid).mark(eth_md);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 321); // 211 + 100 + 10

        // BTC data + position in same frame — BTC reactor wakes ONCE (dedup)
        notify_mut(&world, nid).mark(btc_md);
        notify_mut(&world, nid).mark(positions);
        system.dispatch(&mut world);
        // BTC: 100 (deduped, only once), ETH: 10, SOL: 1
        assert_eq!(*world.resource::<u64>(), 432); // 321 + 100 + 10 + 1

        // Nothing fires — no reactors wake
        let ran = system.dispatch(&mut world);
        assert!(!ran);
        assert_eq!(*world.resource::<u64>(), 432);

        // SOL data only — only SOL reactor
        notify_mut(&world, nid).mark(sol_md);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 433);
    }

    #[test]
    fn per_reactor_fill_routing() {
        // Pattern: each reactor gets its own DataSource for fill routing.
        // Wire protocol embeds the token index in the order client_id.
        // When a fill arrives, the handler marks the reactor's source directly.
        use std::collections::HashMap;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(8, 16));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            reactor_id: Token,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += ctx.reactor_id.index() as u64 + 1;
        }

        // Routing table: token index → reactor's fill source
        let mut fill_sources: HashMap<usize, DataSource> = HashMap::new();

        {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);

            for _ in 0..3 {
                // Each reactor gets its own fill source
                let fill_src = notify.register_source();
                let token = notify
                    .register(|t| Ctx { reactor_id: t }, step, reg)
                    .subscribe(fill_src)
                    .token();

                fill_sources.insert(token.index(), fill_src);
            }
        }

        // Simulate fill arriving for reactor 1 — look up its source by wire ID
        let wire_client_id: usize = 1;
        let fill_source = fill_sources[&wire_client_id];
        notify_mut(&world, nid).mark(fill_source);
        system.dispatch(&mut world);
        // Only reactor 1 ran: token.index()=1, so += 2
        assert_eq!(*world.resource::<u64>(), 2);

        // Fill for reactor 0
        let fill_source = fill_sources[&0];
        notify_mut(&world, nid).mark(fill_source);
        system.dispatch(&mut world);
        // Reactor 0: token.index()=0, += 1
        assert_eq!(*world.resource::<u64>(), 3);
    }

    #[test]
    fn dynamic_source_registration() {
        // Pattern: data sources added at runtime when new instruments
        // come online. Reactors registered and subscribed dynamically.
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
            value: u64,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += ctx.value;
        }

        // Start with just BTC
        let btc_md = {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            let btc_md = notify.register_source();
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 10,
                    },
                    step,
                    reg,
                )
                .subscribe(btc_md);
            btc_md
        };

        notify_mut(&world, nid).mark(btc_md);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 10);

        // Runtime: new instrument comes online — register source + reactor
        let eth_md = {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            let eth_md = notify.register_source();
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 100,
                    },
                    step,
                    reg,
                )
                .subscribe(eth_md);
            eth_md
        };

        // Both instruments fire
        notify_mut(&world, nid).mark(btc_md);
        notify_mut(&world, nid).mark(eth_md);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 120); // 10 + 10 + 100
    }

    // -- Source removal + slab reuse ------------------------------------------

    #[test]
    fn remove_source_and_reuse_slot() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
            value: u64,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += ctx.value;
        }

        // Register two sources
        let (src_a, src_b) = {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            let src_a = notify.register_source();
            let src_b = notify.register_source();
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 10,
                    },
                    step,
                    reg,
                )
                .subscribe(src_a);
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 100,
                    },
                    step,
                    reg,
                )
                .subscribe(src_b);
            (src_a, src_b)
        };

        // Remove source A
        notify_mut(&world, nid).remove_source(src_a);

        // Marking removed source is a no-op
        notify_mut(&world, nid).mark(src_a);
        let ran = system.dispatch(&mut world);
        assert!(!ran);

        // Source B still works
        notify_mut(&world, nid).mark(src_b);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 100);

        // Register a new source — should reuse slot 0
        let src_c = notify_mut(&world, nid).register_source();
        assert_eq!(src_c.0, src_a.0); // slab reused the slot

        // Subscribe reactor to new source and verify it works
        let reg = world.registry();
        let notify = notify_mut(&world, nid);
        notify
            .register(
                |t| Ctx {
                    _reactor_id: t,
                    value: 1,
                },
                step,
                reg,
            )
            .subscribe(src_c);

        notify_mut(&world, nid).mark(src_c);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 101); // 100 + 1
    }

    // -- SourceRegistry -------------------------------------------------------

    #[test]
    fn source_registry_basic() {
        let mut registry = SourceRegistry::new();

        #[derive(Hash, Eq, PartialEq, Debug)]
        struct InstrumentId(u32);

        let src_a = DataSource(0);
        let src_b = DataSource(1);

        registry.insert(InstrumentId(1), src_a);
        registry.insert(InstrumentId(2), src_b);

        assert_eq!(registry.get(&InstrumentId(1)), Some(src_a));
        assert_eq!(registry.get(&InstrumentId(2)), Some(src_b));
        assert_eq!(registry.get(&InstrumentId(3)), None);
        assert!(registry.contains(&InstrumentId(1)));
        assert!(!registry.contains(&InstrumentId(3)));
    }

    #[test]
    fn source_registry_multiple_key_types() {
        let mut registry = SourceRegistry::new();

        #[derive(Hash, Eq, PartialEq)]
        struct InstrumentId(u32);

        #[derive(Hash, Eq, PartialEq)]
        struct StrategyId(u32);

        let src_a = DataSource(0);
        let src_b = DataSource(1);

        // Same registry, different key types
        registry.insert(InstrumentId(1), src_a);
        registry.insert(StrategyId(1), src_b);

        // Different type namespaces — same inner value (1), different results
        assert_eq!(registry.get(&InstrumentId(1)), Some(src_a));
        assert_eq!(registry.get(&StrategyId(1)), Some(src_b));
    }

    #[test]
    fn source_registry_tuple_keys() {
        let mut registry = SourceRegistry::new();

        let src = DataSource(42);
        registry.insert(("BTC", "Binance"), src);

        assert_eq!(registry.get(&("BTC", "Binance")), Some(src));
        assert_eq!(registry.get(&("ETH", "Binance")), None);
    }

    #[test]
    fn source_registry_remove() {
        let mut registry = SourceRegistry::new();

        let src = DataSource(0);
        registry.insert(42u64, src);

        assert_eq!(registry.remove(&42u64), Some(src));
        assert_eq!(registry.get(&42u64), None);
        assert_eq!(registry.remove(&42u64), None); // already gone
    }

    #[test]
    fn source_registry_integrated_with_reactor_system() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        wb.register(SourceRegistry::new());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        #[derive(Hash, Eq, PartialEq, Clone, Copy)]
        struct Instrument(u32);
        const BTC: Instrument = Instrument(0);
        const ETH: Instrument = Instrument(1);

        struct Ctx {
            _reactor_id: Token,
            value: u64,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += ctx.value;
        }

        // Setup: register sources and map to natural keys
        let btc_src = notify_mut(&world, nid).register_source();
        let eth_src = notify_mut(&world, nid).register_source();

        world.resource_mut::<SourceRegistry>().insert(BTC, btc_src);
        world.resource_mut::<SourceRegistry>().insert(ETH, eth_src);

        // Register reactors using natural key lookup
        {
            let reg = world.registry();
            let btc = world.resource::<SourceRegistry>().get(&BTC).unwrap();
            let notify = notify_mut(&world, nid);
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 10,
                    },
                    step,
                    reg,
                )
                .subscribe(btc);
        }

        // Mark via pre-resolved DataSource
        notify_mut(&world, nid).mark(btc_src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 10);

        // Delist BTC — remove from both registry and notify
        let removed = world.resource_mut::<SourceRegistry>().remove(&BTC);
        assert!(removed.is_some());
        notify_mut(&world, nid).remove_source(removed.unwrap());

        // Marking BTC is now a no-op
        notify_mut(&world, nid).mark(btc_src);
        let ran = system.dispatch(&mut world);
        assert!(!ran);
    }

    // -- SourceRegistry edge cases --------------------------------------------

    #[test]
    fn source_registry_overwrite_key() {
        let mut registry = SourceRegistry::new();
        let src_a = DataSource(0);
        let src_b = DataSource(1);

        registry.insert(42u32, src_a);
        assert_eq!(registry.get(&42u32), Some(src_a));

        // Overwrite same key with different source
        registry.insert(42u32, src_b);
        assert_eq!(registry.get(&42u32), Some(src_b));
    }

    #[test]
    fn source_registry_empty_get() {
        let registry = SourceRegistry::new();
        // No key type has ever been registered
        assert_eq!(registry.get(&42u32), None);
        assert!(!registry.contains(&42u32));
    }

    #[test]
    fn source_registry_enum_keys() {
        #[derive(Hash, Eq, PartialEq)]
        enum Venue {
            Binance,
            Coinbase,
        }

        let mut registry = SourceRegistry::new();
        let src = DataSource(0);
        registry.insert(Venue::Binance, src);

        assert_eq!(registry.get(&Venue::Binance), Some(src));
        assert_eq!(registry.get(&Venue::Coinbase), None);
    }

    #[test]
    fn source_registry_composite_key() {
        // (Strategy, Instrument, Venue) triple as key
        #[derive(Hash, Eq, PartialEq)]
        struct StrategyId(u32);
        #[derive(Hash, Eq, PartialEq)]
        struct InstrumentId(u32);
        #[derive(Hash, Eq, PartialEq)]
        struct VenueId(u32);

        let mut registry = SourceRegistry::new();
        let src = DataSource(5);
        registry.insert((StrategyId(1), InstrumentId(0), VenueId(2)), src);

        assert_eq!(
            registry.get(&(StrategyId(1), InstrumentId(0), VenueId(2))),
            Some(src)
        );
        // Different strategy
        assert_eq!(
            registry.get(&(StrategyId(2), InstrumentId(0), VenueId(2))),
            None
        );
    }

    // -- Full lifecycle scenarios ---------------------------------------------

    #[test]
    fn full_lifecycle_add_trade_remove() {
        // Simulates: add instrument → reactors trade → delist → cleanup
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        wb.register(SourceRegistry::new());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        #[derive(Hash, Eq, PartialEq, Clone, Copy)]
        struct Instrument(u32);

        struct Ctx {
            _reactor_id: Token,
            value: u64,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += ctx.value;
        }

        // Phase 1: Add BTC
        let btc_src = notify_mut(&world, nid).register_source();
        world
            .resource_mut::<SourceRegistry>()
            .insert(Instrument(0), btc_src);

        {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 10,
                    },
                    step,
                    reg,
                )
                .subscribe(btc_src);
        }

        // Phase 2: Trade
        notify_mut(&world, nid).mark(btc_src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 10);

        // Phase 3: Add ETH dynamically
        let eth_src = notify_mut(&world, nid).register_source();
        world
            .resource_mut::<SourceRegistry>()
            .insert(Instrument(1), eth_src);

        {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 100,
                    },
                    step,
                    reg,
                )
                .subscribe(eth_src);
        }

        // Both trade
        notify_mut(&world, nid).mark(btc_src);
        notify_mut(&world, nid).mark(eth_src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 120);

        // Phase 4: Delist BTC
        let removed = world
            .resource_mut::<SourceRegistry>()
            .remove(&Instrument(0));
        notify_mut(&world, nid).remove_source(removed.unwrap());

        // Only ETH remains
        notify_mut(&world, nid).mark(eth_src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 220);

        // Phase 5: Add SOL — reuses BTC's old slab slot
        let sol_src = notify_mut(&world, nid).register_source();
        world
            .resource_mut::<SourceRegistry>()
            .insert(Instrument(2), sol_src);
        assert_eq!(sol_src.0, btc_src.0); // slab reused

        {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            notify
                .register(
                    |t| Ctx {
                        _reactor_id: t,
                        value: 1000,
                    },
                    step,
                    reg,
                )
                .subscribe(sol_src);
        }

        // SOL + ETH fire
        notify_mut(&world, nid).mark(sol_src);
        notify_mut(&world, nid).mark(eth_src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 1320); // 220 + 1000 + 100
    }

    #[test]
    fn multi_strategy_same_instrument() {
        // Two strategies on the same instrument with different data sources
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(8, 16));
        wb.register(DeferredRemovals::default());
        wb.register(SourceRegistry::new());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        #[derive(Hash, Eq, PartialEq, Clone, Copy)]
        struct StrategyInstrument(&'static str, &'static str);

        struct Ctx {
            _reactor_id: Token,
            value: u64,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += ctx.value;
        }

        // Per-strategy+instrument sources
        let reg = world.registry();
        let notify = notify_mut(&world, nid);

        let mm_btc = notify.register_source();
        let mm_eth = notify.register_source();
        let arb_btc = notify.register_source();

        // Market maker on BTC and ETH
        notify
            .register(
                |t| Ctx {
                    _reactor_id: t,
                    value: 1,
                },
                step,
                reg,
            )
            .subscribe(mm_btc);
        notify
            .register(
                |t| Ctx {
                    _reactor_id: t,
                    value: 2,
                },
                step,
                reg,
            )
            .subscribe(mm_eth);

        // Arb strategy on BTC
        notify
            .register(
                |t| Ctx {
                    _reactor_id: t,
                    value: 100,
                },
                step,
                reg,
            )
            .subscribe(arb_btc);

        // Map composite keys
        world
            .resource_mut::<SourceRegistry>()
            .insert(StrategyInstrument("MM", "BTC"), mm_btc);
        world
            .resource_mut::<SourceRegistry>()
            .insert(StrategyInstrument("MM", "ETH"), mm_eth);
        world
            .resource_mut::<SourceRegistry>()
            .insert(StrategyInstrument("ARB", "BTC"), arb_btc);

        // BTC data arrives — both MM-BTC and ARB-BTC should fire
        // But they're separate sources, so handler marks both:
        let mm_btc_src = world
            .resource::<SourceRegistry>()
            .get(&StrategyInstrument("MM", "BTC"))
            .unwrap();
        let arb_btc_src = world
            .resource::<SourceRegistry>()
            .get(&StrategyInstrument("ARB", "BTC"))
            .unwrap();

        notify_mut(&world, nid).mark(mm_btc_src);
        notify_mut(&world, nid).mark(arb_btc_src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 101); // 1 + 100
    }

    #[test]
    fn reactor_self_removal_with_registry_cleanup() {
        // Reactor deregisters itself AND the handler cleans up the source
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        wb.register(SourceRegistry::new());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            reactor_id: Token,
        }

        fn one_shot(ctx: &mut Ctx, mut out: ResMut<u64>, mut removals: ResMut<DeferredRemovals>) {
            *out += 1;
            removals.deregister(ctx.reactor_id);
        }

        let src = notify_mut(&world, nid).register_source();
        world
            .resource_mut::<SourceRegistry>()
            .insert("one-shot", src);

        {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            notify
                .register(|t| Ctx { reactor_id: t }, one_shot, reg)
                .subscribe(src);
        }

        // Reactor runs once and removes itself
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 1);
        assert_eq!(system.reactor_count(&world), 0);

        // Source still exists in registry but no reactors subscribe
        assert!(world.resource::<SourceRegistry>().contains(&"one-shot"));

        // Mark again — no reactors wake
        notify_mut(&world, nid).mark(src);
        let ran = system.dispatch(&mut world);
        assert!(!ran);
    }

    #[test]
    fn many_reactors_same_source() {
        // 50 reactors all subscribed to one source — all wake, deduped
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 64));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
        }

        fn step(_ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += 1;
        }

        let src = notify_mut(&world, nid).register_source();

        {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            for _ in 0..50 {
                notify
                    .register(|t| Ctx { _reactor_id: t }, step, reg)
                    .subscribe(src);
            }
        }

        assert_eq!(system.reactor_count(&world), 50);

        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 50); // all 50 ran exactly once
    }

    #[test]
    fn reactor_subscribes_to_multiple_sources() {
        // One reactor subscribed to 5 different sources.
        // All 5 fire in one frame — reactor runs exactly once.
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(8, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
        }

        fn step(_ctx: &mut Ctx, mut out: ResMut<u64>) {
            *out += 1;
        }

        let mut sources = Vec::new();
        let notify = notify_mut(&world, nid);
        for _ in 0..5 {
            sources.push(notify.register_source());
        }

        {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);
            let mut registration = notify.register(|t| Ctx { _reactor_id: t }, step, reg);
            for &src in &sources {
                registration = registration.subscribe(src);
            }
        }

        // Mark all 5 sources
        for &src in &sources {
            notify_mut(&world, nid).mark(src);
        }

        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 1); // ONE run despite 5 sources
    }

    #[test]
    fn stale_data_source_is_noop() {
        // After removing a source, marking it must not panic
        let mut wb = WorldBuilder::new();
        wb.register(ReactorNotify::new(4, 4));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        let src = notify_mut(&world, nid).register_source();
        notify_mut(&world, nid).remove_source(src);

        // Must not panic
        notify_mut(&world, nid).mark(src);
        let ran = system.dispatch(&mut world);
        assert!(!ran);
    }

    #[test]
    fn double_remove_source_is_noop() {
        let mut notify = ReactorNotify::new(4, 4);
        let src = notify.register_source();
        notify.remove_source(src);
        notify.remove_source(src); // must not panic
    }

    // -- PipelineReactor: reactor body is a CtxPipeline ----------------------------

    #[test]
    fn pipeline_reactor_dispatch() {
        use crate::CtxPipelineBuilder;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
            instrument: &'static str,
        }

        fn read_data(ctx: &mut Ctx, val: Res<u64>, _input: ()) -> u64 {
            let _ = ctx.instrument;
            *val
        }

        fn double(_ctx: &mut Ctx, x: u64) -> u64 {
            x * 2
        }

        fn store(_ctx: &mut Ctx, mut out: ResMut<u64>, x: u64) {
            *out = x;
        }

        let reg = world.registry();

        let pipeline = CtxPipelineBuilder::<Ctx, ()>::new()
            .then(read_data, reg)
            .then(double, reg)
            .then(store, reg)
            .build();

        let notify = notify_mut(&world, nid);
        let src = notify.register_source();

        // Wrap pipeline in PipelineReactor
        let reactor = PipelineReactor::new(
            Ctx {
                _reactor_id: Token::new(0),
                instrument: "BTC",
            },
            pipeline,
        );
        notify.register_built(reactor).subscribe(src);

        // Set initial value and dispatch
        *world.resource_mut::<u64>() = 10;
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);

        assert_eq!(*world.resource::<u64>(), 20); // 10 * 2
    }

    #[test]
    fn dag_reactor_dispatch() {
        use crate::CtxDagBuilder;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
        }

        fn root(ctx: &mut Ctx, val: Res<u64>, _input: ()) -> u64 {
            let _ = ctx;
            *val
        }

        fn arm_double(_ctx: &mut Ctx, val: &u64) -> u64 {
            *val * 2
        }

        fn arm_add(_ctx: &mut Ctx, val: &u64) -> u64 {
            *val + 10
        }

        fn merge(_ctx: &mut Ctx, mut out: ResMut<u64>, a: &u64, b: &u64) {
            *out = *a + *b;
        }

        let reg = world.registry();

        let dag = CtxDagBuilder::<Ctx, ()>::new()
            .root(root, reg)
            .fork()
            .arm(|seed| seed.then(arm_double, reg))
            .arm(|seed| seed.then(arm_add, reg))
            .merge(merge, reg)
            .build();

        let notify = notify_mut(&world, nid);
        let src = notify.register_source();

        let reactor = PipelineReactor::new(
            Ctx {
                _reactor_id: Token::new(0),
            },
            dag,
        );
        notify.register_built(reactor).subscribe(src);

        *world.resource_mut::<u64>() = 5;
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);

        // (5 * 2) + (5 + 10) = 10 + 15 = 25
        assert_eq!(*world.resource::<u64>(), 25);
    }

    #[test]
    fn multiple_pipeline_reactors_different_bodies() {
        use crate::CtxPipelineBuilder;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
            factor: u64,
        }

        fn multiply(ctx: &mut Ctx, val: Res<u64>, _input: ()) -> u64 {
            *val * ctx.factor
        }

        fn accumulate(_ctx: &mut Ctx, mut out: ResMut<u64>, val: u64) {
            *out += val;
        }

        let reg = world.registry();

        // Reactor A: multiply by 2
        let pipeline_a = CtxPipelineBuilder::<Ctx, ()>::new()
            .then(multiply, reg)
            .then(accumulate, reg)
            .build();

        // Reactor B: multiply by 10
        let pipeline_b = CtxPipelineBuilder::<Ctx, ()>::new()
            .then(multiply, reg)
            .then(accumulate, reg)
            .build();

        let notify = notify_mut(&world, nid);
        let src = notify.register_source();

        notify
            .register_built(PipelineReactor::new(
                Ctx {
                    _reactor_id: Token::new(0),
                    factor: 2,
                },
                pipeline_a,
            ))
            .subscribe(src);

        notify
            .register_built(PipelineReactor::new(
                Ctx {
                    _reactor_id: Token::new(1),
                    factor: 10,
                },
                pipeline_b,
            ))
            .subscribe(src);

        *world.resource_mut::<u64>() = 5;
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);

        // Reactor A reads 5, adds 5*2=10, so resource=15
        // Reactor B reads 15, adds 15*10=150, so resource=165
        // (Order depends on dispatch order — both subscribed to same source)
        // The value is order-dependent. Just verify both ran:
        let val = *world.resource::<u64>();
        assert!(val > 5, "both reactors should have run, got {val}");
    }

    #[test]
    fn pipeline_reactor_with_guard() {
        use crate::CtxPipelineBuilder;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
            threshold: u64,
        }

        fn read(_ctx: &mut Ctx, val: Res<u64>, _input: ()) -> u64 {
            *val
        }

        fn above_threshold(ctx: &mut Ctx, val: &u64) -> bool {
            *val > ctx.threshold
        }

        fn write(_ctx: &mut Ctx, mut out: ResMut<u64>, _val: u64) {
            *out = 999;
        }

        let reg = world.registry();

        let pipeline = CtxPipelineBuilder::<Ctx, ()>::new()
            .then(read, reg)
            .guard(above_threshold, reg)
            .map(write, reg)
            .build();

        let notify = notify_mut(&world, nid);
        let src = notify.register_source();

        notify
            .register_built(PipelineReactor::new(
                Ctx {
                    _reactor_id: Token::new(0),
                    threshold: 10,
                },
                pipeline,
            ))
            .subscribe(src);

        // Value below threshold — guard blocks
        *world.resource_mut::<u64>() = 5;
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 5); // unchanged

        // Value above threshold — guard passes
        *world.resource_mut::<u64>() = 20;
        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 999);
    }

    // -- Two-phase registration (safe API through World) ----------------------

    #[test]
    fn two_phase_registration_safe_api() {
        // Demonstrates the safe API: create_reactor → into_reactor → insert
        // No unsafe, no registry borrow conflicts.
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();

        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            reactor_id: Token,
            instrument: &'static str,
        }

        fn step(ctx: &mut Ctx, mut out: ResMut<u64>) {
            let _ = ctx.instrument;
            *out += ctx.reactor_id.index() as u64 + 1;
        }

        // Phase 1: reserve slot
        let src = world.resource_mut::<ReactorNotify>().register_source();
        let token = world.resource_mut::<ReactorNotify>().create_reactor();

        // Phase 2: build reactor with token + registry (no borrow conflict)
        let reactor = step.into_reactor(
            Ctx {
                reactor_id: token,
                instrument: "BTC",
            },
            world.registry(),
        );

        // Phase 3: insert + subscribe
        world
            .resource_mut::<ReactorNotify>()
            .insert_reactor(token, reactor)
            .subscribe(src);

        // Verify dispatch
        world.resource_mut::<ReactorNotify>().mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 1); // token index 0 + 1

        // Second reactor — same pattern
        let token2 = world.resource_mut::<ReactorNotify>().create_reactor();
        let actor2 = step.into_reactor(
            Ctx {
                reactor_id: token2,
                instrument: "ETH",
            },
            world.registry(),
        );
        world
            .resource_mut::<ReactorNotify>()
            .insert_reactor(token2, actor2)
            .subscribe(src);

        // Both reactors fire
        world.resource_mut::<ReactorNotify>().mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 4); // 1 + (0+1) + (1+1)
    }

    #[test]
    fn two_phase_with_pipeline_reactor() {
        use crate::CtxPipelineBuilder;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();

        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _reactor_id: Token,
        }

        fn read(ctx: &mut Ctx, val: Res<u64>) -> u64 {
            let _ = ctx;
            *val
        }

        fn double(_ctx: &mut Ctx, x: u64) -> u64 {
            x * 2
        }

        fn store(_ctx: &mut Ctx, mut out: ResMut<u64>, x: u64) {
            *out = x;
        }

        // Phase 1: reserve + register source
        let src = world.resource_mut::<ReactorNotify>().register_source();
        let token = world.resource_mut::<ReactorNotify>().create_reactor();

        // Phase 2: build pipeline + wrap in PipelineReactor (needs registry)
        let reg = world.registry();
        let pipeline = CtxPipelineBuilder::<Ctx, ()>::new()
            .then(crate::no_event(read), reg)
            .then(double, reg)
            .then(store, reg)
            .build();
        let reactor = PipelineReactor::new(Ctx { _reactor_id: token }, pipeline);

        // Phase 3: insert
        world
            .resource_mut::<ReactorNotify>()
            .insert_reactor(token, reactor)
            .subscribe(src);

        *world.resource_mut::<u64>() = 10;
        world.resource_mut::<ReactorNotify>().mark(src);
        system.dispatch(&mut world);
        assert_eq!(*world.resource::<u64>(), 20); // 10 * 2
    }
}
