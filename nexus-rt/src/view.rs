#![allow(clippy::type_complexity)]
// Pipeline view scopes — borrow a projected view from an event.
//
// `.view::<V>()` opens a scope where steps operate on a read-only
// view constructed from the event. `.end_view()` closes the scope
// and the original event continues unchanged.
//
// Lifetime erasure: the view may borrow from the event (e.g.,
// `OrderView<'a>` with `symbol: &'a str`). IntoRefStep resolves
// against `StaticViewType` ('static stand-in). `with_view` bridges
// the two via a scoped transmute — same pattern as std::thread::scope.

use core::marker::PhantomData;

use crate::pipeline::{ChainCall, IntoRefStep, PipelineChain, RefStepCall};
use crate::world::World;

// =============================================================================
// View trait
// =============================================================================

/// Associates a source type with a projected view via a marker.
///
/// `ViewType<'a>` is the real view with borrowed fields.
/// `StaticViewType` is the same struct with `'static` — used only for
/// step resolution at build time, never observed at runtime.
///
/// # Examples
///
/// ```
/// use nexus_rt::View;
///
/// struct OrderView<'a> { symbol: &'a str, qty: u64 }
/// struct NewOrder { symbol: String, qty: u64 }
///
/// struct AsOrderView;
/// unsafe impl View<NewOrder> for AsOrderView {
///     type ViewType<'a> = OrderView<'a>;
///     type StaticViewType = OrderView<'static>;
///     fn view(source: &NewOrder) -> OrderView<'_> {
///         OrderView { symbol: &source.symbol, qty: source.qty }
///     }
/// }
/// ```
#[diagnostic::on_unimplemented(
    message = "`{Source}` cannot be viewed as `{Self}`",
    note = "implement `View<{Source}>` for your view marker type"
)]
/// # Safety
///
/// `StaticViewType` must be layout-identical to `ViewType<'a>` for any `'a`.
/// They must be the same struct with different lifetime parameters. The
/// framework performs a pointer cast between them in `with_view()`.
///
/// For view structs with borrowed fields (e.g., `&'a str`), use `#[repr(C)]`
/// to guarantee layout stability across lifetime parameters. Rust does not
/// currently guarantee that `repr(Rust)` types with different lifetime
/// parameters have identical layouts, though all current compilers do so.
/// `#[repr(C)]` removes any theoretical risk.
///
/// Incorrect implementations (e.g., `StaticViewType` being a different struct)
/// cause undefined behavior. Use the `#[derive(View)]` macro when available
/// to generate correct implementations.
pub unsafe trait View<Source> {
    /// The view type with the source borrow lifetime.
    type ViewType<'a>
    where
        Source: 'a;

    /// The same type with `'static` — for `IntoRefStep` trait resolution.
    /// Must be layout-identical to `ViewType<'a>` for any `'a`.
    type StaticViewType: 'static;

    /// Construct the view from a borrowed source.
    fn view(source: &Source) -> Self::ViewType<'_>;
}

// =============================================================================
// with_view — scoped lifetime erasure
// =============================================================================

/// Constructs a view, erases its lifetime, runs a closure with `&StaticViewType`,
/// then drops the view. The closure cannot leak the reference.
///
/// # Safety argument
///
/// The view borrows from `source` which is alive for this entire call.
/// The transmute erases the borrow lifetime to `'static` so that
/// `RefStepCall<StaticViewType>` (resolved at build time) can accept it.
/// The closure boundary prevents the `'static` reference from escaping —
/// it's dropped before this function returns.
///
/// This is the same pattern as `std::thread::scope` and `crossbeam::scope`.
#[inline(always)]
fn with_view<Source, V, R>(source: &Source, f: impl for<'a> FnOnce(&'a V::StaticViewType) -> R) -> R
where
    V: View<Source>,
{
    let view = V::view(source);
    // SAFETY: ViewType<'a> and StaticViewType are the same struct with
    // different lifetime parameters. The pointer cast is sound because:
    // 1. The layouts are identical (same repr, same fields) — guaranteed
    //    by the `unsafe trait View` contract.
    // 2. `source` outlives this entire function, so the borrow is valid.
    // 3. The `for<'a> FnOnce(&'a ...)` bound prevents the closure from
    //    storing the reference — it must work for ANY lifetime, so it
    //    cannot assume 'static.
    // 4. The view is explicitly dropped after the closure returns.
    let static_ref: &V::StaticViewType =
        unsafe { &*(std::ptr::from_ref(&view) as *const V::StaticViewType) };
    let result = f(static_ref);
    drop(view);
    result
}

// =============================================================================
// ViewScope — builder for steps inside a view scope
// =============================================================================

/// Builder for steps inside a `.view::<V>()` scope.
///
/// `V` is the view marker (implements [`View<Out>`]). Steps resolve
/// against `V::StaticViewType` via `IntoRefStep`.
pub struct ViewScope<In, Out, V: View<Out>, PrevChain, InnerSteps> {
    prev_chain: PrevChain,
    inner: InnerSteps,
    _marker: PhantomData<(fn(In) -> Out, V)>,
}

impl<In, Out, V: View<Out>, PrevChain> ViewScope<In, Out, V, PrevChain, ()> {
    pub(crate) fn new(prev_chain: PrevChain) -> Self {
        ViewScope {
            prev_chain,
            inner: (),
            _marker: PhantomData,
        }
    }
}

// --- Combinators ---

impl<In, Out, V: View<Out>, PrevChain, InnerSteps> ViewScope<In, Out, V, PrevChain, InnerSteps> {
    /// Observe the view. Side effects via `Res`/`ResMut`.
    /// Step signature: `fn(Params..., &ViewType) -> ()`.
    pub fn tap<Params, S: IntoRefStep<V::StaticViewType, (), Params>>(
        self,
        f: S,
        registry: &crate::world::Registry,
    ) -> ViewScope<In, Out, V, PrevChain, (InnerSteps, ViewTap<S::Step>)> {
        ViewScope {
            prev_chain: self.prev_chain,
            inner: (self.inner, ViewTap(f.into_ref_step(registry))),
            _marker: PhantomData,
        }
    }

    /// Observe the view without side effects (no Params).
    /// Step signature: `fn(&ViewType)`.
    pub fn inspect<S: IntoRefStep<V::StaticViewType, (), ()>>(
        self,
        f: S,
        registry: &crate::world::Registry,
    ) -> ViewScope<In, Out, V, PrevChain, (InnerSteps, ViewTap<S::Step>)> {
        self.tap(f, registry)
    }

    /// Filter the event based on the view. Same as `guard` — returns
    /// `bool` to accept/reject.
    /// Step signature: `fn(Params..., &ViewType) -> bool`.
    pub fn filter<Params, S: IntoRefStep<V::StaticViewType, bool, Params>>(
        self,
        f: S,
        registry: &crate::world::Registry,
    ) -> ViewScope<In, Out, V, PrevChain, (InnerSteps, ViewGuard<S::Step>)> {
        self.guard(f, registry)
    }

    /// Guard the event based on the view.
    /// Step signature: `fn(Params..., &ViewType) -> bool`.
    pub fn guard<Params, S: IntoRefStep<V::StaticViewType, bool, Params>>(
        self,
        f: S,
        registry: &crate::world::Registry,
    ) -> ViewScope<In, Out, V, PrevChain, (InnerSteps, ViewGuard<S::Step>)> {
        ViewScope {
            prev_chain: self.prev_chain,
            inner: (self.inner, ViewGuard(f.into_ref_step(registry))),
            _marker: PhantomData,
        }
    }
}

// --- Step wrappers ---

#[doc(hidden)]
pub struct ViewTap<S>(S);

#[doc(hidden)]
pub struct ViewGuard<S>(S);

// --- ViewSteps trait ---

#[doc(hidden)]
pub trait ViewSteps<V> {
    fn run(&mut self, world: &mut World, view: &V) -> bool;
}

impl<V> ViewSteps<V> for () {
    fn run(&mut self, _world: &mut World, _view: &V) -> bool {
        true
    }
}

impl<V, Prev: ViewSteps<V>, S: RefStepCall<V, Out = ()>> ViewSteps<V> for (Prev, ViewTap<S>) {
    fn run(&mut self, world: &mut World, view: &V) -> bool {
        if !self.0.run(world, view) {
            return false;
        }
        self.1.0.call(world, view);
        true
    }
}

impl<V, Prev: ViewSteps<V>, S: RefStepCall<V, Out = bool>> ViewSteps<V> for (Prev, ViewGuard<S>) {
    fn run(&mut self, world: &mut World, view: &V) -> bool {
        if !self.0.run(world, view) {
            return false;
        }
        self.1.0.call(world, view)
    }
}

// =============================================================================
// end_view
// =============================================================================

impl<In, Out, V, PrevChain, InnerSteps> ViewScope<In, Out, V, PrevChain, InnerSteps>
where
    PrevChain: ChainCall<In, Out = Out>,
    V: View<Out>,
    InnerSteps: ViewSteps<V::StaticViewType>,
{
    /// Close the view scope. The event passes through unchanged.
    pub fn end_view(self) -> PipelineChain<In, Out, ViewNode<PrevChain, InnerSteps, V>> {
        PipelineChain {
            chain: ViewNode {
                prev: self.prev_chain,
                inner: self.inner,
                _marker: PhantomData,
            },
            _marker: PhantomData,
        }
    }

    /// Close the view scope. If any guard rejected, returns `None`.
    pub fn end_view_guarded(
        self,
    ) -> PipelineChain<In, Option<Out>, ViewGuardedNode<PrevChain, InnerSteps, V>> {
        PipelineChain {
            chain: ViewGuardedNode {
                prev: self.prev_chain,
                inner: self.inner,
                _marker: PhantomData,
            },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// Chain nodes
// =============================================================================

#[doc(hidden)]
pub struct ViewNode<Prev, Inner, V> {
    prev: Prev,
    inner: Inner,
    _marker: PhantomData<V>,
}

impl<In, Out, Prev, Inner, V> ChainCall<In> for ViewNode<Prev, Inner, V>
where
    Prev: ChainCall<In, Out = Out>,
    V: View<Out>,
    Inner: ViewSteps<V::StaticViewType>,
{
    type Out = Out;

    fn call(&mut self, world: &mut World, input: In) -> Out {
        let event = self.prev.call(world, input);
        with_view::<Out, V, ()>(&event, |view| {
            self.inner.run(world, view);
        });
        event
    }
}

#[doc(hidden)]
pub struct ViewGuardedNode<Prev, Inner, V> {
    prev: Prev,
    inner: Inner,
    _marker: PhantomData<V>,
}

impl<In, Out, Prev, Inner, V> ChainCall<In> for ViewGuardedNode<Prev, Inner, V>
where
    Prev: ChainCall<In, Out = Out>,
    V: View<Out>,
    Inner: ViewSteps<V::StaticViewType>,
{
    type Out = Option<Out>;

    fn call(&mut self, world: &mut World, input: In) -> Option<Out> {
        let event = self.prev.call(world, input);
        let pass = with_view::<Out, V, bool>(&event, |view| self.inner.run(world, view));
        if pass { Some(event) } else { None }
    }
}

// =============================================================================
// PipelineBuilder / PipelineChain integration
// =============================================================================

impl<In> crate::pipeline::PipelineBuilder<In> {
    /// Open a view scope as the first pipeline step.
    pub fn view<V: View<In>>(self) -> ViewScope<In, In, V, crate::pipeline::IdentityNode, ()> {
        ViewScope::new(crate::pipeline::IdentityNode)
    }
}

impl<In, Out, Chain: ChainCall<In, Out = Out>> PipelineChain<In, Out, Chain> {
    /// Open a view scope. Steps inside operate on a read-only view
    /// constructed from the pipeline's current event.
    ///
    /// `V` is a marker type implementing [`View<Out>`]. Inside the scope,
    /// steps resolve against `V::StaticViewType` — borrowed views work
    /// via lifetime erasure (same pattern as `std::thread::scope`).
    pub fn view<V: View<Out>>(self) -> ViewScope<In, Out, V, Chain, ()> {
        ViewScope::new(self.chain)
    }
}

// =============================================================================
// DagChain / DagArm integration
// =============================================================================

impl<In, Out, V, PrevChain, InnerSteps> ViewScope<In, Out, V, PrevChain, InnerSteps>
where
    PrevChain: ChainCall<In, Out = Out>,
    V: View<Out>,
    InnerSteps: ViewSteps<V::StaticViewType>,
    Out: 'static,
{
    /// Close the view scope, returning a [`DagChain`](crate::dag::DagChain).
    pub fn end_view_dag(self) -> crate::dag::DagChain<In, Out, ViewNode<PrevChain, InnerSteps, V>> {
        crate::dag::DagChain {
            chain: ViewNode {
                prev: self.prev_chain,
                inner: self.inner,
                _marker: PhantomData,
            },
            _marker: PhantomData,
        }
    }

    /// Close a guarded view scope, returning a [`DagChain`](crate::dag::DagChain).
    pub fn end_view_dag_guarded(
        self,
    ) -> crate::dag::DagChain<In, Option<Out>, ViewGuardedNode<PrevChain, InnerSteps, V>> {
        crate::dag::DagChain {
            chain: ViewGuardedNode {
                prev: self.prev_chain,
                inner: self.inner,
                _marker: PhantomData,
            },
            _marker: PhantomData,
        }
    }

    /// Close the view scope, returning a [`DagArm`](crate::dag::DagArm).
    pub fn end_view_arm(self) -> crate::dag::DagArm<In, Out, ViewNode<PrevChain, InnerSteps, V>> {
        crate::dag::DagArm {
            chain: ViewNode {
                prev: self.prev_chain,
                inner: self.inner,
                _marker: PhantomData,
            },
            _marker: PhantomData,
        }
    }

    /// Close a guarded view scope, returning a [`DagArm`](crate::dag::DagArm).
    pub fn end_view_arm_guarded(
        self,
    ) -> crate::dag::DagArm<In, Option<Out>, ViewGuardedNode<PrevChain, InnerSteps, V>> {
        crate::dag::DagArm {
            chain: ViewGuardedNode {
                prev: self.prev_chain,
                inner: self.inner,
                _marker: PhantomData,
            },
            _marker: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{PipelineBuilder, Res, ResMut, Resource, WorldBuilder};

    // -- Domain types --

    struct AuditLog(Vec<String>);
    impl Resource for AuditLog {}

    struct RiskLimits {
        max_qty: u64,
    }
    impl Resource for RiskLimits {}

    // Borrowed view — the whole point
    struct OrderView<'a> {
        symbol: &'a str,
        qty: u64,
    }

    struct NewOrderCommand {
        source: String,
        symbol: String,
        qty: u64,
        #[allow(dead_code)]
        price: f64,
    }

    struct AmendOrderCommand {
        #[allow(dead_code)]
        order_id: u64,
        symbol: String,
        qty: u64,
        #[allow(dead_code)]
        price: f64,
    }

    // -- View marker + impls (zero-cost borrows) --

    struct AsOrderView;

    // SAFETY: ViewType<'a> and StaticViewType are the same struct with different
    // lifetime parameters; layout is identical. `view` borrows correctly from source.
    unsafe impl View<NewOrderCommand> for AsOrderView {
        type ViewType<'a> = OrderView<'a>;
        type StaticViewType = OrderView<'static>;
        fn view(source: &NewOrderCommand) -> OrderView<'_> {
            OrderView {
                symbol: &source.symbol,
                qty: source.qty,
            }
        }
    }

    // SAFETY: as above; same struct, different source type.
    unsafe impl View<AmendOrderCommand> for AsOrderView {
        type ViewType<'a> = OrderView<'a>;
        type StaticViewType = OrderView<'static>;
        fn view(source: &AmendOrderCommand) -> OrderView<'_> {
            OrderView {
                symbol: &source.symbol,
                qty: source.qty,
            }
        }
    }

    // -- Reusable steps (Params first, &View last) --

    fn log_order(mut log: ResMut<AuditLog>, v: &OrderView) {
        log.0.push(format!("{} qty={}", v.symbol, v.qty));
    }

    fn check_risk(limits: Res<RiskLimits>, v: &OrderView) -> bool {
        v.qty <= limits.max_qty
    }

    // -- Tests --

    #[test]
    fn tap_observes_view() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view()
            .then(|_cmd: NewOrderCommand| {}, reg);

        p.run(
            &mut world,
            NewOrderCommand {
                source: "test".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["BTC qty=50"]);
    }

    #[test]
    fn guard_rejects() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        wb.register(RiskLimits { max_qty: 100 });
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .guard(check_risk, reg)
            .end_view_guarded();

        let result = p.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );
        assert!(result.is_some());

        let result = p.run(
            &mut world,
            NewOrderCommand {
                source: "b".into(),
                symbol: "ETH".into(),
                qty: 200,
                price: 3000.0,
            },
        );
        assert!(result.is_none());

        // Tap is before guard, so both events are logged.
        // Steps after a rejecting guard short-circuit.
        assert_eq!(world.resource::<AuditLog>().0.len(), 2);
    }

    #[test]
    fn event_passes_through_unchanged() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn sink(mut out: ResMut<AuditLog>, cmd: NewOrderCommand) {
            out.0
                .push(format!("sink: {} from {}", cmd.symbol, cmd.source));
        }

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view()
            .then(sink, reg);

        p.run(
            &mut world,
            NewOrderCommand {
                source: "ops".into(),
                symbol: "SOL".into(),
                qty: 10,
                price: 150.0,
            },
        );

        let log = &world.resource::<AuditLog>().0;
        assert_eq!(log[0], "SOL qty=10");
        assert_eq!(log[1], "sink: SOL from ops");
    }

    #[test]
    fn reusable_across_event_types() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        let mut p_new = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view()
            .then(|_: NewOrderCommand| {}, reg);

        let mut p_amend = PipelineBuilder::<AmendOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg) // SAME function
            .end_view()
            .then(|_: AmendOrderCommand| {}, reg);

        p_new.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );
        p_amend.run(
            &mut world,
            AmendOrderCommand {
                order_id: 123,
                symbol: "ETH".into(),
                qty: 25,
                price: 3000.0,
            },
        );

        let log = &world.resource::<AuditLog>().0;
        assert_eq!(log[0], "BTC qty=50");
        assert_eq!(log[1], "ETH qty=25");
    }

    #[test]
    fn multiple_taps_in_scope() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_symbol(mut log: ResMut<AuditLog>, v: &OrderView) {
            log.0.push(format!("symbol: {}", v.symbol));
        }
        fn log_qty(mut log: ResMut<AuditLog>, v: &OrderView) {
            log.0.push(format!("qty: {}", v.qty));
        }

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_symbol, reg)
            .tap(log_qty, reg)
            .end_view()
            .then(|_: NewOrderCommand| {}, reg);

        p.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );

        let log = &world.resource::<AuditLog>().0;
        assert_eq!(log[0], "symbol: BTC");
        assert_eq!(log[1], "qty: 50");
    }

    #[test]
    fn sequential_views() {
        struct SymbolView<'a> {
            symbol: &'a str,
        }
        struct QtyView {
            qty: u64,
        }

        struct AsSymbolView;
        // SAFETY: ViewType<'a> and StaticViewType are the same struct with different
        // lifetime parameters; layout is identical. `view` borrows correctly from source.
        unsafe impl View<NewOrderCommand> for AsSymbolView {
            type ViewType<'a> = SymbolView<'a>;
            type StaticViewType = SymbolView<'static>;
            fn view(source: &NewOrderCommand) -> SymbolView<'_> {
                SymbolView {
                    symbol: &source.symbol,
                }
            }
        }

        struct AsQtyView;
        // SAFETY: ViewType<'a> and StaticViewType are the same struct; QtyView is
        // Copy with no lifetime, so the layout-identity requirement is trivially met.
        unsafe impl View<NewOrderCommand> for AsQtyView {
            type ViewType<'a> = QtyView;
            type StaticViewType = QtyView;
            fn view(source: &NewOrderCommand) -> QtyView {
                QtyView { qty: source.qty }
            }
        }

        fn log_sym(mut log: ResMut<AuditLog>, v: &SymbolView) {
            log.0.push(format!("sym: {}", v.symbol));
        }
        fn log_qty_view(mut log: ResMut<AuditLog>, v: &QtyView) {
            log.0.push(format!("qty: {}", v.qty));
        }

        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsSymbolView>()
            .tap(log_sym, reg)
            .end_view()
            .view::<AsQtyView>()
            .tap(log_qty_view, reg)
            .end_view()
            .then(|_: NewOrderCommand| {}, reg);

        p.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );

        let log = &world.resource::<AuditLog>().0;
        assert_eq!(log[0], "sym: BTC");
        assert_eq!(log[1], "qty: 50");
    }

    // -- DAG tests --

    #[test]
    fn dag_view_tap() {
        use crate::{DagBuilder, Handler};

        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        let dag = DagBuilder::<NewOrderCommand>::new()
            .root(|cmd: NewOrderCommand| cmd, reg)
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view_dag()
            .then(|_cmd: &NewOrderCommand| {}, reg);

        let mut handler = dag.build();
        handler.run(
            &mut world,
            NewOrderCommand {
                source: "test".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["BTC qty=50"]);
    }

    #[test]
    fn dag_view_guard() {
        use crate::{DagBuilder, Handler};

        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        wb.register(RiskLimits { max_qty: 100 });
        let mut world = wb.build();
        let reg = world.registry();

        fn sink(mut log: ResMut<AuditLog>, val: &Option<NewOrderCommand>) {
            if val.is_some() {
                log.0.push("accepted".into());
            } else {
                log.0.push("rejected".into());
            }
        }

        let dag = DagBuilder::<NewOrderCommand>::new()
            .root(|cmd: NewOrderCommand| cmd, reg)
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .guard(check_risk, reg)
            .end_view_dag_guarded()
            .then(sink, reg);

        let mut handler = dag.build();
        handler.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );
        handler.run(
            &mut world,
            NewOrderCommand {
                source: "b".into(),
                symbol: "ETH".into(),
                qty: 200,
                price: 3000.0,
            },
        );

        let log = &world.resource::<AuditLog>().0;
        assert_eq!(log[0], "BTC qty=50");
        assert_eq!(log[1], "accepted");
        assert_eq!(log[2], "ETH qty=200");
        assert_eq!(log[3], "rejected");
    }

    #[test]
    fn inspect_no_params() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        // inspect takes no Params — just &View
        fn just_print(v: &OrderView) {
            assert!(!v.symbol.is_empty());
        }

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .inspect(just_print, reg)
            .tap(log_order, reg)
            .end_view()
            .then(|_: NewOrderCommand| {}, reg);

        p.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["BTC qty=50"]);
    }

    #[test]
    fn filter_rejects() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        wb.register(RiskLimits { max_qty: 100 });
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .filter(check_risk, reg)
            .end_view_guarded();

        let result = p.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );
        assert!(result.is_some());

        let result = p.run(
            &mut world,
            NewOrderCommand {
                source: "b".into(),
                symbol: "ETH".into(),
                qty: 200,
                price: 3000.0,
            },
        );
        assert!(result.is_none());
    }

    #[test]
    fn guard_short_circuits_subsequent_tap() {
        // guard BEFORE tap — if guard rejects, tap should NOT fire
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        wb.register(RiskLimits { max_qty: 100 });
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .guard(check_risk, reg) // guard FIRST
            .tap(log_order, reg) // tap AFTER — should NOT fire on rejection
            .end_view_guarded();

        // Accepted: guard passes, tap fires
        let result = p.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );
        assert!(result.is_some());
        assert_eq!(world.resource::<AuditLog>().0.len(), 1);

        // Rejected: guard fails, tap does NOT fire (short-circuit)
        let result = p.run(
            &mut world,
            NewOrderCommand {
                source: "b".into(),
                symbol: "ETH".into(),
                qty: 200,
                price: 3000.0,
            },
        );
        assert!(result.is_none());
        assert_eq!(world.resource::<AuditLog>().0.len(), 1); // still 1, not 2
    }

    // -- Multi-field view tests -----------------------------------------------

    struct FullOrderView<'a> {
        source: &'a str,
        symbol: &'a str,
        qty: u64,
        price: f64,
    }

    struct AsFullOrderView;
    // SAFETY: ViewType<'a> and StaticViewType are the same struct with different
    // lifetime parameters; layout is identical. `view` borrows correctly from source.
    unsafe impl View<NewOrderCommand> for AsFullOrderView {
        type ViewType<'a> = FullOrderView<'a>;
        type StaticViewType = FullOrderView<'static>;
        fn view(source: &NewOrderCommand) -> FullOrderView<'_> {
            FullOrderView {
                source: &source.source,
                symbol: &source.symbol,
                qty: source.qty,
                price: source.price,
            }
        }
    }

    #[test]
    fn view_with_multiple_borrowed_fields() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_full(mut log: ResMut<AuditLog>, v: &FullOrderView) {
            log.0.push(format!(
                "{} {} qty={} px={}",
                v.source, v.symbol, v.qty, v.price
            ));
        }

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsFullOrderView>()
            .tap(log_full, reg)
            .end_view()
            .then(|_: NewOrderCommand| {}, reg);

        p.run(
            &mut world,
            NewOrderCommand {
                source: "desk-a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );

        assert_eq!(
            world.resource::<AuditLog>().0,
            vec!["desk-a BTC qty=50 px=42000"]
        );
    }

    // -- Non-Copy type tests --------------------------------------------------

    struct Payload {
        data: Vec<u8>,
        tag: String,
    }

    struct PayloadView<'a> {
        data: &'a [u8],
        tag: &'a str,
    }

    struct AsPayloadView;
    // SAFETY: ViewType<'a> and StaticViewType are the same struct with different
    // lifetime parameters; layout is identical. `view` borrows correctly from source.
    unsafe impl View<Payload> for AsPayloadView {
        type ViewType<'a> = PayloadView<'a>;
        type StaticViewType = PayloadView<'static>;
        fn view(source: &Payload) -> PayloadView<'_> {
            PayloadView {
                data: &source.data,
                tag: &source.tag,
            }
        }
    }

    #[test]
    fn view_of_non_copy_types() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_payload(mut log: ResMut<AuditLog>, v: &PayloadView) {
            log.0.push(format!("tag={} len={}", v.tag, v.data.len()));
        }

        let mut p = PipelineBuilder::<Payload>::new()
            .view::<AsPayloadView>()
            .tap(log_payload, reg)
            .end_view()
            .then(|_: Payload| {}, reg);

        p.run(
            &mut world,
            Payload {
                data: vec![1, 2, 3],
                tag: "test".into(),
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["tag=test len=3"]);
    }

    #[test]
    fn view_guard_preserves_non_copy_event() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn check_tag(v: &PayloadView) -> bool {
            v.tag == "accept"
        }

        let mut p = PipelineBuilder::<Payload>::new()
            .view::<AsPayloadView>()
            .guard(check_tag, reg)
            .end_view_guarded();

        let accepted = p.run(
            &mut world,
            Payload {
                data: vec![1],
                tag: "accept".into(),
            },
        );
        assert!(accepted.is_some());
        assert_eq!(accepted.unwrap().data, vec![1]);

        let rejected = p.run(
            &mut world,
            Payload {
                data: vec![2],
                tag: "reject".into(),
            },
        );
        assert!(rejected.is_none());
    }

    #[test]
    fn view_guard_inside_view() {
        // Guard inside view scope — tests guarded view with accept/reject
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn accept_tag(v: &PayloadView) -> bool {
            v.tag == "accept"
        }

        let mut p = PipelineBuilder::<Payload>::new()
            .view::<AsPayloadView>()
            .guard(accept_tag, reg)
            .end_view_guarded();

        // Wrong tag — guarded out
        let result = p.run(
            &mut world,
            Payload {
                data: vec![1],
                tag: "reject".into(),
            },
        );
        assert!(result.is_none());

        // Right tag — passes through
        let result = p.run(
            &mut world,
            Payload {
                data: vec![1, 2, 3],
                tag: "accept".into(),
            },
        );
        assert!(result.is_some());
        assert_eq!(result.unwrap().data, vec![1, 2, 3]);
    }

    #[test]
    fn view_tap_with_world_resources() {
        // View tap step reads a World resource
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_order(mut log: ResMut<AuditLog>, v: &OrderView) {
            log.0.push(format!("{}:{}", v.symbol, v.qty));
        }

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view();

        p.run(
            &mut world,
            NewOrderCommand {
                source: "test".into(),
                symbol: "BTC".into(),
                qty: 100,
                price: 50000.0,
            },
        );
        p.run(
            &mut world,
            NewOrderCommand {
                source: "test".into(),
                symbol: "ETH".into(),
                qty: 50,
                price: 3000.0,
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["BTC:100", "ETH:50"]);
    }

    #[test]
    fn view_repeated_dispatch() {
        // Stress: same pipeline dispatched many times — no leaks, no drift
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn count(mut log: ResMut<AuditLog>, _v: &OrderView) {
            log.0.push("hit".into());
        }

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(count, reg)
            .end_view();

        for _ in 0..100 {
            p.run(
                &mut world,
                NewOrderCommand {
                    source: "stress".into(),
                    symbol: "X".into(),
                    qty: 1,
                    price: 1.0,
                },
            );
        }

        assert_eq!(world.resource::<AuditLog>().0.len(), 100);
    }
}
