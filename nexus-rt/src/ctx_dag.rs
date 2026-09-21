// Builder return types are necessarily complex — each combinator returns
// CtxDagChain<C, In, Out, NodeType<Chain, ...>>. Same pattern as iterator adapters.
#![allow(clippy::type_complexity)]
// Handler arity is architecturally required by the Param trait — handlers
// take N typed parameters and the macro-generated dispatch impls expand
// per-arity into call_inner functions with N + Input arguments. Module-level
// allow rather than one inline attribute per arity expansion.
#![allow(clippy::too_many_arguments)]

//! Context-aware DAG dispatch.
//!
//! Mirrors the [`dag`](crate::dag) module but threads `&mut C`
//! (per-instance context) through every step. Designed for use inside
//! [`Callback`](crate::Callback) where each handler instance owns private
//! state that pipeline steps need to read or mutate.
//!
//! # Step function convention
//!
//! Context first, then Params, then step input last:
//!
//! ```ignore
//! fn update_book(ctx: &mut TradingCtx, book: ResMut<OrderBook>, msg: &Decoded) -> BookResult { .. }
//! fn update_risk(ctx: &mut TradingCtx, risk: ResMut<RiskState>, msg: &Decoded) -> RiskResult { .. }
//! fn check_and_submit(ctx: &mut TradingCtx, a: &BookResult, b: &RiskResult) { .. }
//! ```
//!
//! # Integration with Callback
//!
//! The built [`CtxDag`] implements [`CtxStepCall`] — it takes
//! `&mut C`, `&mut World`, and `In`, returning `Out`.
//!
//! To use a DAG from a [`Handler`](crate::Handler), create a normal
//! [`Callback`](crate::Callback) whose handler function owns or accesses
//! the context `C` and calls the DAG via its `run` method, passing
//! `&mut C`, `&mut World`, and the handler input.
//!
//! # Three-tier step resolution
//!
//! Each combinator accepts functions via three tiers, matching the
//! [`dag`](crate::dag) module:
//!
//! 1. **Named function with Params** — `fn(&mut C, Res<T>, &In) -> Out`
//! 2. **Arity-0 closure** — `FnMut(&mut C, &In) -> Out`
//! 3. **[`Opaque`](crate::Opaque) closure** — `FnMut(&mut C, &mut World, &In) -> Out`
//!    (raw World access, no Param resolution)
//!
//! # Deferred combinators
//!
//! The following combinators from [`dag`](crate::dag) are not yet implemented:
//! `scan`, `dedup`, `dispatch`, `route`, `tee`, `splat`, `cloned`,
//! `not`/`and`/`or`/`xor` (bool), `ok_or_else`, `or_else`,
//! `Result::unwrap_or_else`, `view`, and `BatchDag`. These can be added
//! when a concrete use case requires them.
//!
//! # Examples
//!
//! ```ignore
//! let dag = CtxDagBuilder::<MyCtx, WireMsg>::new()
//!     .root(decode, &reg)
//!     .fork()
//!     .arm(|a| a.then(update_book, &reg))
//!     .arm(|b| b.then(update_risk, &reg))
//!     .merge(check_and_submit, &reg)
//!     .build();
//!
//! dag.call(&mut ctx, &mut world, wire_msg);
//! ```

use std::marker::PhantomData;

use crate::ctx_pipeline::{
    CtxChainCall, CtxDiscardOptionNode, CtxFilterNode, CtxGuardNode, CtxIdentityNode,
    CtxInspectErrNode, CtxInspectOptionNode, CtxInspectResultNode, CtxMapErrNode, CtxOkNode,
    CtxOkOrNode, CtxOnNoneNode, CtxStepCall, CtxTapNode, CtxThenNode, CtxUnwrapOrElseOptionNode,
    CtxUnwrapOrOptionNode, CtxUnwrapOrResultNode, IntoCtxProducer, IntoCtxRefStep, IntoCtxStep,
};
use crate::dispatch::{Dispatchable, NoopArm, PanicArm, assert_first_arm, finalize_ordinal_table};
use crate::handler::Param;
use crate::world::{Registry, World};

// =============================================================================
// CtxDagThenNode — DAG ref step (takes &Out, produces NewOut)
// =============================================================================

/// Chain node for DAG `.then()` — takes input by reference.
#[doc(hidden)]
pub struct CtxDagThenNode<Prev, S, NewOut> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> NewOut>,
}

impl<C, In, Prev, S, NewOut: 'static> CtxChainCall<C, In> for CtxDagThenNode<Prev, S, NewOut>
where
    Prev: CtxChainCall<C, In>,
    Prev::Out: 'static,
    S: for<'a> CtxStepCall<C, &'a Prev::Out, Out = NewOut>,
{
    type Out = NewOut;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> NewOut {
        let mid = self.prev.call(ctx, world, input);
        self.step.call(ctx, world, &mid)
    }
}

// =============================================================================
// DAG Option/Result nodes that take inner by ref (matching dag.rs pattern)
// =============================================================================

/// Chain node for DAG `.map()` on `Option<T>` — takes `&T`.
#[doc(hidden)]
pub struct CtxDagMapOptionNode<Prev, S, U> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> U>,
}

impl<C, In, T: 'static, Prev, S, U> CtxChainCall<C, In> for CtxDagMapOptionNode<Prev, S, U>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
    S: for<'a> CtxStepCall<C, &'a T, Out = U>,
{
    type Out = Option<U>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<U> {
        match self.prev.call(ctx, world, input) {
            Some(val) => Some(self.step.call(ctx, world, &val)),
            None => None,
        }
    }
}

/// Chain node for DAG `.and_then()` on `Option<T>` — takes `&T`.
#[doc(hidden)]
pub struct CtxDagAndThenOptionNode<Prev, S, U> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> U>,
}

impl<C, In, T: 'static, Prev, S, U> CtxChainCall<C, In> for CtxDagAndThenOptionNode<Prev, S, U>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
    S: for<'a> CtxStepCall<C, &'a T, Out = Option<U>>,
{
    type Out = Option<U>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<U> {
        match self.prev.call(ctx, world, input) {
            Some(val) => self.step.call(ctx, world, &val),
            None => None,
        }
    }
}

/// Chain node for DAG `.map()` on `Result<T, E>` — takes `&T`.
#[doc(hidden)]
pub struct CtxDagMapResultNode<Prev, S, U> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> U>,
}

impl<C, In, T: 'static, E, Prev, S, U> CtxChainCall<C, In> for CtxDagMapResultNode<Prev, S, U>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
    S: for<'a> CtxStepCall<C, &'a T, Out = U>,
{
    type Out = Result<U, E>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Result<U, E> {
        match self.prev.call(ctx, world, input) {
            Ok(val) => Ok(self.step.call(ctx, world, &val)),
            Err(e) => Err(e),
        }
    }
}

/// Chain node for DAG `.and_then()` on `Result<T, E>` — takes `&T`.
#[doc(hidden)]
pub struct CtxDagAndThenResultNode<Prev, S, U> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> U>,
}

impl<C, In, T: 'static, U, E, Prev, S> CtxChainCall<C, In> for CtxDagAndThenResultNode<Prev, S, U>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
    S: for<'a> CtxStepCall<C, &'a T, Out = Result<U, E>>,
{
    type Out = Result<U, E>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Result<U, E> {
        match self.prev.call(ctx, world, input) {
            Ok(val) => self.step.call(ctx, world, &val),
            Err(e) => Err(e),
        }
    }
}

/// Chain node for DAG `.catch()` on `Result<T, E>` — takes `&E`.
#[doc(hidden)]
pub struct CtxDagCatchNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, E: 'static, Prev, S> CtxChainCall<C, In> for CtxDagCatchNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
    S: for<'a> CtxStepCall<C, &'a E, Out = ()>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<T> {
        match self.prev.call(ctx, world, input) {
            Ok(val) => Some(val),
            Err(e) => {
                self.step.call(ctx, world, &e);
                None
            }
        }
    }
}

// =============================================================================
// CtxMergeStepCall / IntoCtxMergeStep — context-aware merge step dispatch
// =============================================================================

/// Callable trait for resolved context-aware merge steps.
///
/// Like [`MergeStepCall`](crate::dag::MergeStepCall) but with `&mut C` context.
#[doc(hidden)]
pub trait CtxMergeStepCall<C, Inputs> {
    /// The output type of this merge step.
    type Out;
    /// Call this merge step with context, world, and input references.
    fn call(&mut self, ctx: &mut C, world: &mut World, inputs: Inputs) -> Self::Out;
}

/// Converts a named function into a resolved context-aware merge step.
///
/// Context first, then Params, then N reference inputs:
///
/// ```ignore
/// fn check(ctx: &mut Ctx, config: Res<Config>, ob: &ObResult, risk: &RiskResult) -> Decision { .. }
/// ```
#[doc(hidden)]
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a context-aware merge step",
    note = "ctx merge steps: `fn(&mut C, Params..., &A, &B, ...) -> Out`",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoCtxMergeStep<C, Inputs, Out, Params> {
    /// The concrete resolved merge step type.
    type Step: CtxMergeStepCall<C, Inputs, Out = Out>;

    /// Resolve Param state from the registry and produce a merge step.
    fn into_ctx_merge_step(self, registry: &Registry) -> Self::Step;
}

/// Internal: pre-resolved context-aware merge step with cached Param state.
#[doc(hidden)]
pub struct CtxMergeStep<F, Params: Param> {
    f: F,
    state: Params::State,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

// -- Merge arity 2, Param arity 0 (closures work) ---------------------------

impl<C, A, B, Out, F> CtxMergeStepCall<C, (&A, &B)> for CtxMergeStep<F, ()>
where
    F: FnMut(&mut C, &A, &B) -> Out + 'static,
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, _world: &mut World, inputs: (&A, &B)) -> Out {
        (self.f)(ctx, inputs.0, inputs.1)
    }
}

impl<C, A, B, Out, F> IntoCtxMergeStep<C, (&A, &B), Out, ()> for F
where
    F: FnMut(&mut C, &A, &B) -> Out + 'static,
{
    type Step = CtxMergeStep<F, ()>;

    fn into_ctx_merge_step(self, registry: &Registry) -> Self::Step {
        CtxMergeStep {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// -- Merge arity 2, Param arities 1-8 ---------------------------------------

macro_rules! impl_ctx_merge2_step {
    ($($P:ident),+) => {
        impl<C, A, B, Out, F: 'static, $($P: Param + 'static),+>
            CtxMergeStepCall<C, (&A, &B)> for CtxMergeStep<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+ &A, &B) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+ &A, &B) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, ctx: &mut C, world: &mut World, inputs: (&A, &B)) -> Out {
                fn call_inner<Ctx, $($P,)+ IA, IB, Output>(
                    mut f: impl FnMut(&mut Ctx, $($P,)+ &IA, &IB) -> Output,
                    ctx: &mut Ctx,
                    $($P: $P,)+
                    a: &IA, b: &IB,
                ) -> Output {
                    f(ctx, $($P,)+ a, b)
                }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: Resource IDs in self.state were obtained from the same
                // Registry that built this World. Borrows are disjoint — enforced
                // by conflict detection at build time (check_access).
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, ctx, $($P,)+ inputs.0, inputs.1)
            }
        }

        impl<C, A, B, Out, F: 'static, $($P: Param + 'static),+>
            IntoCtxMergeStep<C, (&A, &B), Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+ &A, &B) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+ &A, &B) -> Out,
        {
            type Step = CtxMergeStep<F, ($($P,)+)>;

            fn into_ctx_merge_step(self, registry: &Registry) -> Self::Step {
                let state = <($($P,)+) as Param>::init(registry);
                {
                    #[allow(non_snake_case)]
                    let ($($P,)+) = &state;
                    let mut accesses = Vec::new();
                    $(
                        <$P as Param>::collect_access($P, &mut accesses);
                    )+
                    registry.check_access(&accesses);
                }
                CtxMergeStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

// -- Merge arity 3, Param arity 0 -------------------------------------------

impl<Ctx, IA, IB, IC, Out, F> CtxMergeStepCall<Ctx, (&IA, &IB, &IC)> for CtxMergeStep<F, ()>
where
    F: FnMut(&mut Ctx, &IA, &IB, &IC) -> Out + 'static,
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut Ctx, _world: &mut World, inputs: (&IA, &IB, &IC)) -> Out {
        (self.f)(ctx, inputs.0, inputs.1, inputs.2)
    }
}

impl<Ctx, IA, IB, IC, Out, F> IntoCtxMergeStep<Ctx, (&IA, &IB, &IC), Out, ()> for F
where
    F: FnMut(&mut Ctx, &IA, &IB, &IC) -> Out + 'static,
{
    type Step = CtxMergeStep<F, ()>;

    fn into_ctx_merge_step(self, registry: &Registry) -> Self::Step {
        CtxMergeStep {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// -- Merge arity 3, Param arities 1-8 ---------------------------------------

macro_rules! impl_ctx_merge3_step {
    ($($P:ident),+) => {
        impl<Ctx, A, B, C, Out, F: 'static, $($P: Param + 'static),+>
            CtxMergeStepCall<Ctx, (&A, &B, &C)> for CtxMergeStep<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut Ctx, $($P,)+ &A, &B, &C) -> Out +
                FnMut(&mut Ctx, $($P::Item<'a>,)+ &A, &B, &C) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, ctx: &mut Ctx, world: &mut World, inputs: (&A, &B, &C)) -> Out {
                fn call_inner<Cx, $($P,)+ IA, IB, IC, Output>(
                    mut f: impl FnMut(&mut Cx, $($P,)+ &IA, &IB, &IC) -> Output,
                    ctx: &mut Cx,
                    $($P: $P,)+
                    a: &IA, b: &IB, c: &IC,
                ) -> Output {
                    f(ctx, $($P,)+ a, b, c)
                }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: Resource IDs in self.state were obtained from the same
                // Registry that built this World. Borrows are disjoint — enforced
                // by conflict detection at build time (check_access).
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, ctx, $($P,)+ inputs.0, inputs.1, inputs.2)
            }
        }

        impl<Ctx, A, B, C, Out, F: 'static, $($P: Param + 'static),+>
            IntoCtxMergeStep<Ctx, (&A, &B, &C), Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut(&mut Ctx, $($P,)+ &A, &B, &C) -> Out +
                FnMut(&mut Ctx, $($P::Item<'a>,)+ &A, &B, &C) -> Out,
        {
            type Step = CtxMergeStep<F, ($($P,)+)>;

            fn into_ctx_merge_step(self, registry: &Registry) -> Self::Step {
                let state = <($($P,)+) as Param>::init(registry);
                {
                    #[allow(non_snake_case)]
                    let ($($P,)+) = &state;
                    let mut accesses = Vec::new();
                    $(
                        <$P as Param>::collect_access($P, &mut accesses);
                    )+
                    registry.check_access(&accesses);
                }
                CtxMergeStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

// -- Merge arity 4, Param arity 0 -------------------------------------------

impl<Ctx, IA, IB, IC, ID, Out, F> CtxMergeStepCall<Ctx, (&IA, &IB, &IC, &ID)>
    for CtxMergeStep<F, ()>
where
    F: FnMut(&mut Ctx, &IA, &IB, &IC, &ID) -> Out + 'static,
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut Ctx, _world: &mut World, inputs: (&IA, &IB, &IC, &ID)) -> Out {
        (self.f)(ctx, inputs.0, inputs.1, inputs.2, inputs.3)
    }
}

impl<Ctx, IA, IB, IC, ID, Out, F> IntoCtxMergeStep<Ctx, (&IA, &IB, &IC, &ID), Out, ()> for F
where
    F: FnMut(&mut Ctx, &IA, &IB, &IC, &ID) -> Out + 'static,
{
    type Step = CtxMergeStep<F, ()>;

    fn into_ctx_merge_step(self, registry: &Registry) -> Self::Step {
        CtxMergeStep {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// -- Merge arity 4, Param arities 1-8 ---------------------------------------

macro_rules! impl_ctx_merge4_step {
    ($($P:ident),+) => {
        #[allow(clippy::many_single_char_names)]
        impl<Ctx, A, B, C, D, Out, F: 'static, $($P: Param + 'static),+>
            CtxMergeStepCall<Ctx, (&A, &B, &C, &D)> for CtxMergeStep<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut Ctx, $($P,)+ &A, &B, &C, &D) -> Out +
                FnMut(&mut Ctx, $($P::Item<'a>,)+ &A, &B, &C, &D) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, ctx: &mut Ctx, world: &mut World, inputs: (&A, &B, &C, &D)) -> Out {
                fn call_inner<Cx, $($P,)+ IA, IB, IC, ID, Output>(
                    mut f: impl FnMut(&mut Cx, $($P,)+ &IA, &IB, &IC, &ID) -> Output,
                    ctx: &mut Cx,
                    $($P: $P,)+ a: &IA, b: &IB, c: &IC, d: &ID,
                ) -> Output { f(ctx, $($P,)+ a, b, c, d) }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: Resource IDs in self.state were obtained from the same
                // Registry that built this World. Borrows are disjoint — enforced
                // by conflict detection at build time (check_access).
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, ctx, $($P,)+ inputs.0, inputs.1, inputs.2, inputs.3)
            }
        }

        #[allow(clippy::many_single_char_names)]
        impl<Ctx, A, B, C, D, Out, F: 'static, $($P: Param + 'static),+>
            IntoCtxMergeStep<Ctx, (&A, &B, &C, &D), Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut(&mut Ctx, $($P,)+ &A, &B, &C, &D) -> Out +
                FnMut(&mut Ctx, $($P::Item<'a>,)+ &A, &B, &C, &D) -> Out,
        {
            type Step = CtxMergeStep<F, ($($P,)+)>;

            fn into_ctx_merge_step(self, registry: &Registry) -> Self::Step {
                let state = <($($P,)+) as Param>::init(registry);
                {
                    #[allow(non_snake_case)]
                    let ($($P,)+) = &state;
                    let mut accesses = Vec::new();
                    $(
                        <$P as Param>::collect_access($P, &mut accesses);
                    )+
                    registry.check_access(&accesses);
                }
                CtxMergeStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_ctx_merge2_step);
all_tuples!(impl_ctx_merge3_step);
all_tuples!(impl_ctx_merge4_step);

// =============================================================================
// CtxDagBuilder — entry point
// =============================================================================

/// Entry point for building a context-aware DAG pipeline.
///
/// Like [`DagBuilder`](crate::DagBuilder) but every step receives `&mut C`
/// as the first argument.
///
/// # Examples
///
/// ```ignore
/// let dag = CtxDagBuilder::<MyCtx, WireMsg>::new()
///     .root(decode, &reg)
///     .fork()
///     .arm(|a| a.then(update_book, &reg))
///     .arm(|b| b.then(update_risk, &reg))
///     .merge(check_and_submit, &reg)
///     .build();
/// ```
#[must_use = "a DAG builder does nothing unless you chain steps and call .build()"]
pub struct CtxDagBuilder<C, E>(PhantomData<fn(&mut C, E)>);

impl<C, E> CtxDagBuilder<C, E> {
    /// Create a new typed context-aware DAG entry point.
    pub fn new() -> Self {
        Self(PhantomData)
    }

    /// Set the root step. Takes the event `E` by value, produces `Out`.
    pub fn root<Out, Params, S>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxDagChain<C, E, Out, CtxThenNode<CtxIdentityNode, S::Step>>
    where
        Out: 'static,
        S: IntoCtxStep<C, E, Out, Params>,
    {
        CtxDagChain {
            chain: CtxThenNode {
                prev: CtxIdentityNode,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }
}

impl<C, E> Default for CtxDagBuilder<C, E> {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// CtxDagChain — main chain builder
// =============================================================================

/// Main chain builder for a context-aware DAG.
///
/// `Chain` implements [`CtxChainCall<C, E, Out = Out>`].
#[must_use = "DAG chain does nothing until .build() is called"]
pub struct CtxDagChain<C, In, Out, Chain> {
    chain: Chain,
    _marker: PhantomData<fn(&mut C, In) -> Out>,
}

impl<C, In, Out: 'static, Chain> CtxDagChain<C, In, Out, Chain> {
    /// Enter fork mode. Subsequent `.arm()` calls add parallel branches.
    pub fn fork(self) -> CtxDagChainFork<C, In, Out, Chain, ()> {
        CtxDagChainFork {
            chain: self.chain,
            arms: (),
            _marker: PhantomData,
        }
    }
}

impl<C, In, Chain: CtxChainCall<C, In, Out = ()>> CtxDagChain<C, In, (), Chain> {
    /// Finalize into a [`CtxDag`] that implements [`CtxStepCall`].
    #[must_use = "building a DAG without storing it does nothing"]
    pub fn build(self) -> CtxDag<C, In, Chain> {
        CtxDag {
            chain: self.chain,
            _marker: PhantomData,
        }
    }
}

impl<C, In, Chain: CtxChainCall<C, In, Out = Option<()>>> CtxDagChain<C, In, Option<()>, Chain> {
    /// Finalize into a [`CtxDag`], discarding the `Option<()>`.
    #[must_use = "building a DAG without storing it does nothing"]
    pub fn build(self) -> CtxDag<C, In, CtxDiscardOptionNode<Chain>> {
        CtxDag {
            chain: CtxDiscardOptionNode { prev: self.chain },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// CtxDagArmSeed — arm builder seed
// =============================================================================

/// Arm builder seed for context-aware DAG. Used in `.arm()` closures.
pub struct CtxDagArmSeed<C, In>(PhantomData<fn(&mut C, *const In)>);

impl<C, In> CtxDagArmSeed<C, In> {
    /// Create a new arm seed. Typically constructed internally by `.arm()`.
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<C, In> Default for CtxDagArmSeed<C, In> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C, In: 'static> CtxDagArmSeed<C, In> {
    /// Add the first step in this arm. Takes `&In` by reference.
    pub fn then<Out, Params, S>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxDagArm<C, In, Out, CtxThenNode<CtxIdentityNode, S::Step>>
    where
        Out: 'static,
        S: IntoCtxStep<C, &'static In, Out, Params>,
        S::Step: for<'a> CtxStepCall<C, &'a In, Out = Out>,
    {
        CtxDagArm {
            chain: CtxThenNode {
                prev: CtxIdentityNode,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// CtxDagArm — built arm in a DAG fork
// =============================================================================

/// Built arm in a context-aware DAG fork.
pub struct CtxDagArm<C, In, Out, Chain> {
    chain: Chain,
    _marker: PhantomData<fn(&mut C, *const In) -> Out>,
}

impl<C, In: 'static, Out: 'static, Chain> CtxDagArm<C, In, Out, Chain> {
    /// Enter fork mode within this arm.
    pub fn fork(self) -> CtxDagArmFork<C, In, Out, Chain, ()> {
        CtxDagArmFork {
            chain: self.chain,
            arms: (),
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// CtxDagChainFork / CtxDagArmFork — fork builders
// =============================================================================

/// Fork builder on the main chain. Accumulates arms as a tuple.
pub struct CtxDagChainFork<C, In, ForkOut, Chain, Arms> {
    chain: Chain,
    arms: Arms,
    _marker: PhantomData<fn(&mut C, In) -> ForkOut>,
}

/// Fork builder within an arm. Accumulates sub-arms as a tuple.
pub struct CtxDagArmFork<C, In, ForkOut, Chain, Arms> {
    chain: Chain,
    arms: Arms,
    _marker: PhantomData<fn(&mut C, *const In) -> ForkOut>,
}

// =============================================================================
// CtxDag — built context-aware DAG
// =============================================================================

/// Built context-aware DAG.
///
/// Created by [`CtxDagChain::build`]. Implements [`CtxStepCall`]
/// for use inside [`Callback`](crate::Callback) dispatch.
pub struct CtxDag<C, In, Chain> {
    chain: Chain,
    _marker: PhantomData<fn(&mut C, In)>,
}

impl<C, In, Chain: CtxChainCall<C, In, Out = ()>> CtxStepCall<C, In> for CtxDag<C, In, Chain> {
    type Out = ();
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) {
        self.chain.call(ctx, world, input);
    }
}

impl<C, In, Chain: CtxChainCall<C, In, Out = ()>> CtxDag<C, In, Chain> {
    /// Run the DAG with context, world, and input.
    pub fn run(&mut self, ctx: &mut C, world: &mut World, input: In) {
        self.chain.call(ctx, world, input);
    }
}

// =============================================================================
// Merge / Join named nodes — context-aware fork terminal nodes
// =============================================================================

/// Merge two context-aware fork arms into a single output.
#[doc(hidden)]
pub struct CtxMergeNode2<Chain, C0, C1, MS, ForkOut, A0, A1, MOut> {
    chain: Chain,
    arm0: C0,
    arm1: C1,
    merge: MS,
    _marker: PhantomData<fn(ForkOut) -> (A0, A1, MOut)>,
}

impl<Ctx, In, Chain, C0, C1, MS, ForkOut, A0, A1, MOut> CtxChainCall<Ctx, In>
    for CtxMergeNode2<Chain, C0, C1, MS, ForkOut, A0, A1, MOut>
where
    ForkOut: 'static,
    A0: 'static,
    A1: 'static,
    Chain: CtxChainCall<Ctx, In, Out = ForkOut>,
    C0: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = A0>,
    C1: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = A1>,
    MS: for<'x> CtxMergeStepCall<Ctx, (&'x A0, &'x A1), Out = MOut>,
{
    type Out = MOut;

    #[inline(always)]
    fn call(&mut self, ctx: &mut Ctx, world: &mut World, input: In) -> MOut {
        let fork_out = self.chain.call(ctx, world, input);
        let o0 = self.arm0.call(ctx, world, &fork_out);
        let o1 = self.arm1.call(ctx, world, &fork_out);
        self.merge.call(ctx, world, (&o0, &o1))
    }
}

/// Merge three context-aware fork arms into a single output.
#[doc(hidden)]
pub struct CtxMergeNode3<Chain, C0, C1, C2, MS, ForkOut, A0, A1, A2, MOut> {
    chain: Chain,
    arm0: C0,
    arm1: C1,
    arm2: C2,
    merge: MS,
    _marker: PhantomData<fn(ForkOut) -> (A0, A1, A2, MOut)>,
}

impl<Ctx, In, Chain, C0, C1, C2, MS, ForkOut, A0, A1, A2, MOut> CtxChainCall<Ctx, In>
    for CtxMergeNode3<Chain, C0, C1, C2, MS, ForkOut, A0, A1, A2, MOut>
where
    ForkOut: 'static,
    A0: 'static,
    A1: 'static,
    A2: 'static,
    Chain: CtxChainCall<Ctx, In, Out = ForkOut>,
    C0: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = A0>,
    C1: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = A1>,
    C2: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = A2>,
    MS: for<'x> CtxMergeStepCall<Ctx, (&'x A0, &'x A1, &'x A2), Out = MOut>,
{
    type Out = MOut;

    #[inline(always)]
    fn call(&mut self, ctx: &mut Ctx, world: &mut World, input: In) -> MOut {
        let fork_out = self.chain.call(ctx, world, input);
        let o0 = self.arm0.call(ctx, world, &fork_out);
        let o1 = self.arm1.call(ctx, world, &fork_out);
        let o2 = self.arm2.call(ctx, world, &fork_out);
        self.merge.call(ctx, world, (&o0, &o1, &o2))
    }
}

/// Merge four context-aware fork arms into a single output.
#[doc(hidden)]
pub struct CtxMergeNode4<Chain, C0, C1, C2, C3, MS, ForkOut, A0, A1, A2, A3, MOut> {
    chain: Chain,
    arm0: C0,
    arm1: C1,
    arm2: C2,
    arm3: C3,
    merge: MS,
    _marker: PhantomData<fn(ForkOut) -> (A0, A1, A2, A3, MOut)>,
}

#[allow(clippy::many_single_char_names)]
impl<Ctx, In, Chain, C0, C1, C2, C3, MS, ForkOut, A0, A1, A2, A3, MOut> CtxChainCall<Ctx, In>
    for CtxMergeNode4<Chain, C0, C1, C2, C3, MS, ForkOut, A0, A1, A2, A3, MOut>
where
    ForkOut: 'static,
    A0: 'static,
    A1: 'static,
    A2: 'static,
    A3: 'static,
    Chain: CtxChainCall<Ctx, In, Out = ForkOut>,
    C0: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = A0>,
    C1: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = A1>,
    C2: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = A2>,
    C3: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = A3>,
    MS: for<'x> CtxMergeStepCall<Ctx, (&'x A0, &'x A1, &'x A2, &'x A3), Out = MOut>,
{
    type Out = MOut;

    #[inline(always)]
    fn call(&mut self, ctx: &mut Ctx, world: &mut World, input: In) -> MOut {
        let fork_out = self.chain.call(ctx, world, input);
        let o0 = self.arm0.call(ctx, world, &fork_out);
        let o1 = self.arm1.call(ctx, world, &fork_out);
        let o2 = self.arm2.call(ctx, world, &fork_out);
        let o3 = self.arm3.call(ctx, world, &fork_out);
        self.merge.call(ctx, world, (&o0, &o1, &o2, &o3))
    }
}

/// Join two context-aware fork arms (all producing `()`).
#[doc(hidden)]
pub struct CtxJoinNode2<Chain, C0, C1, ForkOut> {
    chain: Chain,
    arm0: C0,
    arm1: C1,
    _marker: PhantomData<fn() -> ForkOut>,
}

impl<Ctx, In, Chain, C0, C1, ForkOut> CtxChainCall<Ctx, In> for CtxJoinNode2<Chain, C0, C1, ForkOut>
where
    ForkOut: 'static,
    Chain: CtxChainCall<Ctx, In, Out = ForkOut>,
    C0: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = ()>,
    C1: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = ()>,
{
    type Out = ();

    #[inline(always)]
    fn call(&mut self, ctx: &mut Ctx, world: &mut World, input: In) {
        let fork_out = self.chain.call(ctx, world, input);
        self.arm0.call(ctx, world, &fork_out);
        self.arm1.call(ctx, world, &fork_out);
    }
}

/// Join three context-aware fork arms (all producing `()`).
#[doc(hidden)]
pub struct CtxJoinNode3<Chain, C0, C1, C2, ForkOut> {
    chain: Chain,
    arm0: C0,
    arm1: C1,
    arm2: C2,
    _marker: PhantomData<fn() -> ForkOut>,
}

impl<Ctx, In, Chain, C0, C1, C2, ForkOut> CtxChainCall<Ctx, In>
    for CtxJoinNode3<Chain, C0, C1, C2, ForkOut>
where
    ForkOut: 'static,
    Chain: CtxChainCall<Ctx, In, Out = ForkOut>,
    C0: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = ()>,
    C1: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = ()>,
    C2: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = ()>,
{
    type Out = ();

    #[inline(always)]
    fn call(&mut self, ctx: &mut Ctx, world: &mut World, input: In) {
        let fork_out = self.chain.call(ctx, world, input);
        self.arm0.call(ctx, world, &fork_out);
        self.arm1.call(ctx, world, &fork_out);
        self.arm2.call(ctx, world, &fork_out);
    }
}

/// Join four context-aware fork arms (all producing `()`).
#[doc(hidden)]
pub struct CtxJoinNode4<Chain, C0, C1, C2, C3, ForkOut> {
    chain: Chain,
    arm0: C0,
    arm1: C1,
    arm2: C2,
    arm3: C3,
    _marker: PhantomData<fn() -> ForkOut>,
}

#[allow(clippy::many_single_char_names)]
impl<Ctx, In, Chain, C0, C1, C2, C3, ForkOut> CtxChainCall<Ctx, In>
    for CtxJoinNode4<Chain, C0, C1, C2, C3, ForkOut>
where
    ForkOut: 'static,
    Chain: CtxChainCall<Ctx, In, Out = ForkOut>,
    C0: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = ()>,
    C1: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = ()>,
    C2: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = ()>,
    C3: for<'a> CtxChainCall<Ctx, &'a ForkOut, Out = ()>,
{
    type Out = ();

    #[inline(always)]
    fn call(&mut self, ctx: &mut Ctx, world: &mut World, input: In) {
        let fork_out = self.chain.call(ctx, world, input);
        self.arm0.call(ctx, world, &fork_out);
        self.arm1.call(ctx, world, &fork_out);
        self.arm2.call(ctx, world, &fork_out);
        self.arm3.call(ctx, world, &fork_out);
    }
}

// =============================================================================
// Combinator macro — shared between CtxDagChain and CtxDagArm
// =============================================================================

/// Generates step combinators, Option/Result helpers for context-aware DAG.
macro_rules! impl_ctx_dag_combinators {
    (builder: $Builder:ident, upstream: $U:ident) => {
        // =============================================================
        // Core — any Out
        // =============================================================

        impl<Ctx, $U, Out: 'static, Chain> $Builder<Ctx, $U, Out, Chain> {
            /// Append a step. The step receives `&Out` by reference.
            pub fn then<NewOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, NewOut, CtxDagThenNode<Chain, S::Step, NewOut>>
            where
                NewOut: 'static,
                S: IntoCtxStep<Ctx, &'static Out, NewOut, Params>,
                S::Step: for<'a> CtxStepCall<Ctx, &'a Out, Out = NewOut> + 'static,
            {
                $Builder {
                    chain: CtxDagThenNode {
                        prev: self.chain,
                        step: f.into_ctx_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Conditionally wrap the output in `Option`.
            pub fn guard<Params, S: IntoCtxRefStep<Ctx, Out, bool, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Option<Out>, CtxGuardNode<Chain, S::Step>> {
                $Builder {
                    chain: CtxGuardNode {
                        prev: self.chain,
                        step: f.into_ctx_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Observe the current value without consuming or changing it.
            pub fn tap<Params, S: IntoCtxRefStep<Ctx, Out, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Out, CtxTapNode<Chain, S::Step>> {
                $Builder {
                    chain: CtxTapNode {
                        prev: self.chain,
                        step: f.into_ctx_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Option helpers
        // =============================================================

        impl<Ctx, $U, T: 'static, Chain> $Builder<Ctx, $U, Option<T>, Chain> {
            /// Transform the inner value. Step not called on None.
            pub fn map<U, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Option<U>, CtxDagMapOptionNode<Chain, S::Step, U>>
            where
                U: 'static,
                S: IntoCtxStep<Ctx, &'static T, U, Params>,
                S::Step: for<'x> CtxStepCall<Ctx, &'x T, Out = U>,
            {
                $Builder {
                    chain: CtxDagMapOptionNode {
                        prev: self.chain,
                        step: f.into_ctx_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Short-circuits on None. std: `Option::and_then`
            pub fn and_then<U, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Option<U>, CtxDagAndThenOptionNode<Chain, S::Step, U>>
            where
                U: 'static,
                S: IntoCtxStep<Ctx, &'static T, Option<U>, Params>,
                S::Step: for<'x> CtxStepCall<Ctx, &'x T, Out = Option<U>>,
            {
                $Builder {
                    chain: CtxDagAndThenOptionNode {
                        prev: self.chain,
                        step: f.into_ctx_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Side effect on None.
            pub fn on_none<Params, S: IntoCtxProducer<Ctx, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Option<T>, CtxOnNoneNode<Chain, S::Step>> {
                $Builder {
                    chain: CtxOnNoneNode {
                        prev: self.chain,
                        producer: f.into_ctx_producer(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Keep value if predicate holds. std: `Option::filter`
            pub fn filter<Params, S: IntoCtxRefStep<Ctx, T, bool, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Option<T>, CtxFilterNode<Chain, S::Step>> {
                $Builder {
                    chain: CtxFilterNode {
                        prev: self.chain,
                        step: f.into_ctx_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Side effect on Some value. std: `Option::inspect`
            pub fn inspect<Params, S: IntoCtxRefStep<Ctx, T, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Option<T>, CtxInspectOptionNode<Chain, S::Step>> {
                $Builder {
                    chain: CtxInspectOptionNode {
                        prev: self.chain,
                        step: f.into_ctx_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// None becomes Err(err). std: `Option::ok_or`
            pub fn ok_or<E: Clone>(
                self,
                err: E,
            ) -> $Builder<Ctx, $U, Result<T, E>, CtxOkOrNode<Chain, E>> {
                $Builder {
                    chain: CtxOkOrNode {
                        prev: self.chain,
                        err,
                    },
                    _marker: PhantomData,
                }
            }

            /// Exit Option — None becomes the default value.
            pub fn unwrap_or(
                self,
                default: T,
            ) -> $Builder<Ctx, $U, T, CtxUnwrapOrOptionNode<Chain, T>>
            where
                T: Clone,
            {
                $Builder {
                    chain: CtxUnwrapOrOptionNode {
                        prev: self.chain,
                        default,
                    },
                    _marker: PhantomData,
                }
            }

            /// Exit Option — None becomes `f()`.
            pub fn unwrap_or_else<Params, S: IntoCtxProducer<Ctx, T, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, T, CtxUnwrapOrElseOptionNode<Chain, S::Step>> {
                $Builder {
                    chain: CtxUnwrapOrElseOptionNode {
                        prev: self.chain,
                        producer: f.into_ctx_producer(registry),
                    },
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Result helpers
        // =============================================================

        impl<Ctx, $U, T: 'static, Err: 'static, Chain> $Builder<Ctx, $U, Result<T, Err>, Chain> {
            /// Transform the Ok value. Step not called on Err.
            pub fn map<U, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Result<U, Err>, CtxDagMapResultNode<Chain, S::Step, U>>
            where
                U: 'static,
                S: IntoCtxStep<Ctx, &'static T, U, Params>,
                S::Step: for<'x> CtxStepCall<Ctx, &'x T, Out = U>,
            {
                $Builder {
                    chain: CtxDagMapResultNode {
                        prev: self.chain,
                        step: f.into_ctx_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Short-circuits on Err. std: `Result::and_then`
            pub fn and_then<U, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Result<U, Err>, CtxDagAndThenResultNode<Chain, S::Step, U>>
            where
                U: 'static,
                S: IntoCtxStep<Ctx, &'static T, Result<U, Err>, Params>,
                S::Step: for<'x> CtxStepCall<Ctx, &'x T, Out = Result<U, Err>>,
            {
                $Builder {
                    chain: CtxDagAndThenResultNode {
                        prev: self.chain,
                        step: f.into_ctx_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Handle error and transition to Option.
            pub fn catch<Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Option<T>, CtxDagCatchNode<Chain, S::Step>>
            where
                S: IntoCtxStep<Ctx, &'static Err, (), Params>,
                S::Step: for<'x> CtxStepCall<Ctx, &'x Err, Out = ()>,
            {
                $Builder {
                    chain: CtxDagCatchNode {
                        prev: self.chain,
                        step: f.into_ctx_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Transform the error. std: `Result::map_err`
            pub fn map_err<E2, Params, S: IntoCtxStep<Ctx, Err, E2, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Result<T, E2>, CtxMapErrNode<Chain, S::Step>> {
                $Builder {
                    chain: CtxMapErrNode {
                        prev: self.chain,
                        step: f.into_ctx_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Side effect on Ok value. std: `Result::inspect`
            pub fn inspect<Params, S: IntoCtxRefStep<Ctx, T, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Result<T, Err>, CtxInspectResultNode<Chain, S::Step>> {
                $Builder {
                    chain: CtxInspectResultNode {
                        prev: self.chain,
                        step: f.into_ctx_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Side effect on Err. std: `Result::inspect_err`
            pub fn inspect_err<Params, S: IntoCtxRefStep<Ctx, Err, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<Ctx, $U, Result<T, Err>, CtxInspectErrNode<Chain, S::Step>> {
                $Builder {
                    chain: CtxInspectErrNode {
                        prev: self.chain,
                        step: f.into_ctx_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Discard error, enter Option land. std: `Result::ok`
            pub fn ok(self) -> $Builder<Ctx, $U, Option<T>, CtxOkNode<Chain>> {
                $Builder {
                    chain: CtxOkNode { prev: self.chain },
                    _marker: PhantomData,
                }
            }

            /// Exit Result — Err becomes the default value.
            pub fn unwrap_or(
                self,
                default: T,
            ) -> $Builder<Ctx, $U, T, CtxUnwrapOrResultNode<Chain, T>>
            where
                T: Clone,
            {
                $Builder {
                    chain: CtxUnwrapOrResultNode {
                        prev: self.chain,
                        default,
                    },
                    _marker: PhantomData,
                }
            }
        }
    };
}

impl_ctx_dag_combinators!(builder: CtxDagChain, upstream: In);
impl_ctx_dag_combinators!(builder: CtxDagArm, upstream: In);

// =============================================================================
// dispatch_on — terminal keyed dispatch on a projected key (issue #723)
// =============================================================================
//
// Context-aware DAG mirror of pipeline's `dispatch_on`. Two things combine
// here: DAG steps take their value **by reference** (arms are
// `for<'a> CtxStepCall<C, &'a V>`, see `.then`) and the arms thread `&mut C`.
// So the erased arm table is
// `Box<dyn for<'a> CtxStepCall<C, &'a V, Out = Out> + Send>` — an HRTB trait
// object whose associated type is bound under `for<'a>` — and each arm
// receives `&mut C` and `&V`. The key is a *projection* of the value (via
// `key_fn`), not its own discriminant, so there is no unchecked unwrap; every
// arm sees the whole `&V`. `Out` bubbles up so the DAG can `.then(...)` the
// result (or `.build()` when `Out = ()`).

// The terminal arm types (`NoopArm`, `PanicArm`) and the ordinal table finalizer
// (`finalize_ordinal_table`) are shared across all four dispatch surfaces —
// see `crate::dispatch`. Both arms carry a `CtxStepCall` impl generic over their
// input, so they coerce to this surface's erased
// `for<'a> CtxStepCall<C, &'a V, Out = _>` arm slot.

/// Chain node for ctx `.dispatch_on()` on a DAG — terminal keyed dispatch on a
/// projected key. Arms borrow `&V` and thread `&mut C`. Bubbles up the arms'
/// `Out`.
#[doc(hidden)]
pub struct CtxDagDispatchOnNode<C, Prev, V, F, Out> {
    pub(crate) prev: Prev,
    pub(crate) key_fn: F,
    pub(crate) table: Vec<Option<Box<dyn for<'a> CtxStepCall<C, &'a V, Out = Out> + Send>>>, // len == K::VARIANTS
    pub(crate) default: Box<dyn for<'a> CtxStepCall<C, &'a V, Out = Out> + Send>, // PanicArm when exhaustive
}
impl<C, In, Prev, V, K, F, Out> CtxChainCall<C, In> for CtxDagDispatchOnNode<C, Prev, V, F, Out>
where
    Prev: CtxChainCall<C, In, Out = V>,
    V: 'static,
    F: Fn(&V) -> K,
    K: Dispatchable,
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Out {
        let value = self.prev.call(ctx, world, input);
        let idx = (self.key_fn)(&value).ordinal();
        match &mut self.table[idx] {
            Some(arm) => arm.call(ctx, world, &value),
            None => self.default.call(ctx, world, &value),
        }
    }
}

/// Builder for [`dispatch_on`](CtxDagChain::dispatch_on) arms on a ctx DAG.
///
/// The table must be exhaustive (every key armed) or carry a `.default`
/// (or `.default_noop()`) — enforced when the combinator is finalized. Every
/// arm receives `&mut C`, borrows the whole value (`&V`), and returns `Out`,
/// inferred from the arm bodies.
#[must_use = "dispatch arms do nothing unless the builder is returned"]
pub struct CtxDagDispatchOnBuilder<'r, C, V, K, Out> {
    table: Vec<Option<Box<dyn for<'a> CtxStepCall<C, &'a V, Out = Out> + Send>>>,
    default: Option<Box<dyn for<'a> CtxStepCall<C, &'a V, Out = Out> + Send>>,
    registry: &'r Registry,
    _key: PhantomData<fn(K)>,
}
impl<'r, C: 'static, V: 'static, K: Dispatchable + 'static, Out: 'static>
    CtxDagDispatchOnBuilder<'r, C, V, K, Out>
{
    fn new(registry: &'r Registry) -> Self {
        let mut table = Vec::with_capacity(K::VARIANTS);
        table.resize_with(K::VARIANTS, || None);
        Self {
            table,
            default: None,
            registry,
            _key: PhantomData,
        }
    }

    /// Wire the arm that runs when the key equals `k`. The step receives
    /// `&mut C`, borrows the whole value (`&V`), and returns `Out`.
    pub fn arm<S, Params>(mut self, k: K, step: S) -> Self
    where
        S: IntoCtxStep<C, &'static V, Out, Params>,
        S::Step: for<'a> CtxStepCall<C, &'a V, Out = Out> + Send + 'static,
    {
        let idx = k.ordinal();
        assert_first_arm(
            self.table[idx].is_some(),
            "dispatch_on",
            std::any::type_name::<K>(),
            Some(idx),
        );
        self.table[idx] = Some(Box::new(step.into_ctx_step(self.registry)));
        self
    }

    /// Set the fallback for keys with no arm. Receives `&mut C`, borrows the
    /// whole value (`&V`), and returns `Out`.
    pub fn default<S, Params>(mut self, step: S) -> Self
    where
        S: IntoCtxStep<C, &'static V, Out, Params>,
        S::Step: for<'a> CtxStepCall<C, &'a V, Out = Out> + Send + 'static,
    {
        self.default = Some(Box::new(step.into_ctx_step(self.registry)));
        self
    }
}

impl<C, V, K> CtxDagDispatchOnBuilder<'_, C, V, K, ()> {
    /// Set the fallback to a no-op (only when arms return `Out = ()`). Sugar for
    /// a `.default` that ignores the value — the way to opt out of the
    /// exhaustive-table requirement when you don't need a real fallback.
    pub fn default_noop(mut self) -> Self {
        self.default = Some(Box::new(NoopArm));
        self
    }
}

/// Shared body of the three ctx `dispatch_on` forms (chain, fork arm, entry):
/// run the arm builder, enforce exhaustive-or-`.default`, and assemble the node.
/// Each caller only wraps the returned node in its own builder type.
fn ctx_dag_dispatch_on_node<C, Prev, V, K, F, Out, Bf>(
    prev: Prev,
    key_fn: F,
    registry: &Registry,
    build: Bf,
) -> CtxDagDispatchOnNode<C, Prev, V, F, Out>
where
    C: 'static,
    V: 'static,
    K: Dispatchable + 'static,
    Out: 'static,
    Bf: FnOnce(
        CtxDagDispatchOnBuilder<'_, C, V, K, Out>,
    ) -> CtxDagDispatchOnBuilder<'_, C, V, K, Out>,
{
    let b = build(CtxDagDispatchOnBuilder::<C, V, K, Out>::new(registry));
    let (table, default) = finalize_ordinal_table(
        b.table,
        b.default,
        K::VARIANTS,
        || {
            Box::new(PanicArm(PhantomData))
                as Box<dyn for<'a> CtxStepCall<C, &'a V, Out = Out> + Send>
        },
        "dispatch_on",
        std::any::type_name::<K>(),
    );
    CtxDagDispatchOnNode {
        prev,
        key_fn,
        table,
        default,
    }
}

impl<C, In, V, Chain> CtxDagChain<C, In, V, Chain>
where
    Chain: CtxChainCall<C, In, Out = V>,
    V: 'static,
    C: 'static,
{
    /// Keyed dispatch on a *projected* key. `key_fn` maps the value to
    /// a [`Dispatchable`] key; each arm receives `&mut C` and **borrows** the
    /// whole value (`&V`), because DAG steps take their value by reference, and
    /// returns `Out`, which bubbles up. Context-aware mirror of
    /// [`DagChain::dispatch_on`](crate::dag::DagChain::dispatch_on).
    ///
    /// The table must be exhaustive (every key armed) or carry a `.default`
    /// / `.default_noop()`; otherwise this panics at construction (deterministic,
    /// before any dispatch).
    ///
    /// `dispatch_variant` is intentionally **pipeline-only** for now: DAG arms
    /// take `&value`, so unwrapping a variant payload would hand each arm
    /// `&Payload`, which is awkward for multi-field variants and has no caller
    /// yet. `dispatch_on` covers the DAG route-to-sub-DAG case. See issue #723.
    pub fn dispatch_on<K, F, Out, Bf>(
        self,
        key_fn: F,
        registry: &Registry,
        build: Bf,
    ) -> CtxDagChain<C, In, Out, CtxDagDispatchOnNode<C, Chain, V, F, Out>>
    where
        K: Dispatchable + 'static,
        F: Fn(&V) -> K + Send + 'static,
        Out: 'static,
        Bf: FnOnce(
            CtxDagDispatchOnBuilder<'_, C, V, K, Out>,
        ) -> CtxDagDispatchOnBuilder<'_, C, V, K, Out>,
    {
        CtxDagChain {
            chain: ctx_dag_dispatch_on_node(self.chain, key_fn, registry, build),
            _marker: PhantomData,
        }
    }
}

impl<C: 'static, E: 'static> CtxDagBuilder<C, E> {
    /// Keyed dispatch on a *projected* key as the ctx DAG's first
    /// step. Mirrors the entry-point form of [`root`](CtxDagBuilder::root); see
    /// [`CtxDagChain::dispatch_on`] for the continuation form and the note on
    /// why `dispatch_variant` stays pipeline-only. Issue #723.
    pub fn dispatch_on<K, F, Out, Bf>(
        self,
        key_fn: F,
        registry: &Registry,
        build: Bf,
    ) -> CtxDagChain<C, E, Out, CtxDagDispatchOnNode<C, CtxIdentityNode, E, F, Out>>
    where
        K: Dispatchable + 'static,
        F: Fn(&E) -> K + Send + 'static,
        Out: 'static,
        Bf: FnOnce(
            CtxDagDispatchOnBuilder<'_, C, E, K, Out>,
        ) -> CtxDagDispatchOnBuilder<'_, C, E, K, Out>,
    {
        CtxDagChain {
            chain: ctx_dag_dispatch_on_node(CtxIdentityNode, key_fn, registry, build),
            _marker: PhantomData,
        }
    }
}

impl<C, In, V: 'static, Chain> CtxDagArm<C, In, V, Chain> {
    /// Keyed dispatch on a *projected* key, inside a fork arm. The
    /// fork-arm counterpart of [`CtxDagChain::dispatch_on`] — every DAG
    /// combinator is available on both the chain and a fork arm — so a fork arm
    /// can itself route to sub-handlers. Each arm receives `&mut C`, **borrows**
    /// the whole value (`&V`), and returns `Out`, which bubbles up. The table
    /// must be exhaustive or carry a `.default` / `.default_noop()`, else this
    /// panics at construction.
    pub fn dispatch_on<K, F, Out, Bf>(
        self,
        key_fn: F,
        registry: &Registry,
        build: Bf,
    ) -> CtxDagArm<C, In, Out, CtxDagDispatchOnNode<C, Chain, V, F, Out>>
    where
        C: 'static,
        K: Dispatchable + 'static,
        F: Fn(&V) -> K + Send + 'static,
        Out: 'static,
        Bf: FnOnce(
            CtxDagDispatchOnBuilder<'_, C, V, K, Out>,
        ) -> CtxDagDispatchOnBuilder<'_, C, V, K, Out>,
    {
        CtxDagArm {
            chain: ctx_dag_dispatch_on_node(self.chain, key_fn, registry, build),
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// Fork arity macro — arm accumulation, merge, join
// =============================================================================

/// Generates arm accumulation, merge, and join for a context-aware fork type.
macro_rules! impl_ctx_dag_fork {
    (
        fork: $Fork:ident,
        output: $Output:ident,
        upstream: $U:ident
    ) => {
        // =============================================================
        // Arm accumulation: 0->1, 1->2, 2->3, 3->4
        // =============================================================

        impl<Ctx, $U, ForkOut, Chain> $Fork<Ctx, $U, ForkOut, Chain, ()> {
            /// Add the first arm to this fork.
            pub fn arm<AOut, ACh>(
                self,
                f: impl FnOnce(CtxDagArmSeed<Ctx, ForkOut>) -> CtxDagArm<Ctx, ForkOut, AOut, ACh>,
            ) -> $Fork<Ctx, $U, ForkOut, Chain, (CtxDagArm<Ctx, ForkOut, AOut, ACh>,)> {
                let arm = f(CtxDagArmSeed(PhantomData));
                $Fork {
                    chain: self.chain,
                    arms: (arm,),
                    _marker: PhantomData,
                }
            }
        }

        impl<Ctx, $U, ForkOut, Chain, A0, C0>
            $Fork<Ctx, $U, ForkOut, Chain, (CtxDagArm<Ctx, ForkOut, A0, C0>,)>
        {
            /// Add a second arm to this fork.
            pub fn arm<AOut, ACh>(
                self,
                f: impl FnOnce(CtxDagArmSeed<Ctx, ForkOut>) -> CtxDagArm<Ctx, ForkOut, AOut, ACh>,
            ) -> $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, A0, C0>,
                    CtxDagArm<Ctx, ForkOut, AOut, ACh>,
                ),
            > {
                let arm = f(CtxDagArmSeed(PhantomData));
                let (a0,) = self.arms;
                $Fork {
                    chain: self.chain,
                    arms: (a0, arm),
                    _marker: PhantomData,
                }
            }
        }

        impl<Ctx, $U, ForkOut, Chain, A0, C0, A1, C1>
            $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, A0, C0>,
                    CtxDagArm<Ctx, ForkOut, A1, C1>,
                ),
            >
        {
            /// Add a third arm to this fork.
            pub fn arm<AOut, ACh>(
                self,
                f: impl FnOnce(CtxDagArmSeed<Ctx, ForkOut>) -> CtxDagArm<Ctx, ForkOut, AOut, ACh>,
            ) -> $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, A0, C0>,
                    CtxDagArm<Ctx, ForkOut, A1, C1>,
                    CtxDagArm<Ctx, ForkOut, AOut, ACh>,
                ),
            > {
                let arm = f(CtxDagArmSeed(PhantomData));
                let (a0, a1) = self.arms;
                $Fork {
                    chain: self.chain,
                    arms: (a0, a1, arm),
                    _marker: PhantomData,
                }
            }
        }

        impl<Ctx, $U, ForkOut, Chain, A0, C0, A1, C1, A2, C2>
            $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, A0, C0>,
                    CtxDagArm<Ctx, ForkOut, A1, C1>,
                    CtxDagArm<Ctx, ForkOut, A2, C2>,
                ),
            >
        {
            /// Add a fourth arm to this fork.
            pub fn arm<AOut, ACh>(
                self,
                f: impl FnOnce(CtxDagArmSeed<Ctx, ForkOut>) -> CtxDagArm<Ctx, ForkOut, AOut, ACh>,
            ) -> $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, A0, C0>,
                    CtxDagArm<Ctx, ForkOut, A1, C1>,
                    CtxDagArm<Ctx, ForkOut, A2, C2>,
                    CtxDagArm<Ctx, ForkOut, AOut, ACh>,
                ),
            > {
                let arm = f(CtxDagArmSeed(PhantomData));
                let (a0, a1, a2) = self.arms;
                $Fork {
                    chain: self.chain,
                    arms: (a0, a1, a2, arm),
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Merge arity 2
        // =============================================================

        impl<Ctx, $U, ForkOut: 'static, Chain, A0: 'static, C0, A1: 'static, C1>
            $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, A0, C0>,
                    CtxDagArm<Ctx, ForkOut, A1, C1>,
                ),
            >
        {
            /// Merge two arms with a context-aware merge step.
            pub fn merge<MOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Output<
                Ctx,
                $U,
                MOut,
                CtxMergeNode2<Chain, C0, C1, S::Step, ForkOut, A0, A1, MOut>,
            >
            where
                MOut: 'static,
                S: IntoCtxMergeStep<Ctx, (&'static A0, &'static A1), MOut, Params>,
                S::Step: for<'x> CtxMergeStepCall<Ctx, (&'x A0, &'x A1), Out = MOut>,
            {
                let (a0, a1) = self.arms;
                $Output {
                    chain: CtxMergeNode2 {
                        chain: self.chain,
                        arm0: a0.chain,
                        arm1: a1.chain,
                        merge: f.into_ctx_merge_step(registry),
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<Ctx, $U, ForkOut: 'static, Chain, C0, C1>
            $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, (), C0>,
                    CtxDagArm<Ctx, ForkOut, (), C1>,
                ),
            >
        {
            /// Join two sink arms (all producing `()`).
            pub fn join(
                self,
            ) -> $Output<Ctx, $U, (), CtxJoinNode2<Chain, C0, C1, ForkOut>> {
                let (a0, a1) = self.arms;
                $Output {
                    chain: CtxJoinNode2 {
                        chain: self.chain,
                        arm0: a0.chain,
                        arm1: a1.chain,
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Merge arity 3
        // =============================================================

        impl<
            Ctx,
            $U,
            ForkOut: 'static,
            Chain,
            A0: 'static,
            C0,
            A1: 'static,
            C1,
            A2: 'static,
            C2,
        >
            $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, A0, C0>,
                    CtxDagArm<Ctx, ForkOut, A1, C1>,
                    CtxDagArm<Ctx, ForkOut, A2, C2>,
                ),
            >
        {
            /// Merge three arms with a context-aware merge step.
            pub fn merge<MOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Output<
                Ctx,
                $U,
                MOut,
                CtxMergeNode3<Chain, C0, C1, C2, S::Step, ForkOut, A0, A1, A2, MOut>,
            >
            where
                MOut: 'static,
                S: IntoCtxMergeStep<
                    Ctx,
                    (&'static A0, &'static A1, &'static A2),
                    MOut,
                    Params,
                >,
                S::Step:
                    for<'x> CtxMergeStepCall<Ctx, (&'x A0, &'x A1, &'x A2), Out = MOut>,
            {
                let (a0, a1, a2) = self.arms;
                $Output {
                    chain: CtxMergeNode3 {
                        chain: self.chain,
                        arm0: a0.chain,
                        arm1: a1.chain,
                        arm2: a2.chain,
                        merge: f.into_ctx_merge_step(registry),
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<Ctx, $U, ForkOut: 'static, Chain, C0, C1, C2>
            $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, (), C0>,
                    CtxDagArm<Ctx, ForkOut, (), C1>,
                    CtxDagArm<Ctx, ForkOut, (), C2>,
                ),
            >
        {
            /// Join three sink arms (all producing `()`).
            pub fn join(
                self,
            ) -> $Output<Ctx, $U, (), CtxJoinNode3<Chain, C0, C1, C2, ForkOut>> {
                let (a0, a1, a2) = self.arms;
                $Output {
                    chain: CtxJoinNode3 {
                        chain: self.chain,
                        arm0: a0.chain,
                        arm1: a1.chain,
                        arm2: a2.chain,
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Merge arity 4
        // =============================================================

        #[allow(clippy::many_single_char_names)]
        impl<
            Ctx,
            $U,
            ForkOut: 'static,
            Chain,
            A0: 'static,
            C0,
            A1: 'static,
            C1,
            A2: 'static,
            C2,
            A3: 'static,
            C3,
        >
            $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, A0, C0>,
                    CtxDagArm<Ctx, ForkOut, A1, C1>,
                    CtxDagArm<Ctx, ForkOut, A2, C2>,
                    CtxDagArm<Ctx, ForkOut, A3, C3>,
                ),
            >
        {
            /// Merge four arms with a context-aware merge step.
            pub fn merge<MOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Output<
                Ctx,
                $U,
                MOut,
                CtxMergeNode4<Chain, C0, C1, C2, C3, S::Step, ForkOut, A0, A1, A2, A3, MOut>,
            >
            where
                MOut: 'static,
                S: IntoCtxMergeStep<
                    Ctx,
                    (&'static A0, &'static A1, &'static A2, &'static A3),
                    MOut,
                    Params,
                >,
                S::Step: for<'x> CtxMergeStepCall<
                    Ctx,
                    (&'x A0, &'x A1, &'x A2, &'x A3),
                    Out = MOut,
                >,
            {
                let (a0, a1, a2, a3) = self.arms;
                $Output {
                    chain: CtxMergeNode4 {
                        chain: self.chain,
                        arm0: a0.chain,
                        arm1: a1.chain,
                        arm2: a2.chain,
                        arm3: a3.chain,
                        merge: f.into_ctx_merge_step(registry),
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<Ctx, $U, ForkOut: 'static, Chain, C0, C1, C2, C3>
            $Fork<
                Ctx,
                $U,
                ForkOut,
                Chain,
                (
                    CtxDagArm<Ctx, ForkOut, (), C0>,
                    CtxDagArm<Ctx, ForkOut, (), C1>,
                    CtxDagArm<Ctx, ForkOut, (), C2>,
                    CtxDagArm<Ctx, ForkOut, (), C3>,
                ),
            >
        {
            /// Join four sink arms (all producing `()`).
            pub fn join(
                self,
            ) -> $Output<Ctx, $U, (), CtxJoinNode4<Chain, C0, C1, C2, C3, ForkOut>> {
                let (a0, a1, a2, a3) = self.arms;
                $Output {
                    chain: CtxJoinNode4 {
                        chain: self.chain,
                        arm0: a0.chain,
                        arm1: a1.chain,
                        arm2: a2.chain,
                        arm3: a3.chain,
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }
    };
}

impl_ctx_dag_fork!(fork: CtxDagChainFork, output: CtxDagChain, upstream: In);
impl_ctx_dag_fork!(fork: CtxDagArmFork, output: CtxDagArm, upstream: In);

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Res, ResMut, WorldBuilder};

    struct TradingCtx {
        book_updates: u32,
        risk_checks: u32,
        submissions: u32,
    }

    // -- Fork/merge basic test ------------------------------------------------

    #[test]
    fn ctx_dag_fork_merge_two_arms() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn decode(ctx: &mut TradingCtx, raw: u32) -> u64 {
            ctx.book_updates += 1;
            raw as u64
        }

        fn arm_a(ctx: &mut TradingCtx, val: &u64) -> u64 {
            ctx.book_updates += 1;
            *val * 2
        }

        fn arm_b(ctx: &mut TradingCtx, val: &u64) -> u64 {
            ctx.risk_checks += 1;
            *val + 10
        }

        fn merge_fn(ctx: &mut TradingCtx, a: &u64, b: &u64) {
            ctx.submissions += 1;
            assert_eq!(*a, 10); // 5 * 2
            assert_eq!(*b, 15); // 5 + 10
        }

        let mut dag = CtxDagBuilder::<TradingCtx, u32>::new()
            .root(decode, reg)
            .fork()
            .arm(|seed| seed.then(arm_a, reg))
            .arm(|seed| seed.then(arm_b, reg))
            .merge(merge_fn, reg)
            .build();

        let mut ctx = TradingCtx {
            book_updates: 0,
            risk_checks: 0,
            submissions: 0,
        };

        dag.run(&mut ctx, &mut world, 5);

        assert_eq!(ctx.book_updates, 2); // decode + arm_a
        assert_eq!(ctx.risk_checks, 1);
        assert_eq!(ctx.submissions, 1);
    }

    // -- Linear chain test ----------------------------------------------------

    #[test]
    fn ctx_dag_linear_then() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root(ctx: &mut TradingCtx, x: u32) -> u64 {
            ctx.book_updates += 1;
            x as u64 * 2
        }

        fn store(ctx: &mut TradingCtx, mut out: ResMut<u64>, val: &u64) {
            ctx.submissions += 1;
            *out = *val;
        }

        let mut dag = CtxDagBuilder::<TradingCtx, u32>::new()
            .root(root, reg)
            .then(store, reg)
            .build();

        let mut ctx = TradingCtx {
            book_updates: 0,
            risk_checks: 0,
            submissions: 0,
        };

        dag.run(&mut ctx, &mut world, 5);

        assert_eq!(ctx.book_updates, 1);
        assert_eq!(ctx.submissions, 1);
        assert_eq!(*world.resource::<u64>(), 10);
    }

    // -- Join test (all arms produce ()) --------------------------------------

    #[test]
    fn ctx_dag_fork_join() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        fn root(_ctx: &mut TradingCtx, x: u32) -> u64 {
            x as u64
        }

        fn side_a(ctx: &mut TradingCtx, _val: &u64) {
            ctx.book_updates += 1;
        }

        fn side_b(ctx: &mut TradingCtx, _val: &u64) {
            ctx.risk_checks += 1;
        }

        let mut dag = CtxDagBuilder::<TradingCtx, u32>::new()
            .root(root, reg)
            .fork()
            .arm(|seed| seed.then(side_a, reg))
            .arm(|seed| seed.then(side_b, reg))
            .join()
            .build();

        let mut ctx = TradingCtx {
            book_updates: 0,
            risk_checks: 0,
            submissions: 0,
        };

        dag.run(&mut ctx, &mut world, 42);

        assert_eq!(ctx.book_updates, 1);
        assert_eq!(ctx.risk_checks, 1);
    }

    // -- Guard + merge --------------------------------------------------------

    #[test]
    fn ctx_dag_guard_before_fork() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        fn root(_ctx: &mut TradingCtx, x: u32) -> u32 {
            x
        }

        let mut dag = CtxDagBuilder::<TradingCtx, u32>::new()
            .root(root, reg)
            .guard(|_ctx: &mut TradingCtx, x: &u32| *x > 10, reg)
            .map(
                |ctx: &mut TradingCtx, x: &u32| {
                    ctx.submissions += 1;
                    *x * 2
                },
                reg,
            )
            .unwrap_or(0u32)
            .then(
                |ctx: &mut TradingCtx, val: &u32| {
                    ctx.book_updates = *val;
                },
                reg,
            )
            .build();

        let mut ctx = TradingCtx {
            book_updates: 0,
            risk_checks: 0,
            submissions: 0,
        };

        // x = 5, guard fails
        dag.run(&mut ctx, &mut world, 5);
        assert_eq!(ctx.book_updates, 0);
        assert_eq!(ctx.submissions, 0);

        // x = 20, guard passes
        dag.run(&mut ctx, &mut world, 20);
        assert_eq!(ctx.book_updates, 40);
        assert_eq!(ctx.submissions, 1);
    }

    // -- 3-arm fork test ------------------------------------------------------

    #[test]
    fn ctx_dag_three_arm_fork_merge() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn decode(ctx: &mut TradingCtx, raw: u32) -> u64 {
            ctx.book_updates += 1;
            raw as u64
        }

        fn arm_a(ctx: &mut TradingCtx, val: &u64) -> u64 {
            ctx.book_updates += 1;
            *val * 2
        }

        fn arm_b(ctx: &mut TradingCtx, val: &u64) -> u64 {
            ctx.risk_checks += 1;
            *val + 10
        }

        fn arm_c(ctx: &mut TradingCtx, val: &u64) -> u64 {
            ctx.submissions += 1;
            *val * 3
        }

        fn merge3(ctx: &mut TradingCtx, a: &u64, b: &u64, c: &u64) {
            ctx.submissions += 1;
            assert_eq!(*a, 10); // 5 * 2
            assert_eq!(*b, 15); // 5 + 10
            assert_eq!(*c, 15); // 5 * 3
        }

        let mut dag = CtxDagBuilder::<TradingCtx, u32>::new()
            .root(decode, reg)
            .fork()
            .arm(|seed| seed.then(arm_a, reg))
            .arm(|seed| seed.then(arm_b, reg))
            .arm(|seed| seed.then(arm_c, reg))
            .merge(merge3, reg)
            .build();

        let mut ctx = TradingCtx {
            book_updates: 0,
            risk_checks: 0,
            submissions: 0,
        };

        dag.run(&mut ctx, &mut world, 5);

        assert_eq!(ctx.book_updates, 2); // decode + arm_a
        assert_eq!(ctx.risk_checks, 1); // arm_b
        assert_eq!(ctx.submissions, 2); // arm_c + merge3
    }

    // -- Merge with Param resolution ------------------------------------------

    #[test]
    fn ctx_dag_merge_with_param() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(100);
        let mut world = wb.build();
        let reg = world.registry();

        fn decode(ctx: &mut TradingCtx, raw: u32) -> u64 {
            ctx.book_updates += 1;
            raw as u64
        }

        fn arm_a(_ctx: &mut TradingCtx, val: &u64) -> u64 {
            *val * 2
        }

        fn arm_b(_ctx: &mut TradingCtx, val: &u64) -> u64 {
            *val + 10
        }

        // Merge step that uses Res<u64> — exercises the unsafe Param::fetch path
        fn merge_with_res(ctx: &mut TradingCtx, scale: Res<u64>, a: &u64, b: &u64) {
            ctx.submissions += 1;
            // scale=100, a=10 (5*2), b=15 (5+10)
            assert_eq!(*scale, 100);
            assert_eq!(*a + *b, 25);
        }

        let mut dag = CtxDagBuilder::<TradingCtx, u32>::new()
            .root(decode, reg)
            .fork()
            .arm(|seed| seed.then(arm_a, reg))
            .arm(|seed| seed.then(arm_b, reg))
            .merge(merge_with_res, reg)
            .build();

        let mut ctx = TradingCtx {
            book_updates: 0,
            risk_checks: 0,
            submissions: 0,
        };

        dag.run(&mut ctx, &mut world, 5);

        assert_eq!(ctx.book_updates, 1);
        assert_eq!(ctx.submissions, 1);
    }
}
