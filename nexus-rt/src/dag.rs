// Builder return types use complex generics for compile-time edge validation.
#![allow(clippy::type_complexity)]
// Handler arity is architecturally required by the Param trait — handlers
// take N typed parameters and the macro-generated dispatch impls expand
// per-arity into call_inner functions with N + Input arguments. Module-level
// allow rather than one inline attribute per arity expansion.
#![allow(clippy::too_many_arguments)]

//! DAG pipeline — monomorphized data-flow graphs with fan-out and merge.
//!
//! [`DagBuilder`] begins a typed DAG that encodes topology in the type system.
//! After monomorphization, the entire DAG is a single flat function with
//! all values as stack locals — no arena, no vtable dispatch. The only
//! `unsafe` is in the shared [`Param::fetch`](crate::Param) path
//! (resource access by pre-resolved index).
//!
//! Nodes receive their input **by reference** — fan-out is free (multiple
//! arms borrow the same stack local). Nodes produce owned output values
//! passed to the next step.
//!
//! # When to use
//!
//! Use DAG pipelines when data needs to fan out to multiple arms and
//! merge back. For linear chains, prefer [`PipelineBuilder`](crate::PipelineBuilder).
//! For dynamic fan-out by reference, use [`FanOut`](crate::FanOut) or
//! [`Broadcast`](crate::Broadcast).
//!
//! # Flow control
//!
//! Option and Result combinators (`.guard()`, `.map()`, `.and_then()`,
//! `.filter()`, `.catch()`, etc.) work on both the main chain and
//! within arms.
//!
//! **Within an arm**, `None` / `Err` short-circuits the remaining steps
//! in **that arm only**. Sibling arms execute unconditionally. The merge
//! step receives whatever each arm produced (including `None`).
//!
//! `.tap()` observes the value mid-chain without consuming or changing it.
//!
//! `.route()` is binary conditional routing — evaluates a predicate and
//! executes exactly one of two arms. Both arms must produce the same
//! output type. For N-ary routing, nest `route` calls.
//!
//! To skip an entire fork, resolve Option/Result **before** `.fork()`:
//!
//! ```ignore
//! DagBuilder::<RawMsg>::new()
//!     .root(decode, reg)
//!     .guard(|msg: &RawMsg| !msg.is_empty(), reg)  // None skips everything below
//!     .unwrap_or(default)                           // → T, enter fork with concrete type
//!     .fork()
//!     // arms work with &T, not &Option<T>
//! ```
//!
//! # Combinator quick reference
//!
//! **Topology:** `.root()`, `.then()`, `.fork()`, `.arm()`, `.merge()`,
//! `.join()`, `.build()`
//!
//! **Flow control:** `.guard()`, `.tap()`, `.route()`, `.tee()`, `.scan()`,
//! `.dedup()`
//!
//! **Tuple `(A, B, ...)` (2-5 elements):** `.splat()` (→ splat builder,
//! call `.then()` with destructured `&T` args)
//!
//! **Option:** `.map()`, `.filter()`, `.inspect()`, `.and_then()`,
//! `.on_none()`, `.ok_or()`, `.unwrap_or()`
//!
//! **Result:** `.map()`, `.and_then()`, `.catch()`, `.map_err()`,
//! `.ok()`, `.unwrap_or()`
//!
//! **Bool:** `.not()`, `.and()`, `.or()`, `.xor()`
//!
//! **Terminal:** `.dispatch()`, `.cloned()`, `.build()`, `.build_batch(cap)`
//!
//! All combinators accepting functions resolve `Param` dependencies at build
//! time via `IntoStep`, `IntoRefStep`, or `IntoProducer` — named functions
//! get direct-pointer access. Arity-0 closures work everywhere. Raw
//! `&mut World` closures are available as an escape hatch via `Opaque`.
//!
//! # Splat — tuple destructuring
//!
//! When a step returns a tuple, the next step normally receives the
//! whole tuple as `&(A, B)`. `.splat()` destructures it into individual
//! reference arguments (`&A, &B`), reusing the existing merge step
//! infrastructure:
//!
//! ```ignore
//! fn split(t: Tick) -> (f64, u64) { (t.price, t.size) }
//! fn weighted(price: &f64, size: &u64) -> f64 { *price * *size as f64 }
//!
//! DagBuilder::<Tick>::new()
//!     .root(split, reg)       // Tick → (f64, u64)
//!     .splat()                // destructure
//!     .then(weighted, reg)    // (&f64, &u64) → f64
//!     .build();
//! ```
//!
//! Supported for tuples of 2-5 elements. Beyond 5, define a named
//! struct — if a combinator stage needs that many arguments, a struct
//! makes the intent clearer and the code more maintainable.
//!
//! # Node signatures
//!
//! The root node takes the event by value. All other nodes take their
//! input by reference:
//!
//! ```ignore
//! // Root: event by value
//! fn decode(raw: RawMsg) -> DecodedMsg { .. }
//!
//! // Regular: input by reference
//! fn update_ob(msg: &DecodedMsg) { .. }
//! fn check_risk(config: Res<Config>, msg: &DecodedMsg) -> RiskResult { .. }
//! ```
//!
//! # Examples
//!
//! ```
//! use nexus_rt::{WorldBuilder, ResMut, Handler, Resource};
//! use nexus_rt::dag::DagBuilder;
//!
//! #[derive(Resource)]
//! struct Accum(u64);
//!
//! let mut wb = WorldBuilder::new();
//! wb.register(Accum(0));
//! let mut world = wb.build();
//! let reg = world.registry();
//!
//! fn double(x: u32) -> u64 { x as u64 * 2 }
//! fn store(mut out: ResMut<Accum>, val: &u64) { out.0 = *val; }
//!
//! let mut dag = DagBuilder::<u32>::new()
//!     .root(double, reg)
//!     .then(store, reg)
//!     .build();
//!
//! dag.run(&mut world, 5u32);
//! assert_eq!(world.resource::<Accum>().0, 10);
//! ```
//!
//! # Returning DAGs from functions (Rust 2024)
//!
//! When a factory function takes `&Registry` and returns `impl Handler<E>`,
//! Rust 2024 captures the registry borrow in the return type by default.
//! Use `+ use<...>` to exclude it:
//!
//! ```ignore
//! fn on_tick<C: Config>(
//!     reg: &Registry,
//! ) -> impl Handler<Tick> + use<C> {
//!     DagBuilder::<Tick>::new()
//!         .root(split::<C>, reg)
//!         .fork()
//!         // ...
//!         .build()
//! }
//! ```
//!
//! List every type parameter the DAG captures; omit the `&Registry`
//! lifetime — it's consumed during `.build()`. See the
//! [crate-level docs](crate#returning-impl-handler-from-functions-rust-2024)
//! for the full explanation.

use std::marker::PhantomData;

use crate::Handler;
use crate::pipeline::{
    AndBoolNode, ChainCall, ClonedNode, ClonedOptionNode, ClonedResultNode, DagAndThenOptionNode,
    DagAndThenResultNode, DagCatchNode, DagMapOptionNode, DagMapResultNode, DagRouteNode,
    DagThenNode, DedupNode, DiscardOptionNode, DispatchNode, FilterNode, GuardNode, IdentityNode,
    InspectErrNode, InspectOptionNode, InspectResultNode, IntoProducer, IntoRefScanStep,
    IntoRefStep, IntoStep, MapErrNode, NotNode, OkOrElseNode, OkOrNode, OkResultNode, OnNoneNode,
    OrBoolNode, OrElseNode, RefScanNode, StepCall, TapNode, TeeNode, ThenNode,
    UnwrapOrElseOptionNode, UnwrapOrElseResultNode, UnwrapOrOptionNode, UnwrapOrResultNode,
    XorBoolNode,
};
use crate::world::{Registry, World};

// =============================================================================
// MergeStepCall / IntoMergeStep — merge step dispatch
// =============================================================================

/// Callable trait for resolved merge steps.
///
/// Like [`StepCall`] but for merge steps with multiple reference inputs
/// bundled as `Inputs` (e.g. `(&'a A, &'a B)`).
#[doc(hidden)]
pub trait MergeStepCall<Inputs, Out> {
    /// Call this merge step with a world reference and input references.
    fn call(&mut self, world: &mut World, inputs: Inputs) -> Out;
}

/// Converts a named function into a resolved merge step.
///
/// Params first, then N reference inputs, returns output:
///
/// ```ignore
/// fn check(config: Res<Config>, ob: &ObResult, risk: &RiskResult) -> Decision { .. }
/// ```
#[doc(hidden)]
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a merge step",
    note = "merge steps take reference tuple inputs from the fork arms",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoMergeStep<Inputs, Out, Params> {
    /// The concrete resolved merge step type.
    type Step: MergeStepCall<Inputs, Out>;

    /// Resolve Param state from the registry and produce a merge step.
    fn into_merge_step(self, registry: &Registry) -> Self::Step;
}

/// Internal: pre-resolved merge step with cached Param state.
#[doc(hidden)]
pub struct MergeStep<F, Params: crate::handler::Param> {
    f: F,
    state: Params::State,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

// -- Merge arity 2 -----------------------------------------------------------

// Param arity 0: closures work.
impl<A, B, Out, F> MergeStepCall<(&A, &B), Out> for MergeStep<F, ()>
where
    F: FnMut(&A, &B) -> Out + 'static,
{
    #[inline(always)]
    fn call(&mut self, _world: &mut World, inputs: (&A, &B)) -> Out {
        (self.f)(inputs.0, inputs.1)
    }
}

impl<A, B, Out, F> IntoMergeStep<(&A, &B), Out, ()> for F
where
    F: FnMut(&A, &B) -> Out + 'static,
{
    type Step = MergeStep<F, ()>;

    fn into_merge_step(self, registry: &Registry) -> Self::Step {
        MergeStep {
            f: self,
            state: <() as crate::handler::Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// Param arities 1-8 for merge arity 2.
macro_rules! impl_merge2_step {
    ($($P:ident),+) => {
        impl<A, B, Out, F: 'static, $($P: crate::handler::Param + 'static),+>
            MergeStepCall<(&A, &B), Out> for MergeStep<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &A, &B) -> Out +
                FnMut($($P::Item<'a>,)+ &A, &B) -> Out,
        {
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, inputs: (&A, &B)) -> Out {
                fn call_inner<$($P,)+ IA, IB, Output>(
                    mut f: impl FnMut($($P,)+ &IA, &IB) -> Output,
                    $($P: $P,)+
                    a: &IA, b: &IB,
                ) -> Output {
                    f($($P,)+ a, b)
                }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as crate::handler::Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ inputs.0, inputs.1)
            }
        }

        impl<A, B, Out, F: 'static, $($P: crate::handler::Param + 'static),+>
            IntoMergeStep<(&A, &B), Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &A, &B) -> Out +
                FnMut($($P::Item<'a>,)+ &A, &B) -> Out,
        {
            type Step = MergeStep<F, ($($P,)+)>;

            fn into_merge_step(self, registry: &Registry) -> Self::Step {
                let state = <($($P,)+) as crate::handler::Param>::init(registry);
                {
                    #[allow(non_snake_case)]
                    let ($($P,)+) = &state;
                    registry.check_access(&[
                        $((<$P as crate::handler::Param>::resource_id($P),
                           std::any::type_name::<$P>()),)+
                    ]);
                }
                MergeStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

// -- Merge arity 3 -----------------------------------------------------------

impl<A, B, C, Out, F> MergeStepCall<(&A, &B, &C), Out> for MergeStep<F, ()>
where
    F: FnMut(&A, &B, &C) -> Out + 'static,
{
    #[inline(always)]
    fn call(&mut self, _world: &mut World, inputs: (&A, &B, &C)) -> Out {
        (self.f)(inputs.0, inputs.1, inputs.2)
    }
}

impl<A, B, C, Out, F> IntoMergeStep<(&A, &B, &C), Out, ()> for F
where
    F: FnMut(&A, &B, &C) -> Out + 'static,
{
    type Step = MergeStep<F, ()>;

    fn into_merge_step(self, registry: &Registry) -> Self::Step {
        MergeStep {
            f: self,
            state: <() as crate::handler::Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_merge3_step {
    ($($P:ident),+) => {
        impl<A, B, C, Out, F: 'static, $($P: crate::handler::Param + 'static),+>
            MergeStepCall<(&A, &B, &C), Out> for MergeStep<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &A, &B, &C) -> Out +
                FnMut($($P::Item<'a>,)+ &A, &B, &C) -> Out,
        {
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, inputs: (&A, &B, &C)) -> Out {
                fn call_inner<$($P,)+ IA, IB, IC, Output>(
                    mut f: impl FnMut($($P,)+ &IA, &IB, &IC) -> Output,
                    $($P: $P,)+
                    a: &IA, b: &IB, c: &IC,
                ) -> Output {
                    f($($P,)+ a, b, c)
                }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as crate::handler::Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ inputs.0, inputs.1, inputs.2)
            }
        }

        impl<A, B, C, Out, F: 'static, $($P: crate::handler::Param + 'static),+>
            IntoMergeStep<(&A, &B, &C), Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &A, &B, &C) -> Out +
                FnMut($($P::Item<'a>,)+ &A, &B, &C) -> Out,
        {
            type Step = MergeStep<F, ($($P,)+)>;

            fn into_merge_step(self, registry: &Registry) -> Self::Step {
                let state = <($($P,)+) as crate::handler::Param>::init(registry);
                {
                    #[allow(non_snake_case)]
                    let ($($P,)+) = &state;
                    registry.check_access(&[
                        $((<$P as crate::handler::Param>::resource_id($P),
                           std::any::type_name::<$P>()),)+
                    ]);
                }
                MergeStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

// -- Merge arity 4 -----------------------------------------------------------

impl<A, B, C, D, Out, F> MergeStepCall<(&A, &B, &C, &D), Out> for MergeStep<F, ()>
where
    F: FnMut(&A, &B, &C, &D) -> Out + 'static,
{
    #[inline(always)]
    fn call(&mut self, _world: &mut World, i: (&A, &B, &C, &D)) -> Out {
        (self.f)(i.0, i.1, i.2, i.3)
    }
}

impl<A, B, C, D, Out, F> IntoMergeStep<(&A, &B, &C, &D), Out, ()> for F
where
    F: FnMut(&A, &B, &C, &D) -> Out + 'static,
{
    type Step = MergeStep<F, ()>;
    fn into_merge_step(self, registry: &Registry) -> Self::Step {
        MergeStep {
            f: self,
            state: <() as crate::handler::Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_merge4_step {
    ($($P:ident),+) => {
        impl<A, B, C, D, Out, F: 'static, $($P: crate::handler::Param + 'static),+>
            MergeStepCall<(&A, &B, &C, &D), Out> for MergeStep<F, ($($P,)+)>
        where for<'a> &'a mut F:
            FnMut($($P,)+ &A, &B, &C, &D) -> Out +
            FnMut($($P::Item<'a>,)+ &A, &B, &C, &D) -> Out,
        {
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, i: (&A, &B, &C, &D)) -> Out {
                fn call_inner<$($P,)+ IA, IB, IC, ID, Output>(
                    mut f: impl FnMut($($P,)+ &IA, &IB, &IC, &ID) -> Output,
                    $($P: $P,)+ a: &IA, b: &IB, c: &IC, d: &ID,
                ) -> Output { f($($P,)+ a, b, c, d) }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as crate::handler::Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ i.0, i.1, i.2, i.3)
            }
        }
        impl<A, B, C, D, Out, F: 'static, $($P: crate::handler::Param + 'static),+>
            IntoMergeStep<(&A, &B, &C, &D), Out, ($($P,)+)> for F
        where for<'a> &'a mut F:
            FnMut($($P,)+ &A, &B, &C, &D) -> Out +
            FnMut($($P::Item<'a>,)+ &A, &B, &C, &D) -> Out,
        {
            type Step = MergeStep<F, ($($P,)+)>;
            fn into_merge_step(self, registry: &Registry) -> Self::Step {
                let state = <($($P,)+) as crate::handler::Param>::init(registry);
                { #[allow(non_snake_case)] let ($($P,)+) = &state;
                  registry.check_access(&[$((<$P as crate::handler::Param>::resource_id($P), std::any::type_name::<$P>()),)+]); }
                MergeStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

// -- Merge arity 5 -----------------------------------------------------------

impl<A, B, C, D, E, Out, F> MergeStepCall<(&A, &B, &C, &D, &E), Out> for MergeStep<F, ()>
where
    F: FnMut(&A, &B, &C, &D, &E) -> Out + 'static,
{
    #[inline(always)]
    fn call(&mut self, _world: &mut World, i: (&A, &B, &C, &D, &E)) -> Out {
        (self.f)(i.0, i.1, i.2, i.3, i.4)
    }
}

impl<A, B, C, D, E, Out, F> IntoMergeStep<(&A, &B, &C, &D, &E), Out, ()> for F
where
    F: FnMut(&A, &B, &C, &D, &E) -> Out + 'static,
{
    type Step = MergeStep<F, ()>;
    fn into_merge_step(self, registry: &Registry) -> Self::Step {
        MergeStep {
            f: self,
            state: <() as crate::handler::Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_merge5_step {
    ($($P:ident),+) => {
        impl<A, B, C, D, E, Out, F: 'static, $($P: crate::handler::Param + 'static),+>
            MergeStepCall<(&A, &B, &C, &D, &E), Out> for MergeStep<F, ($($P,)+)>
        where for<'a> &'a mut F:
            FnMut($($P,)+ &A, &B, &C, &D, &E) -> Out +
            FnMut($($P::Item<'a>,)+ &A, &B, &C, &D, &E) -> Out,
        {
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, i: (&A, &B, &C, &D, &E)) -> Out {
                fn call_inner<$($P,)+ IA, IB, IC, ID, IE, Output>(
                    mut f: impl FnMut($($P,)+ &IA, &IB, &IC, &ID, &IE) -> Output,
                    $($P: $P,)+ a: &IA, b: &IB, c: &IC, d: &ID, e: &IE,
                ) -> Output { f($($P,)+ a, b, c, d, e) }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as crate::handler::Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ i.0, i.1, i.2, i.3, i.4)
            }
        }
        impl<A, B, C, D, E, Out, F: 'static, $($P: crate::handler::Param + 'static),+>
            IntoMergeStep<(&A, &B, &C, &D, &E), Out, ($($P,)+)> for F
        where for<'a> &'a mut F:
            FnMut($($P,)+ &A, &B, &C, &D, &E) -> Out +
            FnMut($($P::Item<'a>,)+ &A, &B, &C, &D, &E) -> Out,
        {
            type Step = MergeStep<F, ($($P,)+)>;
            fn into_merge_step(self, registry: &Registry) -> Self::Step {
                let state = <($($P,)+) as crate::handler::Param>::init(registry);
                { #[allow(non_snake_case)] let ($($P,)+) = &state;
                  registry.check_access(&[$((<$P as crate::handler::Param>::resource_id($P), std::any::type_name::<$P>()),)+]); }
                MergeStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_merge2_step);
all_tuples!(impl_merge3_step);
all_tuples!(impl_merge4_step);
all_tuples!(impl_merge5_step);

// =============================================================================
// DAG — monomorphized, zero vtable dispatch
// =============================================================================
//
// Encodes DAG topology in the type system at compile time. After
// monomorphization, the entire DAG is a single flat function with all
// values as stack locals. No arena, no bitmap. Only unsafe is
// in the shared Param::fetch path (resource access by pre-resolved index).
//
// Fan-out: multiple nodes borrow the same stack local (no Clone).
// Merge: merge step borrows all arm outputs.
// Panic safety: stack unwinding drops all locals automatically.

/// Entry point for building a DAG pipeline.
///
/// The DAG encodes topology in the type system at compile time,
/// producing a single monomorphized chain of named node types. All values live as
/// stack locals in the `run()` body — no arena, no vtable dispatch.
/// The only `unsafe` is in the shared [`Param::fetch`](crate::Param)
/// path (resource access by pre-resolved index).
///
/// # Examples
///
/// ```
/// use nexus_rt::{WorldBuilder, ResMut, Handler, Resource};
/// use nexus_rt::dag::DagBuilder;
///
/// #[derive(Resource)]
/// struct Accum(u64);
///
/// let mut wb = WorldBuilder::new();
/// wb.register(Accum(0));
/// let mut world = wb.build();
/// let reg = world.registry();
///
/// fn double(x: u32) -> u64 { x as u64 * 2 }
/// fn store(mut out: ResMut<Accum>, val: &u64) { out.0 = *val; }
///
/// let mut dag = DagBuilder::<u32>::new()
///     .root(double, reg)
///     .then(store, reg)
///     .build();
///
/// dag.run(&mut world, 5u32);
/// assert_eq!(world.resource::<Accum>().0, 10);
/// ```
#[must_use = "a DAG builder does nothing unless you chain steps and call .build()"]
pub struct DagBuilder<E>(PhantomData<fn(E)>);

impl<E> DagBuilder<E> {
    /// Create a new typed DAG entry point.
    pub fn new() -> Self {
        Self(PhantomData)
    }

    /// Set the root step. Takes the event `E` by value, produces `Out`.
    pub fn root<Out, Params, S>(
        self,
        f: S,
        registry: &Registry,
    ) -> DagChain<E, Out, ThenNode<IdentityNode, S::Step>>
    where
        Out: 'static,
        S: IntoStep<E, Out, Params>,
    {
        DagChain {
            chain: ThenNode {
                prev: IdentityNode,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }
}

impl<E> Default for DagBuilder<E> {
    fn default() -> Self {
        Self::new()
    }
}

/// Main chain builder for a typed DAG.
///
/// `Chain` implements [`ChainCall<E, Out = Out>`] — a named node type
/// representing all steps composed so far. No closures, no `use<>`.
#[must_use = "DAG chain does nothing until .build() is called"]
pub struct DagChain<E, Out, Chain> {
    pub(crate) chain: Chain,
    pub(crate) _marker: PhantomData<fn(E) -> Out>,
}

impl<E, Out: 'static, Chain> DagChain<E, Out, Chain> {
    /// Enter fork mode. Subsequent `.arm()` calls add parallel branches.
    pub fn fork(self) -> DagChainFork<E, Out, Chain, ()> {
        DagChainFork {
            chain: self.chain,
            arms: (),
            _marker: PhantomData,
        }
    }
}

impl<E, Chain> DagChain<E, (), Chain>
where
    Chain: ChainCall<E, Out = ()> + Send,
{
    /// Finalize into a [`Dag`] that implements [`Handler<E>`].
    ///
    /// Only available when the chain ends with `()` or `Option<()>`.
    /// If your DAG produces a value, add a final `.then()` that consumes
    /// the output.
    #[must_use = "building a DAG without storing it does nothing"]
    pub fn build(self) -> Dag<Chain> {
        Dag { chain: self.chain }
    }
}

impl<E, Chain> DagChain<E, Option<()>, Chain>
where
    Chain: ChainCall<E, Out = Option<()>> + Send,
{
    /// Finalize into a [`Dag`], discarding the `Option<()>`.
    ///
    /// DAGs ending with `Option<()>` produce the same [`Dag`] as those
    /// ending with `()`.
    #[must_use = "building a DAG without storing it does nothing"]
    pub fn build(self) -> Dag<DiscardOptionNode<Chain>> {
        Dag {
            chain: DiscardOptionNode { prev: self.chain },
        }
    }
}

/// Arm builder seed. Used in `.arm()` closures and to build arms for
/// [`.route()`](DagChain::route).
///
/// Call `.then()` to add the first step in this arm.
pub struct DagArmSeed<In>(PhantomData<fn(*const In)>);

impl<In: 'static> DagArmSeed<In> {
    /// Create a new arm builder seed.
    ///
    /// Used to build arms passed to [`DagChain::route`] or
    /// [`DagArm::route`]:
    ///
    /// ```ignore
    /// let fast = DagArmSeed::new().then(fast_path, &reg);
    /// let slow = DagArmSeed::new().then(slow_path, &reg);
    /// dag.route(predicate, &reg, fast, slow)
    /// ```
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<In: 'static> Default for DagArmSeed<In> {
    fn default() -> Self {
        Self::new()
    }
}

impl<In: 'static> DagArmSeed<In> {
    /// Add the first step in this arm. Takes `&In` by reference.
    pub fn then<Out, Params, S>(
        self,
        f: S,
        registry: &Registry,
    ) -> DagArm<In, Out, ThenNode<IdentityNode, S::Step>>
    where
        Out: 'static,
        S: IntoStep<&'static In, Out, Params>,
        S::Step: for<'a> StepCall<&'a In, Out = Out>,
    {
        DagArm {
            chain: ThenNode {
                prev: IdentityNode,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }
}

/// Built arm in a typed DAG fork.
///
/// `Chain` implements [`ChainCall<&In, Out = Out>`] — a named node type
/// for this arm's steps.
pub struct DagArm<In, Out, Chain> {
    pub(crate) chain: Chain,
    pub(crate) _marker: PhantomData<fn(*const In) -> Out>,
}

impl<In: 'static, Out: 'static, Chain> DagArm<In, Out, Chain> {
    /// Enter fork mode within this arm.
    pub fn fork(self) -> DagArmFork<In, Out, Chain, ()> {
        DagArmFork {
            chain: self.chain,
            arms: (),
            _marker: PhantomData,
        }
    }
}

/// Fork builder on the main chain. Accumulates arms as a tuple.
pub struct DagChainFork<E, ForkOut, Chain, Arms> {
    chain: Chain,
    arms: Arms,
    _marker: PhantomData<fn(E) -> ForkOut>,
}

/// Fork builder within an arm. Accumulates sub-arms as a tuple.
pub struct DagArmFork<In, ForkOut, Chain, Arms> {
    chain: Chain,
    arms: Arms,
    _marker: PhantomData<fn(*const In) -> ForkOut>,
}

/// Final built DAG. Implements [`Handler<E>`].
///
/// Created by [`DagChain::build`]. The entire DAG is monomorphized
/// at compile time — no boxing, no virtual dispatch, no arena.
/// Supports `for<'a> Handler<&'a T>` for zero-copy event dispatch.
/// For batch processing, see [`BatchDag`].
pub struct Dag<Chain> {
    chain: Chain,
}

impl<E, Chain> Handler<E> for Dag<Chain>
where
    Chain: ChainCall<E, Out = ()> + Send,
{
    fn run(&mut self, world: &mut World, event: E) {
        self.chain.call(world, event);
    }

    fn name(&self) -> &'static str {
        "dag::Dag"
    }
}

// =============================================================================
// Fork arity macro — arm accumulation, merge, join
// =============================================================================

// =============================================================================
// Combinator macro — shared between DagChain and DagArm
// =============================================================================

/// Generates step combinators, Option/Result helpers, and clone helpers.
///
/// DagChain and DagArm use the same named node types — `In` appears only
/// on the `ChainCall<In>` trait impl, not on the struct. No closures, no
/// `use<>` captures.
macro_rules! impl_dag_combinators {
    (builder: $Builder:ident, upstream: $U:ident) => {
        // =============================================================
        // Core — any Out
        // =============================================================

        impl<$U, Out: 'static, Chain> $Builder<$U, Out, Chain> {
            /// Append a step. The step receives `&Out` by reference.
            pub fn then<NewOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, NewOut, DagThenNode<Chain, S::Step, NewOut>>
            where
                NewOut: 'static,
                S: IntoStep<&'static Out, NewOut, Params>,
                S::Step: for<'a> StepCall<&'a Out, Out = NewOut>,
            {
                $Builder {
                    chain: DagThenNode {
                        prev: self.chain,
                        step: f.into_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Dispatch output to a [`Handler<Out>`].
            pub fn dispatch<H: Handler<Out>>(
                self,
                handler: H,
            ) -> $Builder<$U, (), DispatchNode<Chain, H>> {
                $Builder {
                    chain: DispatchNode {
                        prev: self.chain,
                        handler,
                    },
                    _marker: PhantomData,
                }
            }

            /// Conditionally wrap the output in `Option`.
            pub fn guard<Params, S: IntoRefStep<Out, bool, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Option<Out>, GuardNode<Chain, S::Step>> {
                $Builder {
                    chain: GuardNode {
                        prev: self.chain,
                        step: f.into_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Open a view scope. Steps inside operate on a read-only
            /// view constructed from the event. Close with `.end_view()`.
            pub fn view<V: crate::view::View<Out>>(
                self,
            ) -> crate::view::ViewScope<$U, Out, V, Chain, ()> {
                crate::view::ViewScope::new(self.chain)
            }

            /// Observe the current value without consuming or changing it.
            pub fn tap<Params, S: IntoRefStep<Out, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Out, TapNode<Chain, S::Step>> {
                $Builder {
                    chain: TapNode {
                        prev: self.chain,
                        step: f.into_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Binary conditional routing. Both arms borrow `&Out`.
            pub fn route<NewOut, C0, C1, Params, Pred: IntoRefStep<Out, bool, Params>>(
                self,
                pred: Pred,
                registry: &Registry,
                on_true: DagArm<Out, NewOut, C0>,
                on_false: DagArm<Out, NewOut, C1>,
            ) -> $Builder<$U, NewOut, DagRouteNode<Chain, Pred::Step, C0, C1, NewOut>>
            where
                C0: for<'a> ChainCall<&'a Out, Out = NewOut>,
                C1: for<'a> ChainCall<&'a Out, Out = NewOut>,
            {
                $Builder {
                    chain: DagRouteNode {
                        prev: self.chain,
                        pred: pred.into_ref_step(registry),
                        on_true: on_true.chain,
                        on_false: on_false.chain,
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Fork off a multi-step side-effect chain.
            pub fn tee<C>(self, side: DagArm<Out, (), C>) -> $Builder<$U, Out, TeeNode<Chain, C>>
            where
                C: for<'a> ChainCall<&'a Out, Out = ()>,
            {
                $Builder {
                    chain: TeeNode {
                        prev: self.chain,
                        side: side.chain,
                    },
                    _marker: PhantomData,
                }
            }

            /// Scan with persistent accumulator. The step receives
            /// `&mut Acc` and `&Out` by reference.
            pub fn scan<Acc, NewOut, Params, S>(
                self,
                initial: Acc,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, NewOut, RefScanNode<Chain, S::Step, Acc>>
            where
                Acc: 'static,
                NewOut: 'static,
                S: IntoRefScanStep<Acc, Out, NewOut, Params>,
            {
                $Builder {
                    chain: RefScanNode {
                        prev: self.chain,
                        step: f.into_ref_scan_step(registry),
                        acc: initial,
                    },
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Dedup — suppress unchanged values
        // =============================================================

        impl<$U, Out: PartialEq + Clone + 'static, Chain> $Builder<$U, Out, Chain> {
            /// Suppress consecutive unchanged values.
            pub fn dedup(self) -> $Builder<$U, Option<Out>, DedupNode<Chain, Out>> {
                $Builder {
                    chain: DedupNode {
                        prev: self.chain,
                        last: None,
                    },
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Bool combinators
        // =============================================================

        impl<$U, Chain> $Builder<$U, bool, Chain> {
            /// Invert a boolean value.
            #[allow(clippy::should_implement_trait)]
            pub fn not(self) -> $Builder<$U, bool, NotNode<Chain>> {
                $Builder {
                    chain: NotNode { prev: self.chain },
                    _marker: PhantomData,
                }
            }

            /// Short-circuit AND with a second boolean.
            pub fn and<Params, S: IntoProducer<bool, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, bool, AndBoolNode<Chain, S::Step>> {
                $Builder {
                    chain: AndBoolNode {
                        prev: self.chain,
                        producer: f.into_producer(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Short-circuit OR with a second boolean.
            pub fn or<Params, S: IntoProducer<bool, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, bool, OrBoolNode<Chain, S::Step>> {
                $Builder {
                    chain: OrBoolNode {
                        prev: self.chain,
                        producer: f.into_producer(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// XOR with a second boolean.
            pub fn xor<Params, S: IntoProducer<bool, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, bool, XorBoolNode<Chain, S::Step>> {
                $Builder {
                    chain: XorBoolNode {
                        prev: self.chain,
                        producer: f.into_producer(registry),
                    },
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Clone helpers — &T → T transitions
        // =============================================================

        impl<'a, $U, T: Clone, Chain> $Builder<$U, &'a T, Chain> {
            /// Clone a borrowed output to produce an owned value.
            pub fn cloned(self) -> $Builder<$U, T, ClonedNode<Chain>> {
                $Builder {
                    chain: ClonedNode { prev: self.chain },
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, $U, T: Clone, Chain> $Builder<$U, Option<&'a T>, Chain> {
            /// Clone inner borrowed value. `Option<&T>` → `Option<T>`.
            pub fn cloned(self) -> $Builder<$U, Option<T>, ClonedOptionNode<Chain>> {
                $Builder {
                    chain: ClonedOptionNode { prev: self.chain },
                    _marker: PhantomData,
                }
            }
        }

        impl<'a, $U, T: Clone, Err, Chain> $Builder<$U, Result<&'a T, Err>, Chain> {
            /// Clone inner borrowed Ok value.
            pub fn cloned(self) -> $Builder<$U, Result<T, Err>, ClonedResultNode<Chain>> {
                $Builder {
                    chain: ClonedResultNode { prev: self.chain },
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Option helpers
        // =============================================================

        impl<$U, T: 'static, Chain> $Builder<$U, Option<T>, Chain> {
            /// Transform the inner value. Step not called on None.
            pub fn map<U, Params, S: IntoStep<&'static T, U, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Option<U>, DagMapOptionNode<Chain, S::Step, U>>
            where
                U: 'static,
                S::Step: for<'x> StepCall<&'x T, Out = U>,
            {
                $Builder {
                    chain: DagMapOptionNode {
                        prev: self.chain,
                        step: f.into_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Short-circuits on None. std: `Option::and_then`
            pub fn and_then<U, Params, S: IntoStep<&'static T, Option<U>, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Option<U>, DagAndThenOptionNode<Chain, S::Step, U>>
            where
                U: 'static,
                S::Step: for<'x> StepCall<&'x T, Out = Option<U>>,
            {
                $Builder {
                    chain: DagAndThenOptionNode {
                        prev: self.chain,
                        step: f.into_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Side effect on None.
            pub fn on_none<Params, S: IntoProducer<(), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Option<T>, OnNoneNode<Chain, S::Step>> {
                $Builder {
                    chain: OnNoneNode {
                        prev: self.chain,
                        producer: f.into_producer(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Keep value if predicate holds. std: `Option::filter`
            pub fn filter<Params, S: IntoRefStep<T, bool, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Option<T>, FilterNode<Chain, S::Step>> {
                $Builder {
                    chain: FilterNode {
                        prev: self.chain,
                        step: f.into_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Side effect on Some value. std: `Option::inspect`
            pub fn inspect<Params, S: IntoRefStep<T, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Option<T>, InspectOptionNode<Chain, S::Step>> {
                $Builder {
                    chain: InspectOptionNode {
                        prev: self.chain,
                        step: f.into_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// None becomes Err(err). std: `Option::ok_or`
            pub fn ok_or<Err: Clone>(
                self,
                err: Err,
            ) -> $Builder<$U, Result<T, Err>, OkOrNode<Chain, Err>> {
                $Builder {
                    chain: OkOrNode {
                        prev: self.chain,
                        err,
                    },
                    _marker: PhantomData,
                }
            }

            /// None becomes Err(f()). std: `Option::ok_or_else`
            pub fn ok_or_else<Err, Params, S: IntoProducer<Err, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Result<T, Err>, OkOrElseNode<Chain, S::Step>> {
                $Builder {
                    chain: OkOrElseNode {
                        prev: self.chain,
                        producer: f.into_producer(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Exit Option — None becomes the default value.
            pub fn unwrap_or(self, default: T) -> $Builder<$U, T, UnwrapOrOptionNode<Chain, T>>
            where
                T: Clone,
            {
                $Builder {
                    chain: UnwrapOrOptionNode {
                        prev: self.chain,
                        default,
                    },
                    _marker: PhantomData,
                }
            }

            /// Exit Option — None becomes `f()`.
            pub fn unwrap_or_else<Params, S: IntoProducer<T, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, T, UnwrapOrElseOptionNode<Chain, S::Step>> {
                $Builder {
                    chain: UnwrapOrElseOptionNode {
                        prev: self.chain,
                        producer: f.into_producer(registry),
                    },
                    _marker: PhantomData,
                }
            }
        }

        // =============================================================
        // Result helpers
        // =============================================================

        impl<$U, T: 'static, Err: 'static, Chain> $Builder<$U, Result<T, Err>, Chain> {
            /// Transform the Ok value. Step not called on Err.
            pub fn map<U, Params, S: IntoStep<&'static T, U, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Result<U, Err>, DagMapResultNode<Chain, S::Step, U>>
            where
                U: 'static,
                S::Step: for<'x> StepCall<&'x T, Out = U>,
            {
                $Builder {
                    chain: DagMapResultNode {
                        prev: self.chain,
                        step: f.into_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Short-circuits on Err. std: `Result::and_then`
            pub fn and_then<U, Params, S: IntoStep<&'static T, Result<U, Err>, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Result<U, Err>, DagAndThenResultNode<Chain, S::Step, U>>
            where
                U: 'static,
                S::Step: for<'x> StepCall<&'x T, Out = Result<U, Err>>,
            {
                $Builder {
                    chain: DagAndThenResultNode {
                        prev: self.chain,
                        step: f.into_step(registry),
                        _out: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }

            /// Handle error and transition to Option.
            pub fn catch<Params, S: IntoStep<&'static Err, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Option<T>, DagCatchNode<Chain, S::Step>>
            where
                S::Step: for<'x> StepCall<&'x Err, Out = ()>,
            {
                $Builder {
                    chain: DagCatchNode {
                        prev: self.chain,
                        step: f.into_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Transform the error. std: `Result::map_err`
            pub fn map_err<Err2, Params, S: IntoStep<Err, Err2, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Result<T, Err2>, MapErrNode<Chain, S::Step>> {
                $Builder {
                    chain: MapErrNode {
                        prev: self.chain,
                        step: f.into_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Recover from Err. std: `Result::or_else`
            pub fn or_else<Err2, Params, S: IntoStep<Err, Result<T, Err2>, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Result<T, Err2>, OrElseNode<Chain, S::Step>> {
                $Builder {
                    chain: OrElseNode {
                        prev: self.chain,
                        step: f.into_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Side effect on Ok. std: `Result::inspect`
            pub fn inspect<Params, S: IntoRefStep<T, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Result<T, Err>, InspectResultNode<Chain, S::Step>> {
                $Builder {
                    chain: InspectResultNode {
                        prev: self.chain,
                        step: f.into_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Side effect on Err. std: `Result::inspect_err`
            pub fn inspect_err<Params, S: IntoRefStep<Err, (), Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, Result<T, Err>, InspectErrNode<Chain, S::Step>> {
                $Builder {
                    chain: InspectErrNode {
                        prev: self.chain,
                        step: f.into_ref_step(registry),
                    },
                    _marker: PhantomData,
                }
            }

            /// Discard error, enter Option land. std: `Result::ok`
            pub fn ok(self) -> $Builder<$U, Option<T>, OkResultNode<Chain>> {
                $Builder {
                    chain: OkResultNode { prev: self.chain },
                    _marker: PhantomData,
                }
            }

            /// Exit Result — Err becomes the default value.
            pub fn unwrap_or(self, default: T) -> $Builder<$U, T, UnwrapOrResultNode<Chain, T>>
            where
                T: Clone,
            {
                $Builder {
                    chain: UnwrapOrResultNode {
                        prev: self.chain,
                        default,
                    },
                    _marker: PhantomData,
                }
            }

            /// Exit Result — Err becomes `f(err)`.
            pub fn unwrap_or_else<Params, S: IntoStep<Err, T, Params>>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Builder<$U, T, UnwrapOrElseResultNode<Chain, S::Step>> {
                $Builder {
                    chain: UnwrapOrElseResultNode {
                        prev: self.chain,
                        step: f.into_step(registry),
                    },
                    _marker: PhantomData,
                }
            }
        }
    };
}

impl_dag_combinators!(builder: DagChain, upstream: E);
impl_dag_combinators!(builder: DagArm, upstream: In);

// =============================================================================
// Merge / Join named nodes — fork terminal nodes
// =============================================================================

/// Merge two fork arms into a single output via [`MergeStepCall`].
#[doc(hidden)]
pub struct MergeNode2<Chain, C0, C1, MS, ForkOut, A0, A1, MOut> {
    pub(crate) chain: Chain,
    pub(crate) arm0: C0,
    pub(crate) arm1: C1,
    pub(crate) merge: MS,
    pub(crate) _marker: PhantomData<fn(ForkOut) -> (A0, A1, MOut)>,
}

impl<In, Chain, C0, C1, MS, ForkOut, A0, A1, MOut> ChainCall<In>
    for MergeNode2<Chain, C0, C1, MS, ForkOut, A0, A1, MOut>
where
    ForkOut: 'static,
    A0: 'static,
    A1: 'static,
    Chain: ChainCall<In, Out = ForkOut>,
    C0: for<'a> ChainCall<&'a ForkOut, Out = A0>,
    C1: for<'a> ChainCall<&'a ForkOut, Out = A1>,
    MS: for<'x> MergeStepCall<(&'x A0, &'x A1), MOut>,
{
    type Out = MOut;

    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> MOut {
        let fork_out = self.chain.call(world, input);
        let o0 = self.arm0.call(world, &fork_out);
        let o1 = self.arm1.call(world, &fork_out);
        self.merge.call(world, (&o0, &o1))
    }
}

/// Merge three fork arms into a single output via [`MergeStepCall`].
#[doc(hidden)]
pub struct MergeNode3<Chain, C0, C1, C2, MS, ForkOut, A0, A1, A2, MOut> {
    pub(crate) chain: Chain,
    pub(crate) arm0: C0,
    pub(crate) arm1: C1,
    pub(crate) arm2: C2,
    pub(crate) merge: MS,
    pub(crate) _marker: PhantomData<fn(ForkOut) -> (A0, A1, A2, MOut)>,
}

impl<In, Chain, C0, C1, C2, MS, ForkOut, A0, A1, A2, MOut> ChainCall<In>
    for MergeNode3<Chain, C0, C1, C2, MS, ForkOut, A0, A1, A2, MOut>
where
    ForkOut: 'static,
    A0: 'static,
    A1: 'static,
    A2: 'static,
    Chain: ChainCall<In, Out = ForkOut>,
    C0: for<'a> ChainCall<&'a ForkOut, Out = A0>,
    C1: for<'a> ChainCall<&'a ForkOut, Out = A1>,
    C2: for<'a> ChainCall<&'a ForkOut, Out = A2>,
    MS: for<'x> MergeStepCall<(&'x A0, &'x A1, &'x A2), MOut>,
{
    type Out = MOut;

    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> MOut {
        let fork_out = self.chain.call(world, input);
        let o0 = self.arm0.call(world, &fork_out);
        let o1 = self.arm1.call(world, &fork_out);
        let o2 = self.arm2.call(world, &fork_out);
        self.merge.call(world, (&o0, &o1, &o2))
    }
}

/// Merge four fork arms into a single output via [`MergeStepCall`].
#[doc(hidden)]
pub struct MergeNode4<Chain, C0, C1, C2, C3, MS, ForkOut, A0, A1, A2, A3, MOut> {
    pub(crate) chain: Chain,
    pub(crate) arm0: C0,
    pub(crate) arm1: C1,
    pub(crate) arm2: C2,
    pub(crate) arm3: C3,
    pub(crate) merge: MS,
    pub(crate) _marker: PhantomData<fn(ForkOut) -> (A0, A1, A2, A3, MOut)>,
}

#[allow(clippy::many_single_char_names)]
impl<In, Chain, C0, C1, C2, C3, MS, ForkOut, A0, A1, A2, A3, MOut> ChainCall<In>
    for MergeNode4<Chain, C0, C1, C2, C3, MS, ForkOut, A0, A1, A2, A3, MOut>
where
    ForkOut: 'static,
    A0: 'static,
    A1: 'static,
    A2: 'static,
    A3: 'static,
    Chain: ChainCall<In, Out = ForkOut>,
    C0: for<'a> ChainCall<&'a ForkOut, Out = A0>,
    C1: for<'a> ChainCall<&'a ForkOut, Out = A1>,
    C2: for<'a> ChainCall<&'a ForkOut, Out = A2>,
    C3: for<'a> ChainCall<&'a ForkOut, Out = A3>,
    MS: for<'x> MergeStepCall<(&'x A0, &'x A1, &'x A2, &'x A3), MOut>,
{
    type Out = MOut;

    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> MOut {
        let fork_out = self.chain.call(world, input);
        let o0 = self.arm0.call(world, &fork_out);
        let o1 = self.arm1.call(world, &fork_out);
        let o2 = self.arm2.call(world, &fork_out);
        let o3 = self.arm3.call(world, &fork_out);
        self.merge.call(world, (&o0, &o1, &o2, &o3))
    }
}

/// Join two fork arms (all producing `()`).
#[doc(hidden)]
pub struct JoinNode2<Chain, C0, C1, ForkOut> {
    pub(crate) chain: Chain,
    pub(crate) arm0: C0,
    pub(crate) arm1: C1,
    pub(crate) _marker: PhantomData<fn() -> ForkOut>,
}

impl<In, Chain, C0, C1, ForkOut> ChainCall<In> for JoinNode2<Chain, C0, C1, ForkOut>
where
    ForkOut: 'static,
    Chain: ChainCall<In, Out = ForkOut>,
    C0: for<'a> ChainCall<&'a ForkOut, Out = ()>,
    C1: for<'a> ChainCall<&'a ForkOut, Out = ()>,
{
    type Out = ();

    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) {
        let fork_out = self.chain.call(world, input);
        self.arm0.call(world, &fork_out);
        self.arm1.call(world, &fork_out);
    }
}

/// Join three fork arms (all producing `()`).
#[doc(hidden)]
pub struct JoinNode3<Chain, C0, C1, C2, ForkOut> {
    pub(crate) chain: Chain,
    pub(crate) arm0: C0,
    pub(crate) arm1: C1,
    pub(crate) arm2: C2,
    pub(crate) _marker: PhantomData<fn() -> ForkOut>,
}

impl<In, Chain, C0, C1, C2, ForkOut> ChainCall<In> for JoinNode3<Chain, C0, C1, C2, ForkOut>
where
    ForkOut: 'static,
    Chain: ChainCall<In, Out = ForkOut>,
    C0: for<'a> ChainCall<&'a ForkOut, Out = ()>,
    C1: for<'a> ChainCall<&'a ForkOut, Out = ()>,
    C2: for<'a> ChainCall<&'a ForkOut, Out = ()>,
{
    type Out = ();

    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) {
        let fork_out = self.chain.call(world, input);
        self.arm0.call(world, &fork_out);
        self.arm1.call(world, &fork_out);
        self.arm2.call(world, &fork_out);
    }
}

/// Join four fork arms (all producing `()`).
#[doc(hidden)]
pub struct JoinNode4<Chain, C0, C1, C2, C3, ForkOut> {
    pub(crate) chain: Chain,
    pub(crate) arm0: C0,
    pub(crate) arm1: C1,
    pub(crate) arm2: C2,
    pub(crate) arm3: C3,
    pub(crate) _marker: PhantomData<fn() -> ForkOut>,
}

#[allow(clippy::many_single_char_names)]
impl<In, Chain, C0, C1, C2, C3, ForkOut> ChainCall<In> for JoinNode4<Chain, C0, C1, C2, C3, ForkOut>
where
    ForkOut: 'static,
    Chain: ChainCall<In, Out = ForkOut>,
    C0: for<'a> ChainCall<&'a ForkOut, Out = ()>,
    C1: for<'a> ChainCall<&'a ForkOut, Out = ()>,
    C2: for<'a> ChainCall<&'a ForkOut, Out = ()>,
    C3: for<'a> ChainCall<&'a ForkOut, Out = ()>,
{
    type Out = ();

    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) {
        let fork_out = self.chain.call(world, input);
        self.arm0.call(world, &fork_out);
        self.arm1.call(world, &fork_out);
        self.arm2.call(world, &fork_out);
        self.arm3.call(world, &fork_out);
    }
}

// =============================================================================
// Splat — tuple destructuring into individual reference arguments (DAG)
// =============================================================================
//
// DAG splat reuses IntoMergeStep/MergeStepCall since DAG steps take inputs
// by reference — the function signature is the same as a merge step:
// `fn(Params..., &A, &B) -> Out`.
//
// Builder types are `#[doc(hidden)]` — users only see `.splat().then()`.

macro_rules! define_dag_splat_builders {
    (
        $N:literal,
        chain: $SplatChain:ident,
        arm: $SplatArm:ident,
        arm_start: $SplatArmStart:ident,
        splat_then: $SplatThenNode:ident,
        splat_arm_start: $SplatArmStartNode:ident,
        ($($T:ident),+),
        ($($idx:tt),+)
    ) => {
        // -- Named node: splat + step on upstream chain --

        #[doc(hidden)]
        pub struct $SplatThenNode<Chain, MS, $($T,)+ NewOut> {
            pub(crate) chain: Chain,
            pub(crate) merge: MS,
            pub(crate) _marker: PhantomData<fn() -> ($($T,)+ NewOut)>,
        }

        impl<In, Chain, MS, $($T: 'static,)+ NewOut> ChainCall<In>
            for $SplatThenNode<Chain, MS, $($T,)+ NewOut>
        where
            Chain: ChainCall<In, Out = ($($T,)+)>,
            MS: for<'x> MergeStepCall<($(&'x $T,)+), NewOut>,
        {
            type Out = NewOut;

            #[inline(always)]
            fn call(&mut self, world: &mut World, input: In) -> NewOut {
                let tuple = self.chain.call(world, input);
                self.merge.call(world, ($(&tuple.$idx,)+))
            }
        }

        // -- Named node: splat at arm start (no upstream chain) --

        #[doc(hidden)]
        pub struct $SplatArmStartNode<MS, $($T,)+ Out> {
            pub(crate) merge: MS,
            pub(crate) _marker: PhantomData<fn() -> ($($T,)+ Out)>,
        }

        impl<'inp, $($T: 'static,)+ MS, Out> ChainCall<&'inp ($($T,)+)>
            for $SplatArmStartNode<MS, $($T,)+ Out>
        where
            MS: for<'x> MergeStepCall<($(&'x $T,)+), Out>,
        {
            type Out = Out;

            #[inline(always)]
            fn call(&mut self, world: &mut World, input: &($($T,)+)) -> Out {
                self.merge.call(world, ($(&input.$idx,)+))
            }
        }

        // -- Splat builder on main chain --

        /// DAG splat builder on the main chain.
        #[doc(hidden)]
        pub struct $SplatChain<E, $($T,)+ Chain> {
            chain: Chain,
            _marker: PhantomData<fn(E) -> ($($T,)+)>,
        }

        impl<E, $($T: 'static,)+ Chain> $SplatChain<E, $($T,)+ Chain> {
            /// Add a step that receives the tuple elements as individual `&T` arguments.
            pub fn then<NewOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> DagChain<E, NewOut, $SplatThenNode<Chain, S::Step, $($T,)+ NewOut>>
            where
                NewOut: 'static,
                S: IntoMergeStep<($(&'static $T,)+), NewOut, Params>,
                S::Step: for<'x> MergeStepCall<($(&'x $T,)+), NewOut>,
            {
                DagChain {
                    chain: $SplatThenNode {
                        chain: self.chain,
                        merge: f.into_merge_step(registry),
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<E, $($T: 'static,)+ Chain> DagChain<E, ($($T,)+), Chain> {
            /// Destructure the tuple output into individual `&T` arguments.
            pub fn splat(self) -> $SplatChain<E, $($T,)+ Chain> {
                $SplatChain {
                    chain: self.chain,
                    _marker: PhantomData,
                }
            }
        }

        // -- Splat builder within an arm --

        /// DAG splat builder within an arm.
        #[doc(hidden)]
        pub struct $SplatArm<In, $($T,)+ Chain> {
            chain: Chain,
            _marker: PhantomData<fn(*const In) -> ($($T,)+)>,
        }

        impl<In: 'static, $($T: 'static,)+ Chain> $SplatArm<In, $($T,)+ Chain> {
            /// Add a step that receives the tuple elements as individual `&T` arguments.
            pub fn then<NewOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> DagArm<In, NewOut, $SplatThenNode<Chain, S::Step, $($T,)+ NewOut>>
            where
                NewOut: 'static,
                S: IntoMergeStep<($(&'static $T,)+), NewOut, Params>,
                S::Step: for<'x> MergeStepCall<($(&'x $T,)+), NewOut>,
            {
                DagArm {
                    chain: $SplatThenNode {
                        chain: self.chain,
                        merge: f.into_merge_step(registry),
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<In: 'static, $($T: 'static,)+ Chain> DagArm<In, ($($T,)+), Chain> {
            /// Destructure the tuple output into individual `&T` arguments.
            pub fn splat(self) -> $SplatArm<In, $($T,)+ Chain> {
                $SplatArm {
                    chain: self.chain,
                    _marker: PhantomData,
                }
            }
        }

        // -- Splat at arm start position --

        /// DAG splat builder at arm start position.
        #[doc(hidden)]
        pub struct $SplatArmStart<$($T),+>(PhantomData<fn(($($T,)+))>);

        impl<$($T: 'static),+> $SplatArmStart<$($T),+> {
            /// Add a step that receives the tuple elements as individual `&T` arguments.
            pub fn then<Out, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> DagArm<($($T,)+), Out, $SplatArmStartNode<S::Step, $($T,)+ Out>>
            where
                Out: 'static,
                S: IntoMergeStep<($(&'static $T,)+), Out, Params>,
                S::Step: for<'x> MergeStepCall<($(&'x $T,)+), Out>,
            {
                DagArm {
                    chain: $SplatArmStartNode {
                        merge: f.into_merge_step(registry),
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<$($T: 'static),+> DagArmSeed<($($T,)+)> {
            /// Destructure the tuple input into individual `&T` arguments.
            pub fn splat(self) -> $SplatArmStart<$($T),+> {
                $SplatArmStart(PhantomData)
            }
        }
    };
}

define_dag_splat_builders!(2,
    chain: DagSplatChain2,
    arm: DagSplatArm2,
    arm_start: DagSplatArmStart2,
    splat_then: SplatThenNode2,
    splat_arm_start: SplatArmStartNode2,
    (T0, T1),
    (0, 1)
);

define_dag_splat_builders!(3,
    chain: DagSplatChain3,
    arm: DagSplatArm3,
    arm_start: DagSplatArmStart3,
    splat_then: SplatThenNode3,
    splat_arm_start: SplatArmStartNode3,
    (T0, T1, T2),
    (0, 1, 2)
);

define_dag_splat_builders!(4,
    chain: DagSplatChain4,
    arm: DagSplatArm4,
    arm_start: DagSplatArmStart4,
    splat_then: SplatThenNode4,
    splat_arm_start: SplatArmStartNode4,
    (T0, T1, T2, T3),
    (0, 1, 2, 3)
);

define_dag_splat_builders!(5,
    chain: DagSplatChain5,
    arm: DagSplatArm5,
    arm_start: DagSplatArmStart5,
    splat_then: SplatThenNode5,
    splat_arm_start: SplatArmStartNode5,
    (T0, T1, T2, T3, T4),
    (0, 1, 2, 3, 4)
);

// =============================================================================
// Fork arity macro — arm accumulation, merge, join
// =============================================================================

/// Generates arm accumulation, merge, and join for a fork type.
///
/// ChainFork and ArmFork differ only in what output builder they
/// produce (DagChain vs DagArm). All dispatch logic lives in the
/// named MergeNode/JoinNode types — the macro just wires construction.
macro_rules! impl_dag_fork {
    (
        fork: $Fork:ident,
        output: $Output:ident,
        upstream: $U:ident
    ) => {
        // =============================================================
        // Arm accumulation: 0→1, 1→2, 2→3, 3→4
        // =============================================================

        impl<$U, ForkOut, Chain> $Fork<$U, ForkOut, Chain, ()> {
            /// Add the first arm to this fork.
            pub fn arm<AOut, ACh>(
                self,
                f: impl FnOnce(DagArmSeed<ForkOut>) -> DagArm<ForkOut, AOut, ACh>,
            ) -> $Fork<$U, ForkOut, Chain, (DagArm<ForkOut, AOut, ACh>,)> {
                let arm = f(DagArmSeed(PhantomData));
                $Fork {
                    chain: self.chain,
                    arms: (arm,),
                    _marker: PhantomData,
                }
            }
        }

        impl<$U, ForkOut, Chain, A0, C0> $Fork<$U, ForkOut, Chain, (DagArm<ForkOut, A0, C0>,)> {
            /// Add a second arm to this fork.
            pub fn arm<AOut, ACh>(
                self,
                f: impl FnOnce(DagArmSeed<ForkOut>) -> DagArm<ForkOut, AOut, ACh>,
            ) -> $Fork<$U, ForkOut, Chain, (DagArm<ForkOut, A0, C0>, DagArm<ForkOut, AOut, ACh>)>
            {
                let arm = f(DagArmSeed(PhantomData));
                let (a0,) = self.arms;
                $Fork {
                    chain: self.chain,
                    arms: (a0, arm),
                    _marker: PhantomData,
                }
            }
        }

        impl<$U, ForkOut, Chain, A0, C0, A1, C1>
            $Fork<$U, ForkOut, Chain, (DagArm<ForkOut, A0, C0>, DagArm<ForkOut, A1, C1>)>
        {
            /// Add a third arm to this fork.
            pub fn arm<AOut, ACh>(
                self,
                f: impl FnOnce(DagArmSeed<ForkOut>) -> DagArm<ForkOut, AOut, ACh>,
            ) -> $Fork<
                $U,
                ForkOut,
                Chain,
                (
                    DagArm<ForkOut, A0, C0>,
                    DagArm<ForkOut, A1, C1>,
                    DagArm<ForkOut, AOut, ACh>,
                ),
            > {
                let arm = f(DagArmSeed(PhantomData));
                let (a0, a1) = self.arms;
                $Fork {
                    chain: self.chain,
                    arms: (a0, a1, arm),
                    _marker: PhantomData,
                }
            }
        }

        impl<$U, ForkOut, Chain, A0, C0, A1, C1, A2, C2>
            $Fork<
                $U,
                ForkOut,
                Chain,
                (
                    DagArm<ForkOut, A0, C0>,
                    DagArm<ForkOut, A1, C1>,
                    DagArm<ForkOut, A2, C2>,
                ),
            >
        {
            /// Add a fourth arm to this fork.
            pub fn arm<AOut, ACh>(
                self,
                f: impl FnOnce(DagArmSeed<ForkOut>) -> DagArm<ForkOut, AOut, ACh>,
            ) -> $Fork<
                $U,
                ForkOut,
                Chain,
                (
                    DagArm<ForkOut, A0, C0>,
                    DagArm<ForkOut, A1, C1>,
                    DagArm<ForkOut, A2, C2>,
                    DagArm<ForkOut, AOut, ACh>,
                ),
            > {
                let arm = f(DagArmSeed(PhantomData));
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

        impl<$U, ForkOut: 'static, Chain, A0: 'static, C0, A1: 'static, C1>
            $Fork<$U, ForkOut, Chain, (DagArm<ForkOut, A0, C0>, DagArm<ForkOut, A1, C1>)>
        {
            /// Merge two arms with a merge step.
            pub fn merge<MOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Output<
                $U,
                MOut,
                MergeNode2<Chain, C0, C1, S::Step, ForkOut, A0, A1, MOut>,
            >
            where
                MOut: 'static,
                S: IntoMergeStep<(&'static A0, &'static A1), MOut, Params>,
                S::Step: for<'x> MergeStepCall<(&'x A0, &'x A1), MOut>,
            {
                let (a0, a1) = self.arms;
                $Output {
                    chain: MergeNode2 {
                        chain: self.chain,
                        arm0: a0.chain,
                        arm1: a1.chain,
                        merge: f.into_merge_step(registry),
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<$U, ForkOut: 'static, Chain, C0, C1>
            $Fork<$U, ForkOut, Chain, (DagArm<ForkOut, (), C0>, DagArm<ForkOut, (), C1>)>
        {
            /// Join two sink arms (all producing `()`).
            pub fn join(
                self,
            ) -> $Output<$U, (), JoinNode2<Chain, C0, C1, ForkOut>> {
                let (a0, a1) = self.arms;
                $Output {
                    chain: JoinNode2 {
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

        impl<$U, ForkOut: 'static, Chain, A0: 'static, C0, A1: 'static, C1, A2: 'static, C2>
            $Fork<
                $U,
                ForkOut,
                Chain,
                (
                    DagArm<ForkOut, A0, C0>,
                    DagArm<ForkOut, A1, C1>,
                    DagArm<ForkOut, A2, C2>,
                ),
            >
        {
            /// Merge three arms with a merge step.
            pub fn merge<MOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Output<
                $U,
                MOut,
                MergeNode3<Chain, C0, C1, C2, S::Step, ForkOut, A0, A1, A2, MOut>,
            >
            where
                MOut: 'static,
                S: IntoMergeStep<(&'static A0, &'static A1, &'static A2), MOut, Params>,
                S::Step: for<'x> MergeStepCall<(&'x A0, &'x A1, &'x A2), MOut>,
            {
                let (a0, a1, a2) = self.arms;
                $Output {
                    chain: MergeNode3 {
                        chain: self.chain,
                        arm0: a0.chain,
                        arm1: a1.chain,
                        arm2: a2.chain,
                        merge: f.into_merge_step(registry),
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<$U, ForkOut: 'static, Chain, C0, C1, C2>
            $Fork<
                $U,
                ForkOut,
                Chain,
                (
                    DagArm<ForkOut, (), C0>,
                    DagArm<ForkOut, (), C1>,
                    DagArm<ForkOut, (), C2>,
                ),
            >
        {
            /// Join three sink arms (all producing `()`).
            pub fn join(
                self,
            ) -> $Output<$U, (), JoinNode3<Chain, C0, C1, C2, ForkOut>> {
                let (a0, a1, a2) = self.arms;
                $Output {
                    chain: JoinNode3 {
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
                $U,
                ForkOut,
                Chain,
                (
                    DagArm<ForkOut, A0, C0>,
                    DagArm<ForkOut, A1, C1>,
                    DagArm<ForkOut, A2, C2>,
                    DagArm<ForkOut, A3, C3>,
                ),
            >
        {
            /// Merge four arms with a merge step.
            pub fn merge<MOut, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> $Output<
                $U,
                MOut,
                MergeNode4<Chain, C0, C1, C2, C3, S::Step, ForkOut, A0, A1, A2, A3, MOut>,
            >
            where
                MOut: 'static,
                S: IntoMergeStep<
                    (&'static A0, &'static A1, &'static A2, &'static A3),
                    MOut,
                    Params,
                >,
                S::Step: for<'x> MergeStepCall<(&'x A0, &'x A1, &'x A2, &'x A3), MOut>,
            {
                let (a0, a1, a2, a3) = self.arms;
                $Output {
                    chain: MergeNode4 {
                        chain: self.chain,
                        arm0: a0.chain,
                        arm1: a1.chain,
                        arm2: a2.chain,
                        arm3: a3.chain,
                        merge: f.into_merge_step(registry),
                        _marker: PhantomData,
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<$U, ForkOut: 'static, Chain, C0, C1, C2, C3>
            $Fork<
                $U,
                ForkOut,
                Chain,
                (
                    DagArm<ForkOut, (), C0>,
                    DagArm<ForkOut, (), C1>,
                    DagArm<ForkOut, (), C2>,
                    DagArm<ForkOut, (), C3>,
                ),
            >
        {
            /// Join four sink arms (all producing `()`).
            pub fn join(
                self,
            ) -> $Output<$U, (), JoinNode4<Chain, C0, C1, C2, C3, ForkOut>> {
                let (a0, a1, a2, a3) = self.arms;
                $Output {
                    chain: JoinNode4 {
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

impl_dag_fork!(fork: DagChainFork, output: DagChain, upstream: E);
impl_dag_fork!(fork: DagArmFork, output: DagArm, upstream: In);

// =============================================================================
// build_batch — when Out: PipelineOutput (() or Option<()>)
// =============================================================================

impl<E, Out: crate::PipelineOutput, Chain: ChainCall<E, Out = Out>> DagChain<E, Out, Chain> {
    /// Finalize into a [`BatchDag`] with a pre-allocated input buffer.
    ///
    /// Same DAG chain as [`build`](DagChain::build), but the DAG owns an
    /// input buffer that drivers fill between dispatch cycles. Each call
    /// to [`BatchDag::run`] drains the buffer, running every item through
    /// the chain independently.
    ///
    /// Available when the DAG ends with `()` or `Option<()>` (e.g.
    /// after `.guard()` or `.filter()` followed by `.unwrap_or(())`).
    ///
    /// `capacity` is the initial allocation — the buffer can grow if needed,
    /// but sizing it for the expected batch size avoids reallocation.
    #[must_use = "building a DAG without storing it does nothing"]
    pub fn build_batch(self, capacity: usize) -> BatchDag<E, Chain> {
        BatchDag {
            input: Vec::with_capacity(capacity),
            chain: self.chain,
        }
    }
}

// =============================================================================
// BatchDag<E, F> — DAG with owned input buffer
// =============================================================================

/// Batch DAG that owns a pre-allocated input buffer.
///
/// Created by [`DagChain::build_batch`]. Each item flows through the
/// full DAG chain independently — the same per-item `Option` and
/// `Result` flow control as [`Dag`]. Errors are handled inline (via
/// `.catch()`, `.unwrap_or()`, etc.) and the batch continues to the
/// next item.
///
/// Unlike [`Dag`], `BatchDag` does not implement [`Handler`] — it is
/// driven directly by the owner via [`run()`](BatchDag::run).
///
/// # Examples
///
/// ```
/// use nexus_rt::{WorldBuilder, ResMut, Resource};
/// use nexus_rt::dag::DagBuilder;
///
/// #[derive(Resource)]
/// struct Accum(u64);
///
/// let mut wb = WorldBuilder::new();
/// wb.register(Accum(0));
/// let mut world = wb.build();
/// let reg = world.registry();
///
/// fn double(x: u32) -> u64 { x as u64 * 2 }
/// fn store(mut out: ResMut<Accum>, val: &u64) { out.0 += *val; }
///
/// let mut batch = DagBuilder::<u32>::new()
///     .root(double, reg)
///     .then(store, reg)
///     .build_batch(8);
///
/// batch.input_mut().extend([1, 2, 3]);
/// batch.run(&mut world);
///
/// assert_eq!(world.resource::<Accum>().0, 12); // 2 + 4 + 6
/// assert!(batch.input().is_empty());
/// ```
pub struct BatchDag<E, F> {
    input: Vec<E>,
    chain: F,
}

impl<E, Out: crate::PipelineOutput, F: ChainCall<E, Out = Out>> BatchDag<E, F> {
    /// Mutable access to the input buffer. Drivers fill this between
    /// dispatch cycles.
    pub fn input_mut(&mut self) -> &mut Vec<E> {
        &mut self.input
    }

    /// Read-only access to the input buffer.
    pub fn input(&self) -> &[E] {
        &self.input
    }

    /// Drain the input buffer, running each item through the DAG.
    ///
    /// Each item gets independent `Option`/`Result` flow control — an
    /// error on one item does not affect subsequent items. After `run()`,
    /// the input buffer is empty but retains its allocation.
    pub fn run(&mut self, world: &mut World) {
        for item in self.input.drain(..) {
            let _ = self.chain.call(world, item);
        }
    }
}

// =============================================================================
// resolve_arm — pre-resolve a step for manual dispatch
// =============================================================================

/// Resolve a step for use in manual dispatch (e.g. inside an
/// opaque `.then()` closure).
///
/// Returns a closure with pre-resolved [`Param`](crate::Param) state —
/// the same build-time resolution that `.then()` performs, but as a
/// standalone value the caller can invoke from any context.
///
/// # Examples
///
/// ```ignore
/// let mut arm0 = resolve_arm(handle_new, reg);
/// let mut arm1 = resolve_arm(handle_cancel, reg);
///
/// dag.then(move |world: &mut World, msg: &Decoded| match msg.kind {
///     MsgKind::NewOrder => arm0(world, msg),
///     MsgKind::Cancel   => arm1(world, msg),
/// }, reg)
/// ```
pub fn resolve_arm<In, Out, Params, S>(
    f: S,
    registry: &Registry,
) -> impl FnMut(&mut World, &In) -> Out + use<In, Out, Params, S>
where
    In: 'static,
    Out: 'static,
    S: IntoStep<&'static In, Out, Params>,
    S::Step: for<'a> StepCall<&'a In, Out = Out>,
{
    let mut resolved = f.into_step(registry);
    move |world: &mut World, input: &In| resolved.call(world, input)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[allow(
    clippy::ref_option,
    clippy::unnecessary_wraps,
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref,
    clippy::ptr_arg
)]
mod tests {
    use super::*;
    use crate::{IntoHandler, Res, ResMut, Virtual, WorldBuilder};

    // -- Linear chains --

    #[test]
    fn dag_linear_2() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_mul2(x: u32) -> u64 {
            x as u64 * 2
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(root_mul2, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 10);
    }

    #[test]
    fn dag_linear_3() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_mul2(x: u32) -> u64 {
            x as u64 * 2
        }
        fn add_one(val: &u64) -> u64 {
            *val + 1
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(root_mul2, reg)
            .then(add_one, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 11); // (5*2)+1
    }

    #[test]
    fn dag_linear_5() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_id(x: u32) -> u64 {
            x as u64
        }
        fn add_one(val: &u64) -> u64 {
            *val + 1
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(root_id, reg)
            .then(add_one, reg)
            .then(add_one, reg)
            .then(add_one, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 3); // 0+1+1+1
    }

    // -- Diamond: root → [a, b] → merge → sink --

    #[test]
    fn dag_diamond() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_mul2(x: u32) -> u32 {
            x.wrapping_mul(2)
        }
        fn add_one(val: &u32) -> u32 {
            val.wrapping_add(1)
        }
        fn mul3(val: &u32) -> u32 {
            val.wrapping_mul(3)
        }
        fn merge_add(a: &u32, b: &u32) -> u32 {
            a.wrapping_add(*b)
        }
        fn store(mut out: ResMut<u64>, val: &u32) {
            *out = *val as u64;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(root_mul2, reg)
            .fork()
            .arm(|a| a.then(add_one, reg))
            .arm(|b| b.then(mul3, reg))
            .merge(merge_add, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 5u32);
        // root: 10, arm_a: 11, arm_b: 30, merge: 41
        assert_eq!(*world.resource::<u64>(), 41);
    }

    // -- Fan-out to sinks (.join()) --

    #[test]
    fn dag_fan_out_join() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<i64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_id(x: u32) -> u64 {
            x as u64
        }
        fn sink_u64(mut out: ResMut<u64>, val: &u64) {
            *out = *val * 2;
        }
        fn sink_i64(mut out: ResMut<i64>, val: &u64) {
            *out = *val as i64 * 3;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(root_id, reg)
            .fork()
            .arm(|a| a.then(sink_u64, reg))
            .arm(|b| b.then(sink_i64, reg))
            .join()
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 10);
        assert_eq!(*world.resource::<i64>(), 15);
    }

    // -- Nested fork within an arm --

    #[test]
    fn dag_nested_fork() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_id(x: u32) -> u32 {
            x
        }
        fn add_10(val: &u32) -> u32 {
            val.wrapping_add(10)
        }
        fn mul2(val: &u32) -> u32 {
            val.wrapping_mul(2)
        }
        fn mul3(val: &u32) -> u32 {
            val.wrapping_mul(3)
        }
        fn inner_merge(a: &u32, b: &u32) -> u32 {
            a.wrapping_add(*b)
        }
        fn outer_merge(a: &u32, b: &u32) -> u32 {
            a.wrapping_add(*b)
        }
        fn store(mut out: ResMut<u64>, val: &u32) {
            *out = *val as u64;
        }

        // root(5)=5 → fork
        //   arm_a: add_10(5)=15 → fork
        //     sub_c: mul2(15)=30
        //     sub_d: mul3(15)=45
        //     inner_merge(30,45)=75
        //   arm_b: mul3(5)=15
        // outer_merge(75,15)=90
        let mut dag = DagBuilder::<u32>::new()
            .root(root_id, reg)
            .fork()
            .arm(|a| {
                a.then(add_10, reg)
                    .fork()
                    .arm(|c| c.then(mul2, reg))
                    .arm(|d| d.then(mul3, reg))
                    .merge(inner_merge, reg)
            })
            .arm(|b| b.then(mul3, reg))
            .merge(outer_merge, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 90);
    }

    // -- Complex topology: asymmetric arm lengths --

    #[test]
    fn dag_complex_topology() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_mul2(x: u32) -> u32 {
            x.wrapping_mul(2)
        }
        fn add_one(val: &u32) -> u32 {
            val.wrapping_add(1)
        }
        fn add_then_mul2(val: &u32) -> u32 {
            val.wrapping_add(1).wrapping_mul(2)
        }
        fn mul3(val: &u32) -> u32 {
            val.wrapping_mul(3)
        }
        fn merge_add(a: &u32, b: &u32) -> u32 {
            a.wrapping_add(*b)
        }
        fn store(mut out: ResMut<u64>, val: &u32) {
            *out = *val as u64;
        }

        // root(5)=10 → fork
        //   a: add_one(10)=11 → add_then_mul2(11)=24
        //   b: mul3(10)=30
        // merge(24, 30) = 54
        let mut dag = DagBuilder::<u32>::new()
            .root(root_mul2, reg)
            .fork()
            .arm(|a| a.then(add_one, reg).then(add_then_mul2, reg))
            .arm(|b| b.then(mul3, reg))
            .merge(merge_add, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 54);
    }

    // -- Boxable into Box<dyn Handler<E>> --

    #[test]
    fn dag_boxable() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_id(x: u32) -> u64 {
            x as u64
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut boxed: Virtual<u32> = Box::new(
            DagBuilder::<u32>::new()
                .root(root_id, reg)
                .then(store, reg)
                .build(),
        );
        boxed.run(&mut world, 77u32);
        assert_eq!(*world.resource::<u64>(), 77);
    }

    // -- World access (Res<T>, ResMut<T>) in nodes --

    #[test]
    fn dag_world_access() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10); // factor
        wb.register::<String>(String::new());
        let mut world = wb.build();
        let reg = world.registry();

        fn scale(factor: Res<u64>, val: &u32) -> u64 {
            *factor * (*val as u64)
        }
        fn store(mut out: ResMut<String>, val: &u64) {
            *out = val.to_string();
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(|x: u32| x, reg)
            .then(scale, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 7u32);
        assert_eq!(world.resource::<String>().as_str(), "70");
    }

    // -- Root-only (terminal root outputting ()) --

    #[test]
    fn dag_root_only() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(
                |mut out: ResMut<u64>, x: u32| {
                    *out = x as u64;
                },
                reg,
            )
            .build();

        dag.run(&mut world, 42u32);
        assert_eq!(*world.resource::<u64>(), 42);
    }

    // -- Multiple dispatches reuse state --

    #[test]
    fn dag_multiple_dispatches() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_id(x: u32) -> u64 {
            x as u64
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(root_id, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 1u32);
        assert_eq!(*world.resource::<u64>(), 1);
        dag.run(&mut world, 2u32);
        assert_eq!(*world.resource::<u64>(), 2);
        dag.run(&mut world, 3u32);
        assert_eq!(*world.resource::<u64>(), 3);
    }

    // -- 3-way merge --

    #[test]
    fn dag_3way_merge() {
        let mut wb = WorldBuilder::new();
        wb.register::<String>(String::new());
        let mut world = wb.build();
        let reg = world.registry();

        fn root_id(x: u32) -> u64 {
            x as u64
        }
        fn mul1(val: &u64) -> u64 {
            *val
        }
        fn mul2(val: &u64) -> u64 {
            *val * 2
        }
        fn mul3(val: &u64) -> u64 {
            *val * 3
        }
        fn merge3_fmt(mut out: ResMut<String>, a: &u64, b: &u64, c: &u64) {
            *out = format!("{},{},{}", a, b, c);
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(root_id, reg)
            .fork()
            .arm(|a| a.then(mul1, reg))
            .arm(|b| b.then(mul2, reg))
            .arm(|c| c.then(mul3, reg))
            .merge(merge3_fmt, reg)
            .build();

        dag.run(&mut world, 10u32);
        assert_eq!(world.resource::<String>().as_str(), "10,20,30");
    }

    // -- DAG combinators --

    #[test]
    fn dag_dispatch() {
        fn root(x: u32) -> u64 {
            x as u64 + 42
        }
        fn sink(mut out: ResMut<u64>, event: u64) {
            *out = event;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .dispatch(sink.into_handler(reg))
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 42);
    }

    #[test]
    fn dag_option_map() {
        fn root(_x: u32) -> Option<u64> {
            Some(10)
        }
        fn double(val: &u64) -> u64 {
            *val * 2
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .map(double, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 20);
    }

    #[test]
    fn dag_option_map_none() {
        fn root(_x: u32) -> Option<u64> {
            None
        }
        fn double(val: &u64) -> u64 {
            *val * 2
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(999);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .map(double, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 999);
    }

    #[test]
    fn dag_option_and_then() {
        fn root(_x: u32) -> Option<u64> {
            Some(5)
        }
        fn check(val: &u64) -> Option<u64> {
            if *val > 3 { Some(*val * 10) } else { None }
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .and_then(check, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 50);
    }

    #[test]
    fn dag_option_filter_keeps() {
        fn root(_x: u32) -> Option<u64> {
            Some(5)
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, world.registry())
            .filter(|v: &u64| *v > 3, world.registry())
            .then(sink, world.registry())
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 5);
    }

    #[test]
    fn dag_option_filter_drops() {
        fn root(_x: u32) -> Option<u64> {
            Some(5)
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, world.registry())
            .filter(|v: &u64| *v > 10, world.registry())
            .then(sink, world.registry())
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 0);
    }

    #[test]
    fn dag_option_on_none() {
        fn root(_x: u32) -> Option<u64> {
            None
        }
        fn sink(_val: &Option<u64>) {}
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(false);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .on_none(
                |w: &mut World| {
                    *w.resource_mut::<bool>() = true;
                },
                reg,
            )
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert!(*world.resource::<bool>());
    }

    #[test]
    fn dag_option_unwrap_or() {
        fn root(_x: u32) -> Option<u64> {
            None
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .unwrap_or(42u64)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 42);
    }

    #[test]
    fn dag_option_ok_or() {
        fn root(_x: u32) -> Option<u64> {
            None
        }
        fn sink(mut out: ResMut<u64>, val: &Result<u64, &str>) {
            *out = val.as_ref().map_or(999, |v| *v);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .ok_or("missing")
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 999);
    }

    #[test]
    fn dag_result_map() {
        fn root(_x: u32) -> Result<u64, &'static str> {
            Ok(10)
        }
        fn double(val: &u64) -> u64 {
            *val * 2
        }
        fn sink(mut out: ResMut<u64>, val: &Result<u64, &str>) {
            *out = val.as_ref().copied().unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .map(double, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 20);
    }

    #[test]
    fn dag_result_and_then() {
        fn root(_x: u32) -> Result<u64, &'static str> {
            Ok(5)
        }
        fn check(val: &u64) -> Result<u64, &'static str> {
            if *val > 3 {
                Ok(*val * 10)
            } else {
                Err("too small")
            }
        }
        fn sink(mut out: ResMut<u64>, val: &Result<u64, &str>) {
            *out = val.as_ref().copied().unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .and_then(check, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 50);
    }

    #[test]
    fn dag_result_catch() {
        fn root(_x: u32) -> Result<u64, String> {
            Err("oops".into())
        }
        fn handle_err(mut log: ResMut<String>, err: &String) {
            *log = err.clone();
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<String>(String::new());
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .catch(handle_err, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 0);
        assert_eq!(world.resource::<String>().as_str(), "oops");
    }

    #[test]
    fn dag_result_ok() {
        fn root(_x: u32) -> Result<u64, &'static str> {
            Err("fail")
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .ok()
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 0);
    }

    #[test]
    fn dag_result_unwrap_or_else() {
        fn root(_x: u32) -> Result<u64, &'static str> {
            Err("fail")
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .unwrap_or_else(|_err: &str| 42u64, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 42);
    }

    #[test]
    fn dag_result_map_err() {
        fn root(_x: u32) -> Result<u64, u32> {
            Err(5)
        }
        fn sink(mut out: ResMut<u64>, val: &Result<u64, String>) {
            *out = match val {
                Ok(v) => *v,
                Err(e) => e.len() as u64,
            };
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .map_err(|e: u32| format!("err:{e}"), reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        // "err:5".len() == 5
        assert_eq!(*world.resource::<u64>(), 5);
    }

    #[test]
    fn dag_arm_combinators() {
        fn root(x: u32) -> u64 {
            x as u64 + 10
        }
        fn arm_step(val: &u64) -> Option<u64> {
            if *val > 5 { Some(*val * 3) } else { None }
        }
        fn double(val: &u64) -> u64 {
            *val * 2
        }
        fn merge_fn(a: &u64, b: &u64) -> String {
            format!("{a},{b}")
        }
        fn sink(mut out: ResMut<String>, val: &String) {
            *out = val.clone();
        }
        let mut wb = WorldBuilder::new();
        wb.register::<String>(String::new());
        let mut world = wb.build();
        let reg = world.registry();

        // Arm 0: root → arm_step (Option) → unwrap_or(0)
        // Arm 1: root → double
        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .fork()
            .arm(|a| a.then(arm_step, reg).unwrap_or(0u64))
            .arm(|b| b.then(double, reg))
            .merge(merge_fn, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        // root(0) = 10
        // arm0: 10 > 5 → Some(30) → unwrap → 30
        // arm1: 10 * 2 = 20
        assert_eq!(world.resource::<String>().as_str(), "30,20");
    }

    #[test]
    fn dag_option_inspect() {
        fn root(_x: u32) -> Option<u64> {
            Some(42)
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(false);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .inspect(
                |w: &mut World, _val: &u64| {
                    *w.resource_mut::<bool>() = true;
                },
                reg,
            )
            .then(sink, reg)
            .build();

        dag.run(&mut world, 0u32);
        assert_eq!(*world.resource::<u64>(), 42);
        assert!(*world.resource::<bool>());
    }

    // -- Guard combinator --

    #[test]
    fn dag_guard_keeps() {
        fn root(x: u32) -> u64 {
            x as u64
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .guard(|v: &u64| *v > 3, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 5);
    }

    #[test]
    fn dag_guard_drops() {
        fn root(x: u32) -> u64 {
            x as u64
        }
        fn sink(mut out: ResMut<u64>, val: &Option<u64>) {
            *out = val.unwrap_or(999);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .guard(|v: &u64| *v > 10, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 999);
    }

    #[test]
    fn dag_arm_guard() {
        fn root(x: u32) -> u64 {
            x as u64
        }
        fn double(val: &u64) -> u64 {
            *val * 2
        }
        fn merge_fn(a: &Option<u64>, b: &u64) -> String {
            format!("{:?},{}", a, b)
        }
        fn sink(mut out: ResMut<String>, val: &String) {
            *out = val.clone();
        }
        let mut wb = WorldBuilder::new();
        wb.register::<String>(String::new());
        let mut world = wb.build();
        let reg = world.registry();

        // arm_a: guard drops (5 < 10), arm_b: runs normally
        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .fork()
            .arm(|a| a.then(double, reg).guard(|v: &u64| *v > 100, reg))
            .arm(|b| b.then(double, reg))
            .merge(merge_fn, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 5u32);
        // arm_a: 10, guard fails → None. arm_b: 10.
        assert_eq!(world.resource::<String>().as_str(), "None,10");
    }

    // -- Tap combinator --

    #[test]
    fn dag_tap_observes_without_changing() {
        fn root(x: u32) -> u64 {
            x as u64 * 2
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(false);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .tap(
                |w: &mut World, val: &u64| {
                    // Side-effect: record that we observed the value.
                    *w.resource_mut::<bool>() = *val == 10;
                },
                reg,
            )
            .then(sink, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 10); // value passed through
        assert!(*world.resource::<bool>()); // tap fired
    }

    #[test]
    fn dag_arm_tap() {
        fn root(x: u32) -> u64 {
            x as u64
        }
        fn double(val: &u64) -> u64 {
            *val * 2
        }
        fn merge_add(a: &u64, b: &u64) -> u64 {
            *a + *b
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(false);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .fork()
            .arm(|a| {
                a.then(double, reg).tap(
                    |w: &mut World, _v: &u64| {
                        *w.resource_mut::<bool>() = true;
                    },
                    reg,
                )
            })
            .arm(|b| b.then(double, reg))
            .merge(merge_add, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 5u32);
        // arm_a: 10, arm_b: 10, merge: 20
        assert_eq!(*world.resource::<u64>(), 20);
        assert!(*world.resource::<bool>()); // tap in arm_a fired
    }

    // -- Route combinator --

    #[test]
    fn dag_route_true_arm() {
        fn root(x: u32) -> u64 {
            x as u64
        }
        fn double(val: &u64) -> u64 {
            *val * 2
        }
        fn triple(val: &u64) -> u64 {
            *val * 3
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let arm_t = DagArmSeed::new().then(double, reg);
        let arm_f = DagArmSeed::new().then(triple, reg);

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .route(|v: &u64| *v > 3, reg, arm_t, arm_f)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 5u32); // 5 > 3 → true arm → double → 10
        assert_eq!(*world.resource::<u64>(), 10);
    }

    #[test]
    fn dag_route_false_arm() {
        fn root(x: u32) -> u64 {
            x as u64
        }
        fn double(val: &u64) -> u64 {
            *val * 2
        }
        fn triple(val: &u64) -> u64 {
            *val * 3
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let arm_t = DagArmSeed::new().then(double, reg);
        let arm_f = DagArmSeed::new().then(triple, reg);

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .route(|v: &u64| *v > 10, reg, arm_t, arm_f)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 5u32); // 5 <= 10 → false arm → triple → 15
        assert_eq!(*world.resource::<u64>(), 15);
    }

    #[test]
    fn dag_route_nested() {
        fn root(x: u32) -> u64 {
            x as u64
        }
        fn pass(val: &u64) -> u64 {
            *val
        }
        fn add_100(val: &u64) -> u64 {
            *val + 100
        }
        fn add_200(val: &u64) -> u64 {
            *val + 200
        }
        fn add_300(val: &u64) -> u64 {
            *val + 300
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        // N-ary via nesting: <5 → +100, 5..10 → +200, >=10 → +300
        let inner_t = DagArmSeed::new().then(add_200, reg);
        let inner_f = DagArmSeed::new().then(add_300, reg);
        let outer_t = DagArmSeed::new().then(add_100, reg);
        let outer_f =
            DagArmSeed::new()
                .then(pass, reg)
                .route(|v: &u64| *v < 10, reg, inner_t, inner_f);

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .route(|v: &u64| *v < 5, reg, outer_t, outer_f)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 3u32); // 3 < 5 → +100 → 103
        assert_eq!(*world.resource::<u64>(), 103);

        dag.run(&mut world, 7u32); // 7 >= 5, 7 < 10 → +200 → 207
        assert_eq!(*world.resource::<u64>(), 207);

        dag.run(&mut world, 15u32); // 15 >= 5, 15 >= 10 → +300 → 315
        assert_eq!(*world.resource::<u64>(), 315);
    }

    // -- Tee combinator --

    #[test]
    fn dag_tee_side_effect_chain() {
        fn root(x: u32) -> u64 {
            x as u64 * 2
        }
        fn log_step(mut counter: ResMut<u32>, _val: &u64) {
            *counter += 1;
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<u32>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let side = DagArmSeed::new().then(log_step, reg);

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .tee(side)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 10); // value passed through
        assert_eq!(*world.resource::<u32>(), 1); // side-effect fired

        dag.run(&mut world, 7u32);
        assert_eq!(*world.resource::<u64>(), 14);
        assert_eq!(*world.resource::<u32>(), 2); // fired again
    }

    // -- Dedup combinator --

    #[test]
    fn dag_dedup_suppresses_unchanged() {
        fn root(x: u32) -> u64 {
            x as u64 / 2 // intentional integer division: 4→2, 5→2
        }
        fn sink(mut out: ResMut<u32>, val: &Option<u64>) {
            if val.is_some() {
                *out += 1;
            }
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u32>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .dedup()
            .then(sink, reg)
            .build();

        dag.run(&mut world, 4u32); // 2 — first, Some
        assert_eq!(*world.resource::<u32>(), 1);

        dag.run(&mut world, 5u32); // 2 — same, None
        assert_eq!(*world.resource::<u32>(), 1);

        dag.run(&mut world, 6u32); // 3 — changed, Some
        assert_eq!(*world.resource::<u32>(), 2);
    }

    // -- Bool combinators --

    #[test]
    fn dag_not() {
        fn root(x: u32) -> bool {
            x > 5
        }
        fn sink(mut out: ResMut<bool>, val: &bool) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(false);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .not()
            .then(sink, reg)
            .build();

        dag.run(&mut world, 3u32); // 3 > 5 = false, not = true
        assert!(*world.resource::<bool>());

        dag.run(&mut world, 10u32); // 10 > 5 = true, not = false
        assert!(!*world.resource::<bool>());
    }

    #[test]
    fn dag_and() {
        fn root(x: u32) -> bool {
            x > 5
        }
        fn sink(mut out: ResMut<bool>, val: &bool) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(true); // "market open" flag
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .and(|w: &mut World| *w.resource::<bool>(), reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 10u32); // true && true = true
        assert!(*world.resource::<bool>());

        *world.resource_mut::<bool>() = false; // close market
        dag.run(&mut world, 10u32); // true && false = false
        assert!(!*world.resource::<bool>());
    }

    #[test]
    fn dag_or() {
        fn root(x: u32) -> bool {
            x > 5
        }
        fn sink(mut out: ResMut<bool>, val: &bool) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(false);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .or(|w: &mut World| *w.resource::<bool>(), reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 3u32); // false || false = false
        assert!(!*world.resource::<bool>());

        *world.resource_mut::<bool>() = true;
        dag.run(&mut world, 3u32); // false || true = true
        assert!(*world.resource::<bool>());
    }

    #[test]
    fn dag_xor() {
        fn root(x: u32) -> bool {
            x > 5
        }
        fn sink(mut out: ResMut<bool>, val: &bool) {
            *out = *val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(true);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .xor(|w: &mut World| *w.resource::<bool>(), reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 10u32); // true ^ true = false
        assert!(!*world.resource::<bool>());
    }

    // =========================================================================
    // Splat — tuple destructuring
    // =========================================================================

    #[test]
    fn dag_splat2_on_chain() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn split(x: u32) -> (u32, u32) {
            (x, x * 2)
        }
        fn store(mut out: ResMut<u64>, a: &u32, b: &u32) {
            *out = *a as u64 + *b as u64;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(split, reg)
            .splat()
            .then(store, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 15); // 5 + 10
    }

    #[test]
    fn dag_splat3_on_chain() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn split3(x: u32) -> (u32, u32, u32) {
            (x, x + 1, x + 2)
        }
        fn sum3(a: &u32, b: &u32, c: &u32) -> u64 {
            *a as u64 + *b as u64 + *c as u64
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(split3, reg)
            .splat()
            .then(sum3, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 10u32);
        assert_eq!(*world.resource::<u64>(), 33); // 10+11+12
    }

    #[test]
    fn dag_splat2_with_param() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(100);
        let mut world = wb.build();
        let reg = world.registry();

        fn split(x: u32) -> (u32, u32) {
            (x, x * 3)
        }
        fn add_base(base: Res<u64>, a: &u32, b: &u32) -> u64 {
            *base + *a as u64 + *b as u64
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(split, reg)
            .splat()
            .then(add_base, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 120); // 100 + 5 + 15
    }

    #[test]
    fn dag_splat_on_arm_start() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn split(x: u32) -> (u32, u32) {
            (x, x + 10)
        }
        fn sum2(a: &u32, b: &u32) -> u64 {
            *a as u64 + *b as u64
        }
        fn identity(x: &(u32, u32)) -> u64 {
            x.0 as u64 * x.1 as u64
        }
        fn merge_add(a: &u64, b: &u64) -> u64 {
            *a + *b
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(split, reg)
            .fork()
            .arm(|a| a.splat().then(sum2, reg))
            .arm(|b| b.then(identity, reg))
            .merge(merge_add, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 5u32);
        // arm_a: splat (5, 15) → sum2 = 20
        // arm_b: identity (5, 15) → 75
        // merge: 20 + 75 = 95
        assert_eq!(*world.resource::<u64>(), 95);
    }

    #[test]
    fn dag_splat_on_arm() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn root_id(x: u32) -> u32 {
            x
        }
        fn make_pair(val: &u32) -> (u32, u32) {
            (*val, *val + 100)
        }
        fn sum2(a: &u32, b: &u32) -> u64 {
            *a as u64 + *b as u64
        }
        fn double(val: &u32) -> u64 {
            *val as u64 * 2
        }
        fn merge_add(a: &u64, b: &u64) -> u64 {
            *a + *b
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(root_id, reg)
            .fork()
            .arm(|a| a.then(make_pair, reg).splat().then(sum2, reg))
            .arm(|b| b.then(double, reg))
            .merge(merge_add, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 7u32);
        // arm_a: make_pair(7) = (7, 107), splat → sum2 = 114
        // arm_b: double(7) = 14
        // merge: 114 + 14 = 128
        assert_eq!(*world.resource::<u64>(), 128);
    }

    #[test]
    fn dag_splat4_on_chain() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn split4(x: u32) -> (u32, u32, u32, u32) {
            (x, x + 1, x + 2, x + 3)
        }
        fn sum4(a: &u32, b: &u32, c: &u32, d: &u32) -> u64 {
            (*a + *b + *c + *d) as u64
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(split4, reg)
            .splat()
            .then(sum4, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 10u32);
        assert_eq!(*world.resource::<u64>(), 46); // 10+11+12+13
    }

    #[test]
    fn dag_splat5_on_chain() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn split5(x: u32) -> (u8, u8, u8, u8, u8) {
            let x = x as u8;
            (x, x + 1, x + 2, x + 3, x + 4)
        }
        #[allow(clippy::many_single_char_names)]
        fn sum5(a: &u8, b: &u8, c: &u8, d: &u8, e: &u8) -> u64 {
            (*a as u64) + (*b as u64) + (*c as u64) + (*d as u64) + (*e as u64)
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u32>::new()
            .root(split5, reg)
            .splat()
            .then(sum5, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, 1u32);
        assert_eq!(*world.resource::<u64>(), 15); // 1+2+3+4+5
    }

    #[test]
    fn dag_splat_boxable() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn split(x: u32) -> (u32, u32) {
            (x, x * 2)
        }
        fn store(mut out: ResMut<u64>, a: &u32, b: &u32) {
            *out = *a as u64 + *b as u64;
        }

        let dag = DagBuilder::<u32>::new()
            .root(split, reg)
            .splat()
            .then(store, reg)
            .build();

        let mut boxed: Virtual<u32> = Box::new(dag);
        boxed.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 15);
    }

    // -- Batch DAG --

    #[test]
    fn batch_dag_basic() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn double(x: u32) -> u64 {
            x as u64 * 2
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out += *val;
        }

        let mut batch = DagBuilder::<u32>::new()
            .root(double, reg)
            .then(store, reg)
            .build_batch(8);

        batch.input_mut().extend([1, 2, 3]);
        batch.run(&mut world);

        assert_eq!(*world.resource::<u64>(), 12); // 2 + 4 + 6
        assert!(batch.input().is_empty());
    }

    #[test]
    fn batch_dag_option_terminal() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn double(x: u32) -> u64 {
            x as u64 * 2
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out += *val;
        }

        let mut batch = DagBuilder::<u32>::new()
            .root(double, reg)
            .guard(|val: &u64| *val > 5, reg)
            .map(store, reg)
            .unwrap_or(())
            .build_batch(8);

        batch.input_mut().extend([1, 2, 3, 4, 5]);
        batch.run(&mut world);

        // double: 2, 4, 6, 8, 10
        // guard keeps > 5: 6, 8, 10
        assert_eq!(*world.resource::<u64>(), 24); // 6 + 8 + 10
    }

    #[test]
    fn batch_dag_buffer_reuse() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn double(x: u32) -> u64 {
            x as u64 * 2
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out += *val;
        }

        let mut batch = DagBuilder::<u32>::new()
            .root(double, reg)
            .then(store, reg)
            .build_batch(8);

        batch.input_mut().extend([1, 2]);
        batch.run(&mut world);
        assert_eq!(*world.resource::<u64>(), 6); // 2 + 4
        assert!(batch.input().is_empty());

        batch.input_mut().extend([10, 20]);
        batch.run(&mut world);
        assert_eq!(*world.resource::<u64>(), 66); // 6 + 20 + 40
    }

    #[test]
    fn batch_dag_retains_allocation() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        fn noop(_x: u32) {}

        let mut batch = DagBuilder::<u32>::new().root(noop, reg).build_batch(64);

        batch.input_mut().extend([1, 2, 3]);
        batch.run(&mut world);

        assert!(batch.input().is_empty());
        assert!(batch.input_mut().capacity() >= 64);
    }

    #[test]
    fn batch_dag_empty_is_noop() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn double(x: u32) -> u64 {
            x as u64 * 2
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out += *val;
        }

        let mut batch = DagBuilder::<u32>::new()
            .root(double, reg)
            .then(store, reg)
            .build_batch(8);

        batch.run(&mut world);
        assert_eq!(*world.resource::<u64>(), 0);
    }

    #[test]
    fn batch_dag_with_splat() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn split(x: u32) -> (u64, u64) {
            (x as u64, x as u64 * 10)
        }
        fn combine(a: &u64, b: &u64) -> u64 {
            *a + *b
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out += *val;
        }

        let mut batch = DagBuilder::<u32>::new()
            .root(split, reg)
            .splat()
            .then(combine, reg)
            .then(store, reg)
            .build_batch(4);

        batch.input_mut().extend([1, 2]);
        batch.run(&mut world);

        // 1 → (1, 10) → 11, 2 → (2, 20) → 22
        assert_eq!(*world.resource::<u64>(), 33); // 11 + 22
    }

    // -- Conditional then (formerly switch) --

    #[test]
    fn dag_then_conditional_basic() {
        fn root(x: u32) -> u64 {
            x as u64
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .then(|val: &u64| if *val > 5 { *val * 10 } else { *val + 1 }, reg)
            .then(sink, reg)
            .build();

        dag.run(&mut world, 10u32); // 10 > 5 → 100
        assert_eq!(*world.resource::<u64>(), 100);

        dag.run(&mut world, 3u32); // 3 <= 5 → 4
        assert_eq!(*world.resource::<u64>(), 4);
    }

    #[test]
    fn dag_then_conditional_3_way() {
        fn root(x: u32) -> u32 {
            x
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .then(
                |val: &u32| match *val % 3 {
                    0 => *val as u64 + 100,
                    1 => *val as u64 + 200,
                    _ => *val as u64 + 300,
                },
                reg,
            )
            .then(sink, reg)
            .build();

        dag.run(&mut world, 6u32); // 6 % 3 == 0 → 106
        assert_eq!(*world.resource::<u64>(), 106);

        dag.run(&mut world, 7u32); // 7 % 3 == 1 → 207
        assert_eq!(*world.resource::<u64>(), 207);

        dag.run(&mut world, 8u32); // 8 % 3 == 2 → 308
        assert_eq!(*world.resource::<u64>(), 308);
    }

    #[test]
    fn dag_then_with_resolve_arm() {
        fn root(x: u32) -> u32 {
            x
        }
        fn double(val: &u32) -> u64 {
            *val as u64 * 2
        }
        fn triple(val: &u32) -> u64 {
            *val as u64 * 3
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut arm_even = resolve_arm(double, reg);
        let mut arm_odd = resolve_arm(triple, reg);

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .then(
                move |world: &mut World, val: &u32| {
                    if (*val).is_multiple_of(2) {
                        arm_even(world, val)
                    } else {
                        arm_odd(world, val)
                    }
                },
                reg,
            )
            .then(sink, reg)
            .build();

        dag.run(&mut world, 4u32); // even → double → 8
        assert_eq!(*world.resource::<u64>(), 8);

        dag.run(&mut world, 5u32); // odd → triple → 15
        assert_eq!(*world.resource::<u64>(), 15);
    }

    #[test]
    fn dag_resolve_arm_with_params() {
        fn root(x: u32) -> u32 {
            x
        }
        fn add_offset(offset: Res<i64>, val: &u32) -> u64 {
            (*offset + *val as i64) as u64
        }
        fn plain_double(val: &u32) -> u64 {
            *val as u64 * 2
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<i64>(100);
        let mut world = wb.build();
        let reg = world.registry();

        // Each arm resolves different params
        let mut arm_offset = resolve_arm(add_offset, reg);
        let mut arm_double = resolve_arm(plain_double, reg);

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .then(
                move |world: &mut World, val: &u32| {
                    if *val > 10 {
                        arm_offset(world, val)
                    } else {
                        arm_double(world, val)
                    }
                },
                reg,
            )
            .then(sink, reg)
            .build();

        dag.run(&mut world, 20u32); // > 10 → add_offset → 100 + 20 = 120
        assert_eq!(*world.resource::<u64>(), 120);

        dag.run(&mut world, 5u32); // <= 10 → double → 10
        assert_eq!(*world.resource::<u64>(), 10);
    }

    #[test]
    fn dag_then_conditional_in_fork_arm() {
        fn root(x: u32) -> u32 {
            x
        }
        fn pass(val: &u32) -> u32 {
            *val
        }
        fn sink_u64(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }
        fn sink_i64(mut out: ResMut<i64>, val: &u32) {
            *out = -(*val as i64);
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<i64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut dag = DagBuilder::<u32>::new()
            .root(root, reg)
            .fork()
            .arm(|a| {
                a.then(pass, reg)
                    .then(
                        |val: &u32| {
                            if *val > 5 {
                                *val as u64 * 10
                            } else {
                                *val as u64
                            }
                        },
                        reg,
                    )
                    .then(sink_u64, reg)
            })
            .arm(|a| a.then(sink_i64, reg))
            .join()
            .build();

        dag.run(&mut world, 10u32); // arm0: 10 > 5 → 100, arm1: -10
        assert_eq!(*world.resource::<u64>(), 100);
        assert_eq!(*world.resource::<i64>(), -10);

        dag.run(&mut world, 3u32); // arm0: 3 <= 5 → 3, arm1: -3
        assert_eq!(*world.resource::<u64>(), 3);
        assert_eq!(*world.resource::<i64>(), -3);
    }

    #[test]
    fn batch_dag_then_conditional() {
        fn root(x: u32) -> u32 {
            x
        }
        fn sink(mut out: ResMut<u64>, val: &u64) {
            *out += *val;
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut batch = DagBuilder::<u32>::new()
            .root(root, reg)
            .then(
                |val: &u32| {
                    if (*val).is_multiple_of(2) {
                        *val as u64 * 10
                    } else {
                        *val as u64
                    }
                },
                reg,
            )
            .then(sink, reg)
            .build_batch(8);

        batch.input_mut().extend([1, 2, 3, 4]);
        batch.run(&mut world);

        // 1 → 1, 2 → 20, 3 → 3, 4 → 40 = 64
        assert_eq!(*world.resource::<u64>(), 64);
    }

    // =========================================================================
    // Scan combinator (DAG)
    // =========================================================================

    #[test]
    fn dag_scan_arity0_closure() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let mut dag = DagBuilder::<u64>::new()
            .root(|x: u64| x, reg)
            .scan(
                0u64,
                |acc: &mut u64, val: &u64| {
                    *acc += val;
                    *acc
                },
                reg,
            )
            .then(store, reg)
            .build();

        dag.run(&mut world, 10);
        assert_eq!(*world.resource::<u64>(), 10);
        dag.run(&mut world, 20);
        assert_eq!(*world.resource::<u64>(), 30);
        dag.run(&mut world, 5);
        assert_eq!(*world.resource::<u64>(), 35);
    }

    #[test]
    fn dag_scan_named_fn_with_param() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(100);
        wb.register::<String>(String::new());
        let mut world = wb.build();
        let reg = world.registry();

        fn threshold(limit: Res<u64>, acc: &mut u64, val: &u64) -> Option<u64> {
            *acc += val;
            if *acc > *limit { Some(*acc) } else { None }
        }
        fn store_opt(mut out: ResMut<String>, val: &Option<u64>) {
            *out = val
                .as_ref()
                .map_or_else(|| "below".into(), |v| format!("hit:{v}"));
        }

        let mut dag = DagBuilder::<u64>::new()
            .root(|x: u64| x, reg)
            .scan(0u64, threshold, reg)
            .then(store_opt, reg)
            .build();

        dag.run(&mut world, 50);
        assert_eq!(world.resource::<String>().as_str(), "below");
        dag.run(&mut world, 60);
        assert_eq!(world.resource::<String>().as_str(), "hit:110");
    }

    #[test]
    fn dag_arm_scan() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        let scan_arm = DagArmSeed::<u64>::new()
            .then(|v: &u64| *v, reg)
            .scan(
                0u64,
                |acc: &mut u64, val: &u64| {
                    *acc += val;
                    *acc
                },
                reg,
            )
            .then(store, reg);

        let pass_arm = DagArmSeed::<u64>::new().then(|_: &u64| {}, reg);

        let mut dag = DagBuilder::<u64>::new()
            .root(|x: u64| x, reg)
            .fork()
            .arm(|_| scan_arm)
            .arm(|_| pass_arm)
            .merge(|(): &(), (): &()| {}, reg)
            .build();

        dag.run(&mut world, 10);
        assert_eq!(*world.resource::<u64>(), 10);
        dag.run(&mut world, 20);
        assert_eq!(*world.resource::<u64>(), 30);
    }

    // =========================================================================
    // Build — Option<()> terminal
    // =========================================================================

    #[test]
    fn build_option_unit_terminal() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        // root takes by value (IntoStep), then .guard() produces Option
        fn check(x: u32) -> u64 {
            x as u64
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out += *val;
        }

        // guard → Option<u64>, map(store) → Option<()>, build() should work
        let mut dag = DagBuilder::<u32>::new()
            .root(check, reg)
            .guard(|val: &u64| *val > 5, reg)
            .map(store, reg)
            .build();

        dag.run(&mut world, 3); // guard filters → None
        assert_eq!(*world.resource::<u64>(), 0);
        dag.run(&mut world, 7); // passes guard → stores 7
        assert_eq!(*world.resource::<u64>(), 7);
    }

    // =========================================================================
    // Build — borrowed event type
    // =========================================================================

    #[test]
    fn build_borrowed_event_direct() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn decode(msg: &[u8]) -> u64 {
            msg.len() as u64
        }
        fn store(mut out: ResMut<u64>, val: &u64) {
            *out = *val;
        }

        // msg declared before dag so it outlives the DAG (drop order).
        let msg = vec![1u8, 2, 3];
        let reg = world.registry();
        let mut dag = DagBuilder::<&[u8]>::new()
            .root(decode, reg)
            .then(store, reg)
            .build();

        dag.run(&mut world, &msg);
        assert_eq!(*world.resource::<u64>(), 3);
    }
}
