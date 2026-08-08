// Builder return types are necessarily complex — each combinator returns
// PipelineChain<In, Out, NodeType<Chain, ...>>. Same pattern as iterator adapters.
#![allow(clippy::type_complexity)]
// Handler arity is architecturally required by the Param trait — handlers
// take N typed parameters and the macro-generated dispatch impls expand
// per-arity into call_inner functions with N + Input arguments. Module-level
// allow rather than one inline attribute per arity expansion.
#![allow(clippy::too_many_arguments)]

//! Pre-resolved pipeline dispatch using [`Param`] steps.
//!
//! [`PipelineBuilder`] begins a typed composition chain where each step
//! is a named function with [`Param`] dependencies resolved at build
//! time. The result is a monomorphized chain of named node types where dispatch-time
//! resource access is a single pointer deref per fetch — zero framework overhead.
//! [`ResourceId`](crate::ResourceId) is a direct pointer, not a HashMap lookup.
//!
//! Two dispatch tiers in nexus-rt:
//! 1. **Pipeline** — static after build, pre-resolved, the workhorse
//! 2. **Callback** — dynamic registration with per-instance context
//!
//! # Step function convention
//!
//! Params first, step input last, returns output:
//!
//! ```ignore
//! fn validate(config: Res<Config>, order: Order) -> Option<ValidOrder> { .. }
//! fn enrich(cache: Res<MarketData>, order: ValidOrder) -> EnrichedOrder { .. }
//! fn submit(mut gw: ResMut<Gateway>, order: CheckedOrder) { gw.send(order); }
//! ```
//!
//! # Combinator split
//!
//! **IntoStep-based (pre-resolved, hot path):**
//! `.then()`, `.map()`, `.and_then()`, `.catch()`
//!
//! **Trait-based (same API for named functions, arity-0 closures, and [`Opaque`] closures):**
//! `.guard()`, `.filter()`, `.tap()`, `.inspect()`, `.inspect_err()`,
//! `.on_none()`, `.ok_or_else()`, `.unwrap_or_else()`, `.map_err()`,
//! `.or_else()`, `.and()`, `.or()`, `.xor()`, `.route()`
//!
//! # Combinator quick reference
//!
//! **Bare value `T`:** `.then()`, `.tap()`, `.guard()` (→ `Option<T>`),
//! `.dispatch()`, `.route()`, `.tee()`, `.scan()`, `.dedup()` (→ `Option<T>`)
//!
//! **Tuple `(A, B, ...)` (2-5 elements):** `.splat()` (→ splat builder,
//! call `.then()` with destructured args)
//!
//! **`Option<T>`:** `.map()`, `.filter()`, `.inspect()`, `.and_then()`,
//! `.on_none()`, `.ok_or()` (→ `Result`), `.unwrap_or()` (→ `T`),
//! `.cloned()` (→ `Option<T>` from `Option<&T>`)
//!
//! **`Result<T, E>`:** `.map()`, `.and_then()`, `.catch()` (→ `Option<T>`),
//! `.map_err()`, `.inspect_err()`, `.ok()` (→ `Option<T>`),
//! `.unwrap_or()` (→ `T`), `.or_else()`
//!
//! **`bool`:** `.not()`, `.and()`, `.or()`, `.xor()`
//!
//! **Terminal:** `.build()` (→ `Pipeline`), `.build_batch(cap)`
//! (→ `BatchPipeline<In>`)
//!
//! # Splat — tuple destructuring
//!
//! Pipeline steps follow a single-value-in, single-value-out convention.
//! When a step returns a tuple like `(OrderId, f64)`, the next step
//! must accept the whole tuple as one argument. `.splat()` destructures
//! the tuple so the next step receives individual arguments instead:
//!
//! ```ignore
//! // Without splat — next step takes the whole tuple:
//! fn process(pair: (OrderId, f64)) -> bool { .. }
//!
//! // With splat — next step takes individual args:
//! fn process(id: OrderId, price: f64) -> bool { .. }
//!
//! PipelineBuilder::<Order>::new()
//!     .then(extract, reg)   // Order → (OrderId, f64)
//!     .splat()              // destructure
//!     .then(process, reg)   // (OrderId, f64) → bool
//!     .build();
//! ```
//!
//! Supported for tuples of 2-5 elements. Beyond 5, define a named
//! struct — if a combinator stage needs that many arguments, a struct
//! makes the intent clearer and the code more maintainable.
//!
//! # Returning pipelines from functions (Rust 2024)
//!
//! When a factory function takes `&Registry` and returns `impl Handler<E>`,
//! Rust 2024 captures the registry borrow in the return type by default.
//! Use `+ use<...>` to exclude it:
//!
//! ```ignore
//! fn on_order<C: Config>(
//!     reg: &Registry,
//! ) -> impl Handler<Order> + use<C> {
//!     PipelineBuilder::<Order>::new()
//!         .then(validate::<C>, reg)
//!         .dispatch(submit::<C>.into_handler(reg))
//!         .build()
//! }
//! ```
//!
//! List every type parameter the pipeline captures; omit the `&Registry`
//! lifetime — it's consumed during `.build()`. See the
//! [crate-level docs](crate#returning-impl-handler-from-functions-rust-2024)
//! for the full explanation.

use std::marker::PhantomData;

use crate::Handler;
use crate::dag::DagArm;
use crate::handler::{Opaque, Param};
use crate::world::{Registry, World};

// =============================================================================
// Step — pre-resolved step with Param state
// =============================================================================

/// Internal: pre-resolved step with cached Param state.
///
/// Users don't construct this directly — it's produced by [`IntoStep`] and
/// stored inside named chain node types.
#[doc(hidden)]
pub struct Step<F, Params: Param> {
    f: F,
    state: Params::State,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

// =============================================================================
// StepCall — callable trait for resolved steps
// =============================================================================

/// Internal: callable trait for resolved steps.
///
/// Used as a bound on [`IntoStep::Step`]. Users don't implement this.
#[doc(hidden)]
pub trait StepCall<In> {
    /// The output type of this step.
    type Out;
    /// Call this step with a world reference and input value.
    fn call(&mut self, world: &mut World, input: In) -> Self::Out;
}

// =============================================================================
// IntoStep — converts a named function into a resolved step
// =============================================================================

/// Converts a named function into a pre-resolved pipeline step.
///
/// Params first, step input last, returns output. Arity 0 (no
/// Params) supports closures. Arities 1+ require named functions
/// (same HRTB+GAT limitation as [`IntoHandler`](crate::IntoHandler)).
///
/// # Examples
///
/// ```ignore
/// // Arity 0 — closure works
/// let step = (|x: u32| x * 2).into_step(registry);
///
/// // Arity 1 — named function required
/// fn validate(config: Res<Config>, order: Order) -> Option<ValidOrder> { .. }
/// let step = validate.into_step(registry);
/// ```
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a pipeline step for this input type",
    note = "if the pipeline output is `Option<T>`, use `.map()` to operate on the inner `T`",
    note = "if the pipeline output is `Result<T, E>`, use `.map()` for `Ok` or `.catch()` for `Err`",
    note = "if using a closure with resource params (Res<T>, ResMut<T>), that isn't supported — use a named `fn`"
)]
pub trait IntoStep<In, Out, Params> {
    /// The concrete resolved step type.
    type Step: StepCall<In, Out = Out>;

    /// Resolve Param state from the registry and produce a step.
    fn into_step(self, registry: &Registry) -> Self::Step;
}

// =============================================================================
// Arity 0 — fn(In) -> Out — closures work (no HRTB+GAT issues)
// =============================================================================

impl<In, Out, F: FnMut(In) -> Out + 'static> StepCall<In> for Step<F, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, _world: &mut World, input: In) -> Out {
        (self.f)(input)
    }
}

impl<In, Out, F: FnMut(In) -> Out + 'static> IntoStep<In, Out, ()> for F {
    type Step = Step<F, ()>;

    fn into_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// Arities 1-8 via macro — HRTB with -> Out
// =============================================================================

macro_rules! impl_into_step {
    ($($P:ident),+) => {
        impl<In, Out, F: 'static, $($P: Param + 'static),+>
            StepCall<In> for Step<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ In) -> Out +
                FnMut($($P::Item<'a>,)+ In) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, input: In) -> Out {
                fn call_inner<$($P,)+ Input, Output>(
                    mut f: impl FnMut($($P,)+ Input) -> Output,
                    $($P: $P,)+
                    input: Input,
                ) -> Output {
                    f($($P,)+ input)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ input)
            }
        }

        impl<In, Out, F: 'static, $($P: Param + 'static),+>
            IntoStep<In, Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ In) -> Out +
                FnMut($($P::Item<'a>,)+ In) -> Out,
        {
            type Step = Step<F, ($($P,)+)>;

            fn into_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_step);

// =============================================================================
// No-event Step — IntoStep<(), Out, _> without passing `()` to the function
// =============================================================================

use crate::handler::NoEvent;

// Arity 0: fn() -> Out
impl<Out, F: FnMut() -> Out + 'static> StepCall<()> for Step<NoEvent<F>, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, _world: &mut World, _input: ()) -> Out {
        (self.f.0)()
    }
}

impl<Out, F: FnMut() -> Out + 'static> IntoStep<(), Out, NoEvent<F>> for F {
    type Step = Step<NoEvent<F>, ()>;

    fn into_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: NoEvent(self),
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_into_step_no_event {
    ($($P:ident),+) => {
        impl<Out, F: 'static, $($P: Param + 'static),+>
            StepCall<()> for Step<NoEvent<F>, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+) -> Out +
                FnMut($($P::Item<'a>,)+) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, _input: ()) -> Out {
                fn call_inner<$($P,)+ Output>(
                    mut f: impl FnMut($($P,)+) -> Output,
                    $($P: $P,)+
                ) -> Output {
                    f($($P,)+)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f.0, $($P,)+)
            }
        }

        impl<Out, F: 'static, $($P: Param + 'static),+>
            IntoStep<(), Out, ($($P,)+)> for NoEvent<F>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+) -> Out +
                FnMut($($P::Item<'a>,)+) -> Out,
        {
            type Step = Step<NoEvent<F>, ($($P,)+)>;

            fn into_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_step_no_event);

// =============================================================================
// OpaqueStep — wrapper for opaque closures as steps
// =============================================================================

/// Internal: wrapper for opaque closures used as pipeline steps.
///
/// Unlike [`Step<F, P>`] which stores resolved `Param::State`, this
/// holds only the function — no state to resolve.
#[doc(hidden)]
pub struct OpaqueStep<F> {
    f: F,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

impl<In, Out, F: FnMut(&mut World, In) -> Out + 'static> StepCall<In> for OpaqueStep<F> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Out {
        (self.f)(world, input)
    }
}

impl<In, Out, F: FnMut(&mut World, In) -> Out + 'static> IntoStep<In, Out, Opaque> for F {
    type Step = OpaqueStep<F>;

    fn into_step(self, _registry: &Registry) -> Self::Step {
        OpaqueStep {
            f: self,
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// RefStepCall / IntoRefStep — step taking &In, returning Out
// =============================================================================

/// Internal: callable trait for resolved steps taking input by reference.
///
/// Used by combinators like `tap`, `guard`, `filter`, `inspect` that
/// observe the value without consuming it.
#[doc(hidden)]
pub trait RefStepCall<In> {
    /// The output type of this step.
    type Out;
    /// Call this step with a world reference and borrowed input.
    fn call(&mut self, world: &mut World, input: &In) -> Self::Out;
}

/// Converts a function into a pre-resolved step taking input by reference.
///
/// Same three-tier resolution as [`IntoStep`]:
///
/// | Params | Function shape | Example |
/// |--------|---------------|---------|
/// | `()` | `FnMut(&In) -> Out` | `\|o: &Order\| o.price > 0.0` |
/// | `(P0,)...(P0..P7,)` | `fn(Params..., &In) -> Out` | `fn check(c: Res<Config>, o: &Order) -> bool` |
/// | [`Opaque`] | `FnMut(&mut World, &In) -> Out` | `\|w: &mut World, o: &Order\| { ... }` |
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a reference step for this input type",
    note = "reference steps (guard, filter, tap, inspect) take `&In`, not `In`",
    note = "if the pipeline output is `Option<T>`, `.filter()` operates on `&T` inside the Option",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoRefStep<In, Out, Params> {
    /// The concrete resolved step type.
    type Step: RefStepCall<In, Out = Out>;

    /// Resolve Param state from the registry and produce a step.
    fn into_ref_step(self, registry: &Registry) -> Self::Step;
}

// -- Arity 0: FnMut(&In) -> Out — closures work ----------------------------

impl<In, Out, F: FnMut(&In) -> Out + 'static> RefStepCall<In> for Step<F, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, _world: &mut World, input: &In) -> Out {
        (self.f)(input)
    }
}

impl<In, Out, F: FnMut(&In) -> Out + 'static> IntoRefStep<In, Out, ()> for F {
    type Step = Step<F, ()>;

    fn into_ref_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// -- Arities 1-8: named functions with Param resolution ---------------------

macro_rules! impl_into_ref_step {
    ($($P:ident),+) => {
        impl<In, Out, F: 'static, $($P: Param + 'static),+>
            RefStepCall<In> for Step<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &In) -> Out +
                FnMut($($P::Item<'a>,)+ &In) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, input: &In) -> Out {
                fn call_inner<$($P,)+ Input: ?Sized, Output>(
                    mut f: impl FnMut($($P,)+ &Input) -> Output,
                    $($P: $P,)+
                    input: &Input,
                ) -> Output {
                    f($($P,)+ input)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ input)
            }
        }

        impl<In, Out, F: 'static, $($P: Param + 'static),+>
            IntoRefStep<In, Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &In) -> Out +
                FnMut($($P::Item<'a>,)+ &In) -> Out,
        {
            type Step = Step<F, ($($P,)+)>;

            fn into_ref_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_ref_step);

// =============================================================================
// No-event RefStep — IntoRefStep<(), Out, _> without passing `&()` to function
// =============================================================================

// Arity 0: fn() -> Out
impl<Out, F: FnMut() -> Out + 'static> RefStepCall<()> for Step<NoEvent<F>, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, _world: &mut World, _input: &()) -> Out {
        (self.f.0)()
    }
}

impl<Out, F: FnMut() -> Out + 'static> IntoRefStep<(), Out, NoEvent<F>> for F {
    type Step = Step<NoEvent<F>, ()>;

    fn into_ref_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: NoEvent(self),
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_into_ref_step_no_event {
    ($($P:ident),+) => {
        impl<Out, F: 'static, $($P: Param + 'static),+>
            RefStepCall<()> for Step<NoEvent<F>, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+) -> Out +
                FnMut($($P::Item<'a>,)+) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, _input: &()) -> Out {
                fn call_inner<$($P,)+ Output>(
                    mut f: impl FnMut($($P,)+) -> Output,
                    $($P: $P,)+
                ) -> Output {
                    f($($P,)+)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f.0, $($P,)+)
            }
        }

        impl<Out, F: 'static, $($P: Param + 'static),+>
            IntoRefStep<(), Out, ($($P,)+)> for NoEvent<F>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+) -> Out +
                FnMut($($P::Item<'a>,)+) -> Out,
        {
            type Step = Step<NoEvent<F>, ($($P,)+)>;

            fn into_ref_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_ref_step_no_event);

// -- Opaque: FnMut(&mut World, &In) -> Out ---------------------------------

/// Internal: wrapper for opaque closures taking input by reference.
#[doc(hidden)]
pub struct OpaqueRefStep<F> {
    f: F,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

impl<In, Out, F: FnMut(&mut World, &In) -> Out + 'static> RefStepCall<In> for OpaqueRefStep<F> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: &In) -> Out {
        (self.f)(world, input)
    }
}

impl<In, Out, F: FnMut(&mut World, &In) -> Out + 'static> IntoRefStep<In, Out, Opaque> for F {
    type Step = OpaqueRefStep<F>;

    fn into_ref_step(self, _registry: &Registry) -> Self::Step {
        OpaqueRefStep {
            f: self,
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// resolve_ref_step — pre-resolve a ref step for manual dispatch
// =============================================================================

/// Resolve a reference step for manual dispatch.
///
/// Returns a closure with pre-resolved [`Param`] state. Reference-input
/// counterpart of [`resolve_step`].
pub fn resolve_ref_step<In, Out, Params, S: IntoRefStep<In, Out, Params>>(
    f: S,
    registry: &Registry,
) -> impl FnMut(&mut World, &In) -> Out + use<In, Out, Params, S> {
    let mut resolved = f.into_ref_step(registry);
    move |world: &mut World, input: &In| resolved.call(world, input)
}

// =============================================================================
// ProducerCall / IntoProducer — step producing a value with no pipeline input
// =============================================================================

/// Internal: callable trait for resolved steps that produce a value
/// without receiving pipeline input.
///
/// Used by combinators like `and`, `or`, `xor`, `on_none`, `ok_or_else`,
/// `unwrap_or_else` (Option).
#[doc(hidden)]
pub trait ProducerCall {
    /// The output type of this producer.
    type Out;
    /// Call this producer with a world reference.
    fn call(&mut self, world: &mut World) -> Self::Out;
}

/// Converts a function into a pre-resolved producer step.
///
/// Same three-tier resolution as [`IntoStep`]:
///
/// | Params | Function shape | Example |
/// |--------|---------------|---------|
/// | `()` | `FnMut() -> Out` | `\|\| true` |
/// | `(P0,)...(P0..P7,)` | `fn(Params...) -> Out` | `fn is_active(s: Res<State>) -> bool` |
/// | [`Opaque`] | `FnMut(&mut World) -> Out` | `\|w: &mut World\| { ... }` |
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a producer for this output type",
    note = "producers take no pipeline input — they produce a value (e.g., default, fallback)",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoProducer<Out, Params> {
    /// The concrete resolved producer type.
    type Step: ProducerCall<Out = Out>;

    /// Resolve Param state from the registry and produce a step.
    fn into_producer(self, registry: &Registry) -> Self::Step;
}

// -- Arity 0: FnMut() -> Out — closures work --------------------------------

impl<Out, F: FnMut() -> Out + 'static> ProducerCall for Step<F, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, _world: &mut World) -> Out {
        (self.f)()
    }
}

impl<Out, F: FnMut() -> Out + 'static> IntoProducer<Out, ()> for F {
    type Step = Step<F, ()>;

    fn into_producer(self, registry: &Registry) -> Self::Step {
        Step {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// -- Arities 1-8: named functions with Param resolution ---------------------

macro_rules! impl_into_producer {
    ($($P:ident),+) => {
        impl<Out, F: 'static, $($P: Param + 'static),+>
            ProducerCall for Step<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+) -> Out +
                FnMut($($P::Item<'a>,)+) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World) -> Out {
                fn call_inner<$($P,)+ Output>(
                    mut f: impl FnMut($($P,)+) -> Output,
                    $($P: $P,)+
                ) -> Output {
                    f($($P,)+)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+)
            }
        }

        impl<Out, F: 'static, $($P: Param + 'static),+>
            IntoProducer<Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut($($P,)+) -> Out +
                FnMut($($P::Item<'a>,)+) -> Out,
        {
            type Step = Step<F, ($($P,)+)>;

            fn into_producer(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_producer);

// -- Opaque: FnMut(&mut World) -> Out ---------------------------------------

/// Internal: wrapper for opaque closures used as producers.
#[doc(hidden)]
pub struct OpaqueProducer<F> {
    f: F,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

impl<Out, F: FnMut(&mut World) -> Out + 'static> ProducerCall for OpaqueProducer<F> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World) -> Out {
        (self.f)(world)
    }
}

impl<Out, F: FnMut(&mut World) -> Out + 'static> IntoProducer<Out, Opaque> for F {
    type Step = OpaqueProducer<F>;

    fn into_producer(self, _registry: &Registry) -> Self::Step {
        OpaqueProducer {
            f: self,
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// resolve_producer — pre-resolve a producer for manual dispatch
// =============================================================================

/// Resolve a producer for manual dispatch.
///
/// Returns a closure with pre-resolved [`Param`] state. No-input
/// counterpart of [`resolve_step`].
pub fn resolve_producer<Out, Params, S: IntoProducer<Out, Params>>(
    f: S,
    registry: &Registry,
) -> impl FnMut(&mut World) -> Out + use<Out, Params, S> {
    let mut resolved = f.into_producer(registry);
    move |world: &mut World| resolved.call(world)
}

// =============================================================================
// ScanStepCall / IntoScanStep — step with persistent accumulator
// =============================================================================

/// Internal: callable trait for resolved scan steps.
///
/// Like [`StepCall`] but with an additional `&mut Acc` accumulator
/// argument that persists across invocations.
#[doc(hidden)]
pub trait ScanStepCall<Acc, In> {
    /// The output type of this scan step.
    type Out;
    /// Call this scan step with a world reference, accumulator, and input value.
    fn call(&mut self, world: &mut World, acc: &mut Acc, input: In) -> Self::Out;
}

/// Converts a function into a pre-resolved scan step with persistent state.
///
/// Same three-tier resolution as [`IntoStep`]:
///
/// | Params | Function shape | Example |
/// |--------|---------------|---------|
/// | `()` | `FnMut(&mut Acc, In) -> Out` | `\|acc, trade\| { *acc += trade.amount; Some(*acc) }` |
/// | `(P0,)...(P0..P7,)` | `fn(Params..., &mut Acc, In) -> Out` | `fn vwap(c: Res<Config>, acc: &mut State, t: Trade) -> Option<f64>` |
/// | [`Opaque`] | `FnMut(&mut World, &mut Acc, In) -> Out` | `\|w: &mut World, acc: &mut u64, t: Trade\| { ... }` |
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a scan step",
    note = "scan steps take `&mut Accumulator` as first param, then resources, then input last",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoScanStep<Acc, In, Out, Params> {
    /// The concrete resolved scan step type.
    type Step: ScanStepCall<Acc, In, Out = Out>;

    /// Resolve Param state from the registry and produce a scan step.
    fn into_scan_step(self, registry: &Registry) -> Self::Step;
}

// -- Arity 0: FnMut(&mut Acc, In) -> Out — closures work --------------------

impl<Acc, In, Out, F: FnMut(&mut Acc, In) -> Out + 'static> ScanStepCall<Acc, In> for Step<F, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, _world: &mut World, acc: &mut Acc, input: In) -> Out {
        (self.f)(acc, input)
    }
}

impl<Acc, In, Out, F: FnMut(&mut Acc, In) -> Out + 'static> IntoScanStep<Acc, In, Out, ()> for F {
    type Step = Step<F, ()>;

    fn into_scan_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// -- Arities 1-8: named functions with Param resolution ----------------------

macro_rules! impl_into_scan_step {
    ($($P:ident),+) => {
        impl<Acc, In, Out, F: 'static, $($P: Param + 'static),+>
            ScanStepCall<Acc, In> for Step<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &mut Acc, In) -> Out +
                FnMut($($P::Item<'a>,)+ &mut Acc, In) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, acc: &mut Acc, input: In) -> Out {
                fn call_inner<$($P,)+ Accumulator, Input, Output>(
                    mut f: impl FnMut($($P,)+ &mut Accumulator, Input) -> Output,
                    $($P: $P,)+
                    acc: &mut Accumulator,
                    input: Input,
                ) -> Output {
                    f($($P,)+ acc, input)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ acc, input)
            }
        }

        impl<Acc, In, Out, F: 'static, $($P: Param + 'static),+>
            IntoScanStep<Acc, In, Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &mut Acc, In) -> Out +
                FnMut($($P::Item<'a>,)+ &mut Acc, In) -> Out,
        {
            type Step = Step<F, ($($P,)+)>;

            fn into_scan_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_scan_step);

// =============================================================================
// No-event ScanStep — IntoScanStep<Acc, (), Out, _> without passing `()` input
// =============================================================================

// Arity 0: fn(&mut Acc) -> Out
impl<Acc, Out, F: FnMut(&mut Acc) -> Out + 'static> ScanStepCall<Acc, ()> for Step<NoEvent<F>, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, _world: &mut World, acc: &mut Acc, _input: ()) -> Out {
        (self.f.0)(acc)
    }
}

impl<Acc, Out, F: FnMut(&mut Acc) -> Out + 'static> IntoScanStep<Acc, (), Out, NoEvent<F>> for F {
    type Step = Step<NoEvent<F>, ()>;

    fn into_scan_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: NoEvent(self),
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_into_scan_step_no_event {
    ($($P:ident),+) => {
        impl<Acc, Out, F: 'static, $($P: Param + 'static),+>
            ScanStepCall<Acc, ()> for Step<NoEvent<F>, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &mut Acc) -> Out +
                FnMut($($P::Item<'a>,)+ &mut Acc) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, acc: &mut Acc, _input: ()) -> Out {
                fn call_inner<$($P,)+ Accumulator, Output>(
                    mut f: impl FnMut($($P,)+ &mut Accumulator) -> Output,
                    $($P: $P,)+
                    acc: &mut Accumulator,
                ) -> Output {
                    f($($P,)+ acc)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f.0, $($P,)+ acc)
            }
        }

        impl<Acc, Out, F: 'static, $($P: Param + 'static),+>
            IntoScanStep<Acc, (), Out, ($($P,)+)> for NoEvent<F>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &mut Acc) -> Out +
                FnMut($($P::Item<'a>,)+ &mut Acc) -> Out,
        {
            type Step = Step<NoEvent<F>, ($($P,)+)>;

            fn into_scan_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_scan_step_no_event);

// -- Opaque: FnMut(&mut World, &mut Acc, In) -> Out --------------------------

/// Internal: wrapper for opaque closures used as scan steps.
#[doc(hidden)]
pub struct OpaqueScanStep<F> {
    f: F,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

impl<Acc, In, Out, F: FnMut(&mut World, &mut Acc, In) -> Out + 'static> ScanStepCall<Acc, In>
    for OpaqueScanStep<F>
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, acc: &mut Acc, input: In) -> Out {
        (self.f)(world, acc, input)
    }
}

impl<Acc, In, Out, F: FnMut(&mut World, &mut Acc, In) -> Out + 'static>
    IntoScanStep<Acc, In, Out, Opaque> for F
{
    type Step = OpaqueScanStep<F>;

    fn into_scan_step(self, _registry: &Registry) -> Self::Step {
        OpaqueScanStep {
            f: self,
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// resolve_scan_step — pre-resolve a scan step for manual dispatch
// =============================================================================

/// Resolve a scan step for manual dispatch.
///
/// Returns a closure with pre-resolved [`Param`] state. Scan variant
/// of [`resolve_step`] with an additional `&mut Acc` accumulator.
pub fn resolve_scan_step<Acc, In, Out, Params, S: IntoScanStep<Acc, In, Out, Params>>(
    f: S,
    registry: &Registry,
) -> impl FnMut(&mut World, &mut Acc, In) -> Out + use<Acc, In, Out, Params, S> {
    let mut resolved = f.into_scan_step(registry);
    move |world: &mut World, acc: &mut Acc, input: In| resolved.call(world, acc, input)
}

// =============================================================================
// RefScanStepCall / IntoRefScanStep — scan step taking &In
// =============================================================================

/// Internal: callable trait for resolved scan steps taking input by reference.
///
/// DAG variant of [`ScanStepCall`] — each step borrows its input.
#[doc(hidden)]
pub trait RefScanStepCall<Acc, In> {
    /// The output type of this ref-scan step.
    type Out;
    /// Call this scan step with a world reference, accumulator, and borrowed input.
    fn call(&mut self, world: &mut World, acc: &mut Acc, input: &In) -> Self::Out;
}

/// Converts a function into a pre-resolved ref-scan step with persistent state.
///
/// Same three-tier resolution as [`IntoRefStep`]:
///
/// | Params | Function shape | Example |
/// |--------|---------------|---------|
/// | `()` | `FnMut(&mut Acc, &In) -> Out` | `\|acc, trade: &Trade\| { ... }` |
/// | `(P0,)...(P0..P7,)` | `fn(Params..., &mut Acc, &In) -> Out` | `fn vwap(c: Res<Config>, acc: &mut State, t: &Trade) -> Option<f64>` |
/// | [`Opaque`] | `FnMut(&mut World, &mut Acc, &In) -> Out` | `\|w: &mut World, acc: &mut u64, t: &Trade\| { ... }` |
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a reference scan step",
    note = "reference scan steps take `&mut Accumulator` as first param, then resources, then `&In` last",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoRefScanStep<Acc, In, Out, Params> {
    /// The concrete resolved ref-scan step type.
    type Step: RefScanStepCall<Acc, In, Out = Out>;

    /// Resolve Param state from the registry and produce a ref-scan step.
    fn into_ref_scan_step(self, registry: &Registry) -> Self::Step;
}

// -- Arity 0: FnMut(&mut Acc, &In) -> Out — closures work -------------------

impl<Acc, In, Out, F: FnMut(&mut Acc, &In) -> Out + 'static> RefScanStepCall<Acc, In>
    for Step<F, ()>
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, _world: &mut World, acc: &mut Acc, input: &In) -> Out {
        (self.f)(acc, input)
    }
}

impl<Acc, In, Out, F: FnMut(&mut Acc, &In) -> Out + 'static> IntoRefScanStep<Acc, In, Out, ()>
    for F
{
    type Step = Step<F, ()>;

    fn into_ref_scan_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// -- Arities 1-8: named functions with Param resolution ----------------------

macro_rules! impl_into_ref_scan_step {
    ($($P:ident),+) => {
        impl<Acc, In, Out, F: 'static, $($P: Param + 'static),+>
            RefScanStepCall<Acc, In> for Step<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &mut Acc, &In) -> Out +
                FnMut($($P::Item<'a>,)+ &mut Acc, &In) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, acc: &mut Acc, input: &In) -> Out {
                fn call_inner<$($P,)+ Accumulator, Input: ?Sized, Output>(
                    mut f: impl FnMut($($P,)+ &mut Accumulator, &Input) -> Output,
                    $($P: $P,)+
                    acc: &mut Accumulator,
                    input: &Input,
                ) -> Output {
                    f($($P,)+ acc, input)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ acc, input)
            }
        }

        impl<Acc, In, Out, F: 'static, $($P: Param + 'static),+>
            IntoRefScanStep<Acc, In, Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &mut Acc, &In) -> Out +
                FnMut($($P::Item<'a>,)+ &mut Acc, &In) -> Out,
        {
            type Step = Step<F, ($($P,)+)>;

            fn into_ref_scan_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_ref_scan_step);

// =============================================================================
// No-event RefScanStep — IntoRefScanStep<Acc, (), Out, _> without `&()` input
// =============================================================================

// Arity 0: fn(&mut Acc) -> Out
impl<Acc, Out, F: FnMut(&mut Acc) -> Out + 'static> RefScanStepCall<Acc, ()>
    for Step<NoEvent<F>, ()>
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, _world: &mut World, acc: &mut Acc, _input: &()) -> Out {
        (self.f.0)(acc)
    }
}

impl<Acc, Out, F: FnMut(&mut Acc) -> Out + 'static> IntoRefScanStep<Acc, (), Out, NoEvent<F>>
    for F
{
    type Step = Step<NoEvent<F>, ()>;

    fn into_ref_scan_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: NoEvent(self),
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_into_ref_scan_step_no_event {
    ($($P:ident),+) => {
        impl<Acc, Out, F: 'static, $($P: Param + 'static),+>
            RefScanStepCall<Acc, ()> for Step<NoEvent<F>, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &mut Acc) -> Out +
                FnMut($($P::Item<'a>,)+ &mut Acc) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, world: &mut World, acc: &mut Acc, _input: &()) -> Out {
                fn call_inner<$($P,)+ Accumulator, Output>(
                    mut f: impl FnMut($($P,)+ &mut Accumulator) -> Output,
                    $($P: $P,)+
                    acc: &mut Accumulator,
                ) -> Output {
                    f($($P,)+ acc)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f.0, $($P,)+ acc)
            }
        }

        impl<Acc, Out, F: 'static, $($P: Param + 'static),+>
            IntoRefScanStep<Acc, (), Out, ($($P,)+)> for NoEvent<F>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ &mut Acc) -> Out +
                FnMut($($P::Item<'a>,)+ &mut Acc) -> Out,
        {
            type Step = Step<NoEvent<F>, ($($P,)+)>;

            fn into_ref_scan_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_ref_scan_step_no_event);

// -- Opaque: FnMut(&mut World, &mut Acc, &In) -> Out ------------------------

/// Internal: wrapper for opaque closures used as ref-scan steps.
#[doc(hidden)]
pub struct OpaqueRefScanStep<F> {
    f: F,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

impl<Acc, In, Out, F: FnMut(&mut World, &mut Acc, &In) -> Out + 'static> RefScanStepCall<Acc, In>
    for OpaqueRefScanStep<F>
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, acc: &mut Acc, input: &In) -> Out {
        (self.f)(world, acc, input)
    }
}

impl<Acc, In, Out, F: FnMut(&mut World, &mut Acc, &In) -> Out + 'static>
    IntoRefScanStep<Acc, In, Out, Opaque> for F
{
    type Step = OpaqueRefScanStep<F>;

    fn into_ref_scan_step(self, _registry: &Registry) -> Self::Step {
        OpaqueRefScanStep {
            f: self,
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// resolve_ref_scan_step — pre-resolve a ref-scan step for manual dispatch
// =============================================================================

/// Resolve a ref-scan step for manual dispatch.
///
/// Returns a closure with pre-resolved [`Param`] state. Reference-input
/// counterpart of [`resolve_scan_step`].
pub fn resolve_ref_scan_step<Acc, In, Out, Params, S: IntoRefScanStep<Acc, In, Out, Params>>(
    f: S,
    registry: &Registry,
) -> impl FnMut(&mut World, &mut Acc, &In) -> Out + use<Acc, In, Out, Params, S> {
    let mut resolved = f.into_ref_scan_step(registry);
    move |world: &mut World, acc: &mut Acc, input: &In| resolved.call(world, acc, input)
}

// =============================================================================
// SplatCall / IntoSplatStep — splat step dispatch (tuple destructuring)
// =============================================================================
//
// Splat traits mirror StepCall/IntoStep but accept multiple owned values
// instead of a single input. This lets `.splat()` destructure a tuple
// output into individual function arguments for the next step.
//
// One trait pair per arity (2-5). Past 5, use a named struct.

// -- Splat 2 ------------------------------------------------------------------

/// Internal: callable trait for resolved 2-splat steps.
#[doc(hidden)]
pub trait SplatCall2<A, B> {
    /// Output type of this splat step.
    type Out;
    fn call_splat(&mut self, world: &mut World, a: A, b: B) -> Self::Out;
}

/// Converts a named function into a resolved 2-splat step.
#[doc(hidden)]
pub trait IntoSplatStep2<A, B, Out, Params> {
    type Step: SplatCall2<A, B, Out = Out>;
    fn into_splat_step(self, registry: &Registry) -> Self::Step;
}

impl<A, B, Out, F: FnMut(A, B) -> Out + 'static> SplatCall2<A, B> for Step<F, ()> {
    type Out = Out;
    #[inline(always)]
    fn call_splat(&mut self, _world: &mut World, a: A, b: B) -> Out {
        (self.f)(a, b)
    }
}

impl<A, B, Out, F: FnMut(A, B) -> Out + 'static> IntoSplatStep2<A, B, Out, ()> for F {
    type Step = Step<F, ()>;
    fn into_splat_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_splat2_step {
    ($($P:ident),+) => {
        impl<A, B, Out, F: 'static, $($P: Param + 'static),+>
            SplatCall2<A, B> for Step<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ A, B) -> Out +
                FnMut($($P::Item<'a>,)+ A, B) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call_splat(&mut self, world: &mut World, a: A, b: B) -> Out {
                fn call_inner<$($P,)+ IA, IB, Output>(
                    mut f: impl FnMut($($P,)+ IA, IB) -> Output,
                    $($P: $P,)+
                    a: IA, b: IB,
                ) -> Output {
                    f($($P,)+ a, b)
                }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ a, b)
            }
        }

        impl<A, B, Out, F: 'static, $($P: Param + 'static),+>
            IntoSplatStep2<A, B, Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ A, B) -> Out +
                FnMut($($P::Item<'a>,)+ A, B) -> Out,
        {
            type Step = Step<F, ($($P,)+)>;

            fn into_splat_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

// -- Splat 3 ------------------------------------------------------------------

/// Internal: callable trait for resolved 3-splat steps.
#[doc(hidden)]
pub trait SplatCall3<A, B, C> {
    /// Output type of this splat step.
    type Out;
    fn call_splat(&mut self, world: &mut World, a: A, b: B, c: C) -> Self::Out;
}

/// Converts a named function into a resolved 3-splat step.
#[doc(hidden)]
pub trait IntoSplatStep3<A, B, C, Out, Params> {
    type Step: SplatCall3<A, B, C, Out = Out>;
    fn into_splat_step(self, registry: &Registry) -> Self::Step;
}

impl<A, B, C, Out, F: FnMut(A, B, C) -> Out + 'static> SplatCall3<A, B, C> for Step<F, ()> {
    type Out = Out;
    #[inline(always)]
    fn call_splat(&mut self, _world: &mut World, a: A, b: B, c: C) -> Out {
        (self.f)(a, b, c)
    }
}

impl<A, B, C, Out, F: FnMut(A, B, C) -> Out + 'static> IntoSplatStep3<A, B, C, Out, ()> for F {
    type Step = Step<F, ()>;
    fn into_splat_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_splat3_step {
    ($($P:ident),+) => {
        impl<A, B, C, Out, F: 'static, $($P: Param + 'static),+>
            SplatCall3<A, B, C> for Step<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ A, B, C) -> Out +
                FnMut($($P::Item<'a>,)+ A, B, C) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call_splat(&mut self, world: &mut World, a: A, b: B, c: C) -> Out {
                fn call_inner<$($P,)+ IA, IB, IC, Output>(
                    mut f: impl FnMut($($P,)+ IA, IB, IC) -> Output,
                    $($P: $P,)+
                    a: IA, b: IB, c: IC,
                ) -> Output {
                    f($($P,)+ a, b, c)
                }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ a, b, c)
            }
        }

        impl<A, B, C, Out, F: 'static, $($P: Param + 'static),+>
            IntoSplatStep3<A, B, C, Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut($($P,)+ A, B, C) -> Out +
                FnMut($($P::Item<'a>,)+ A, B, C) -> Out,
        {
            type Step = Step<F, ($($P,)+)>;

            fn into_splat_step(self, registry: &Registry) -> Self::Step {
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
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

// -- Splat 4 ------------------------------------------------------------------

/// Internal: callable trait for resolved 4-splat steps.
#[doc(hidden)]
pub trait SplatCall4<A, B, C, D> {
    /// Output type of this splat step.
    type Out;
    fn call_splat(&mut self, world: &mut World, a: A, b: B, c: C, d: D) -> Self::Out;
}

/// Converts a named function into a resolved 4-splat step.
#[doc(hidden)]
pub trait IntoSplatStep4<A, B, C, D, Out, Params> {
    type Step: SplatCall4<A, B, C, D, Out = Out>;
    fn into_splat_step(self, registry: &Registry) -> Self::Step;
}

impl<A, B, C, D, Out, F: FnMut(A, B, C, D) -> Out + 'static> SplatCall4<A, B, C, D>
    for Step<F, ()>
{
    type Out = Out;
    #[inline(always)]
    fn call_splat(&mut self, _world: &mut World, a: A, b: B, c: C, d: D) -> Out {
        (self.f)(a, b, c, d)
    }
}

impl<A, B, C, D, Out, F: FnMut(A, B, C, D) -> Out + 'static> IntoSplatStep4<A, B, C, D, Out, ()>
    for F
{
    type Step = Step<F, ()>;
    fn into_splat_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_splat4_step {
    ($($P:ident),+) => {
        impl<A, B, C, D, Out, F: 'static, $($P: Param + 'static),+>
            SplatCall4<A, B, C, D> for Step<F, ($($P,)+)>
        where for<'a> &'a mut F:
            FnMut($($P,)+ A, B, C, D) -> Out +
            FnMut($($P::Item<'a>,)+ A, B, C, D) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call_splat(&mut self, world: &mut World, a: A, b: B, c: C, d: D) -> Out {
                fn call_inner<$($P,)+ IA, IB, IC, ID, Output>(
                    mut f: impl FnMut($($P,)+ IA, IB, IC, ID) -> Output,
                    $($P: $P,)+ a: IA, b: IB, c: IC, d: ID,
                ) -> Output { f($($P,)+ a, b, c, d) }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ a, b, c, d)
            }
        }
        impl<A, B, C, D, Out, F: 'static, $($P: Param + 'static),+>
            IntoSplatStep4<A, B, C, D, Out, ($($P,)+)> for F
        where for<'a> &'a mut F:
            FnMut($($P,)+ A, B, C, D) -> Out +
            FnMut($($P::Item<'a>,)+ A, B, C, D) -> Out,
        {
            type Step = Step<F, ($($P,)+)>;
            fn into_splat_step(self, registry: &Registry) -> Self::Step {
                let state = <($($P,)+) as Param>::init(registry);
                { #[allow(non_snake_case)] let ($($P,)+) = &state;
                  registry.check_access(&[$((<$P as Param>::resource_id($P), std::any::type_name::<$P>()),)+]); }
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

// -- Splat 5 ------------------------------------------------------------------

/// Internal: callable trait for resolved 5-splat steps.
#[doc(hidden)]
pub trait SplatCall5<A, B, C, D, E> {
    /// Output type of this splat step.
    type Out;
    #[allow(clippy::many_single_char_names)]
    fn call_splat(&mut self, world: &mut World, a: A, b: B, c: C, d: D, e: E) -> Self::Out;
}

/// Converts a named function into a resolved 5-splat step.
#[doc(hidden)]
pub trait IntoSplatStep5<A, B, C, D, E, Out, Params> {
    type Step: SplatCall5<A, B, C, D, E, Out = Out>;
    fn into_splat_step(self, registry: &Registry) -> Self::Step;
}

impl<A, B, C, D, E, Out, F: FnMut(A, B, C, D, E) -> Out + 'static> SplatCall5<A, B, C, D, E>
    for Step<F, ()>
{
    type Out = Out;
    #[inline(always)]
    #[allow(clippy::many_single_char_names)]
    fn call_splat(&mut self, _world: &mut World, a: A, b: B, c: C, d: D, e: E) -> Out {
        (self.f)(a, b, c, d, e)
    }
}

impl<A, B, C, D, E, Out, F: FnMut(A, B, C, D, E) -> Out + 'static>
    IntoSplatStep5<A, B, C, D, E, Out, ()> for F
{
    type Step = Step<F, ()>;
    fn into_splat_step(self, registry: &Registry) -> Self::Step {
        Step {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

macro_rules! impl_splat5_step {
    ($($P:ident),+) => {
        impl<A, B, C, D, E, Out, F: 'static, $($P: Param + 'static),+>
            SplatCall5<A, B, C, D, E> for Step<F, ($($P,)+)>
        where for<'a> &'a mut F:
            FnMut($($P,)+ A, B, C, D, E) -> Out +
            FnMut($($P::Item<'a>,)+ A, B, C, D, E) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case, clippy::many_single_char_names)]
            fn call_splat(&mut self, world: &mut World, a: A, b: B, c: C, d: D, e: E) -> Out {
                fn call_inner<$($P,)+ IA, IB, IC, ID, IE, Output>(
                    mut f: impl FnMut($($P,)+ IA, IB, IC, ID, IE) -> Output,
                    $($P: $P,)+ a: IA, b: IB, c: IC, d: ID, e: IE,
                ) -> Output { f($($P,)+ a, b, c, d, e) }
                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P,)+ a, b, c, d, e)
            }
        }
        impl<A, B, C, D, E, Out, F: 'static, $($P: Param + 'static),+>
            IntoSplatStep5<A, B, C, D, E, Out, ($($P,)+)> for F
        where for<'a> &'a mut F:
            FnMut($($P,)+ A, B, C, D, E) -> Out +
            FnMut($($P::Item<'a>,)+ A, B, C, D, E) -> Out,
        {
            type Step = Step<F, ($($P,)+)>;
            fn into_splat_step(self, registry: &Registry) -> Self::Step {
                let state = <($($P,)+) as Param>::init(registry);
                { #[allow(non_snake_case)] let ($($P,)+) = &state;
                  registry.check_access(&[$((<$P as Param>::resource_id($P), std::any::type_name::<$P>()),)+]); }
                Step { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_splat2_step);
all_tuples!(impl_splat3_step);
all_tuples!(impl_splat4_step);
all_tuples!(impl_splat5_step);

// =============================================================================
// ChainCall — named chain dispatch trait
// =============================================================================

/// Trait for pipeline chain nodes. Each node transforms input through
/// the chain, producing an output. `In` appears only on the trait impl,
/// not on the implementing struct — this preserves HRTB compatibility
/// so `Pipeline<Chain>` can satisfy `for<'a> Handler<&'a T>`.
#[doc(hidden)]
pub trait ChainCall<In> {
    /// The output type of this chain node.
    type Out;
    /// Execute the chain on the given input.
    fn call(&mut self, world: &mut World, input: In) -> Self::Out;
}

// =============================================================================
// Chain nodes — named types for HRTB-compatible pipeline composition
// =============================================================================
//
// Each combinator gets a named struct following the iterator adapter pattern
// (like `Map<I, F>`, `Filter<I, P>`). `In` appears only on the `ChainCall<In>`
// trait impl, never on the struct — this is what enables HRTB boxing.

/// Identity passthrough node. Used as the initial chain element.
#[doc(hidden)]
pub struct IdentityNode;

impl<In> ChainCall<In> for IdentityNode {
    type Out = In;
    #[inline(always)]
    fn call(&mut self, _world: &mut World, input: In) -> In {
        input
    }
}

// -- Core (any Out) ----------------------------------------------------------

/// Chain node for `.then()` — transforms output via a resolved step.
#[doc(hidden)]
pub struct ThenNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, Prev, S> ChainCall<In> for ThenNode<Prev, S>
where
    Prev: ChainCall<In>,
    S: StepCall<Prev::Out>,
{
    type Out = S::Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> S::Out {
        let mid = self.prev.call(world, input);
        self.step.call(world, mid)
    }
}

/// Chain node for `.tap()` — side effect via `&Out`, value passes through.
#[doc(hidden)]
pub struct TapNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, Prev, S> ChainCall<In> for TapNode<Prev, S>
where
    Prev: ChainCall<In>,
    S: RefStepCall<Prev::Out, Out = ()>,
{
    type Out = Prev::Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Prev::Out {
        let val = self.prev.call(world, input);
        self.step.call(world, &val);
        val
    }
}

/// Chain node for `.guard()` — wraps output in `Option` based on predicate.
#[doc(hidden)]
pub struct GuardNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, Prev, S> ChainCall<In> for GuardNode<Prev, S>
where
    Prev: ChainCall<In>,
    S: RefStepCall<Prev::Out, Out = bool>,
{
    type Out = Option<Prev::Out>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<Prev::Out> {
        let val = self.prev.call(world, input);
        if self.step.call(world, &val) {
            Some(val)
        } else {
            None
        }
    }
}

/// Chain node for `.dedup()` — suppresses consecutive unchanged values.
#[doc(hidden)]
pub struct DedupNode<Prev, T> {
    pub(crate) prev: Prev,
    pub(crate) last: Option<T>,
}

impl<In, T: PartialEq + Clone, Prev: ChainCall<In, Out = T>> ChainCall<In> for DedupNode<Prev, T> {
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<T> {
        let val = self.prev.call(world, input);
        if self.last.as_ref() == Some(&val) {
            None
        } else {
            self.last = Some(val.clone());
            Some(val)
        }
    }
}

/// Chain node for `.scan()` — transforms with persistent accumulator.
#[doc(hidden)]
pub struct ScanNode<Prev, S, Acc> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) acc: Acc,
}

impl<In, Prev, S, Acc> ChainCall<In> for ScanNode<Prev, S, Acc>
where
    Prev: ChainCall<In>,
    S: ScanStepCall<Acc, Prev::Out>,
{
    type Out = S::Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> S::Out {
        let val = self.prev.call(world, input);
        self.step.call(world, &mut self.acc, val)
    }
}

/// Chain node for `.dispatch()` — feeds output to a [`Handler`].
#[doc(hidden)]
pub struct DispatchNode<Prev, H> {
    pub(crate) prev: Prev,
    pub(crate) handler: H,
}

impl<In, Prev, H> ChainCall<In> for DispatchNode<Prev, H>
where
    Prev: ChainCall<In>,
    H: Handler<Prev::Out>,
{
    type Out = ();
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) {
        let out = self.prev.call(world, input);
        self.handler.run(world, out);
    }
}

/// Chain node for `.tee()` — runs side-effect chain on `&Out`, passes value through.
#[doc(hidden)]
pub struct TeeNode<Prev, C> {
    pub(crate) prev: Prev,
    pub(crate) side: C,
}

impl<In, Prev, C> ChainCall<In> for TeeNode<Prev, C>
where
    Prev: ChainCall<In>,
    Prev::Out: 'static,
    C: for<'a> ChainCall<&'a Prev::Out, Out = ()>,
{
    type Out = Prev::Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Prev::Out {
        let val = self.prev.call(world, input);
        self.side.call(world, &val);
        val
    }
}

/// Chain node for `.route()` — binary conditional dispatch.
#[doc(hidden)]
pub struct RouteNode<Prev, P, C0, C1> {
    pub(crate) prev: Prev,
    pub(crate) pred: P,
    pub(crate) on_true: C0,
    pub(crate) on_false: C1,
}

impl<In, Prev, P, C0, C1> ChainCall<In> for RouteNode<Prev, P, C0, C1>
where
    Prev: ChainCall<In>,
    P: RefStepCall<Prev::Out, Out = bool>,
    C0: ChainCall<Prev::Out>,
    C1: ChainCall<Prev::Out, Out = C0::Out>,
{
    type Out = C0::Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> C0::Out {
        let val = self.prev.call(world, input);
        if self.pred.call(world, &val) {
            self.on_true.call(world, val)
        } else {
            self.on_false.call(world, val)
        }
    }
}

// -- Option<T> nodes ---------------------------------------------------------

/// Chain node for `.map()` on `Option<T>`.
#[doc(hidden)]
pub struct MapOptionNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, Prev, S> ChainCall<In> for MapOptionNode<Prev, S>
where
    Prev: ChainCall<In, Out = Option<T>>,
    S: StepCall<T>,
{
    type Out = Option<S::Out>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<S::Out> {
        self.prev
            .call(world, input)
            .map(|val| self.step.call(world, val))
    }
}

/// Chain node for `.filter()` on `Option<T>`.
#[doc(hidden)]
pub struct FilterNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, Prev, S> ChainCall<In> for FilterNode<Prev, S>
where
    Prev: ChainCall<In, Out = Option<T>>,
    S: RefStepCall<T, Out = bool>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<T> {
        self.prev
            .call(world, input)
            .filter(|val| self.step.call(world, val))
    }
}

/// Chain node for `.inspect()` on `Option<T>`.
#[doc(hidden)]
pub struct InspectOptionNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, Prev, S> ChainCall<In> for InspectOptionNode<Prev, S>
where
    Prev: ChainCall<In, Out = Option<T>>,
    S: RefStepCall<T, Out = ()>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<T> {
        self.prev
            .call(world, input)
            .inspect(|val| self.step.call(world, val))
    }
}

/// Chain node for `.and_then()` on `Option<T>`.
#[doc(hidden)]
pub struct AndThenNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, U, Prev, S> ChainCall<In> for AndThenNode<Prev, S>
where
    Prev: ChainCall<In, Out = Option<T>>,
    S: StepCall<T, Out = Option<U>>,
{
    type Out = Option<U>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<U> {
        self.prev
            .call(world, input)
            .and_then(|val| self.step.call(world, val))
    }
}

/// Chain node for `.on_none()` — side effect when `None`.
#[doc(hidden)]
pub struct OnNoneNode<Prev, P> {
    pub(crate) prev: Prev,
    pub(crate) producer: P,
}

impl<In, T, Prev, P> ChainCall<In> for OnNoneNode<Prev, P>
where
    Prev: ChainCall<In, Out = Option<T>>,
    P: ProducerCall<Out = ()>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<T> {
        let result = self.prev.call(world, input);
        if result.is_none() {
            self.producer.call(world);
        }
        result
    }
}

/// Chain node for `.ok_or()` — `Option<T>` → `Result<T, E>`.
#[doc(hidden)]
pub struct OkOrNode<Prev, E> {
    pub(crate) prev: Prev,
    pub(crate) err: E,
}

impl<In, T, E: Clone, Prev: ChainCall<In, Out = Option<T>>> ChainCall<In> for OkOrNode<Prev, E> {
    type Out = Result<T, E>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<T, E> {
        self.prev.call(world, input).ok_or_else(|| self.err.clone())
    }
}

/// Chain node for `.ok_or_else()` — `Option<T>` → `Result<T, E>`.
#[doc(hidden)]
pub struct OkOrElseNode<Prev, P> {
    pub(crate) prev: Prev,
    pub(crate) producer: P,
}

impl<In, T, E, Prev, P> ChainCall<In> for OkOrElseNode<Prev, P>
where
    Prev: ChainCall<In, Out = Option<T>>,
    P: ProducerCall<Out = E>,
{
    type Out = Result<T, E>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<T, E> {
        self.prev
            .call(world, input)
            .ok_or_else(|| self.producer.call(world))
    }
}

/// Chain node for `.unwrap_or()` on `Option<T>`.
#[doc(hidden)]
pub struct UnwrapOrOptionNode<Prev, T> {
    pub(crate) prev: Prev,
    pub(crate) default: T,
}

impl<In, T: Clone, Prev: ChainCall<In, Out = Option<T>>> ChainCall<In>
    for UnwrapOrOptionNode<Prev, T>
{
    type Out = T;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> T {
        self.prev
            .call(world, input)
            .unwrap_or_else(|| self.default.clone())
    }
}

/// Chain node for `.unwrap_or_else()` on `Option<T>`.
#[doc(hidden)]
pub struct UnwrapOrElseOptionNode<Prev, P> {
    pub(crate) prev: Prev,
    pub(crate) producer: P,
}

impl<In, T, Prev, P> ChainCall<In> for UnwrapOrElseOptionNode<Prev, P>
where
    Prev: ChainCall<In, Out = Option<T>>,
    P: ProducerCall<Out = T>,
{
    type Out = T;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> T {
        self.prev
            .call(world, input)
            .unwrap_or_else(|| self.producer.call(world))
    }
}

// -- Result<T, E> nodes ------------------------------------------------------

/// Chain node for `.map()` on `Result<T, E>`.
#[doc(hidden)]
pub struct MapResultNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, E, Prev, S> ChainCall<In> for MapResultNode<Prev, S>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: StepCall<T>,
{
    type Out = Result<S::Out, E>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<S::Out, E> {
        self.prev
            .call(world, input)
            .map(|val| self.step.call(world, val))
    }
}

/// Chain node for `.and_then()` on `Result<T, E>`.
#[doc(hidden)]
pub struct AndThenResultNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, U, E, Prev, S> ChainCall<In> for AndThenResultNode<Prev, S>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: StepCall<T, Out = Result<U, E>>,
{
    type Out = Result<U, E>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<U, E> {
        self.prev
            .call(world, input)
            .and_then(|val| self.step.call(world, val))
    }
}

/// Chain node for `.catch()` — `Result<T, E>` → `Option<T>`.
#[doc(hidden)]
pub struct CatchNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, E, Prev, S> ChainCall<In> for CatchNode<Prev, S>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: StepCall<E, Out = ()>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<T> {
        match self.prev.call(world, input) {
            Ok(val) => Some(val),
            Err(err) => {
                self.step.call(world, err);
                None
            }
        }
    }
}

/// Chain node for `.map_err()`.
#[doc(hidden)]
pub struct MapErrNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, E, Prev, S> ChainCall<In> for MapErrNode<Prev, S>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: StepCall<E>,
{
    type Out = Result<T, S::Out>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<T, S::Out> {
        self.prev
            .call(world, input)
            .map_err(|err| self.step.call(world, err))
    }
}

/// Chain node for `.or_else()`.
#[doc(hidden)]
pub struct OrElseNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, E, E2, Prev, S> ChainCall<In> for OrElseNode<Prev, S>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: StepCall<E, Out = Result<T, E2>>,
{
    type Out = Result<T, E2>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<T, E2> {
        self.prev
            .call(world, input)
            .or_else(|err| self.step.call(world, err))
    }
}

/// Chain node for `.inspect()` on `Result<T, E>`.
#[doc(hidden)]
pub struct InspectResultNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, E, Prev, S> ChainCall<In> for InspectResultNode<Prev, S>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: RefStepCall<T, Out = ()>,
{
    type Out = Result<T, E>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<T, E> {
        self.prev
            .call(world, input)
            .inspect(|val| self.step.call(world, val))
    }
}

/// Chain node for `.inspect_err()`.
#[doc(hidden)]
pub struct InspectErrNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, E, Prev, S> ChainCall<In> for InspectErrNode<Prev, S>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: RefStepCall<E, Out = ()>,
{
    type Out = Result<T, E>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<T, E> {
        self.prev
            .call(world, input)
            .inspect_err(|err| self.step.call(world, err))
    }
}

/// Chain node for `.ok()` — `Result<T, E>` → `Option<T>`.
#[doc(hidden)]
pub struct OkResultNode<Prev> {
    pub(crate) prev: Prev,
}

impl<In, T, E, Prev: ChainCall<In, Out = Result<T, E>>> ChainCall<In> for OkResultNode<Prev> {
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<T> {
        self.prev.call(world, input).ok()
    }
}

/// Chain node for `.unwrap_or()` on `Result<T, E>`.
#[doc(hidden)]
pub struct UnwrapOrResultNode<Prev, T> {
    pub(crate) prev: Prev,
    pub(crate) default: T,
}

impl<In, T: Clone, E, Prev: ChainCall<In, Out = Result<T, E>>> ChainCall<In>
    for UnwrapOrResultNode<Prev, T>
{
    type Out = T;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> T {
        self.prev
            .call(world, input)
            .unwrap_or_else(|_| self.default.clone())
    }
}

/// Chain node for `.unwrap_or_else()` on `Result<T, E>`.
#[doc(hidden)]
pub struct UnwrapOrElseResultNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, E, Prev, S> ChainCall<In> for UnwrapOrElseResultNode<Prev, S>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: StepCall<E, Out = T>,
{
    type Out = T;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> T {
        match self.prev.call(world, input) {
            Ok(val) => val,
            Err(err) => self.step.call(world, err),
        }
    }
}

// -- Bool nodes --------------------------------------------------------------

/// Chain node for `.not()`.
#[doc(hidden)]
pub struct NotNode<Prev> {
    pub(crate) prev: Prev,
}

impl<In, Prev: ChainCall<In, Out = bool>> ChainCall<In> for NotNode<Prev> {
    type Out = bool;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> bool {
        !self.prev.call(world, input)
    }
}

/// Chain node for `.and()` on bool.
#[doc(hidden)]
pub struct AndBoolNode<Prev, P> {
    pub(crate) prev: Prev,
    pub(crate) producer: P,
}

impl<In, Prev, P> ChainCall<In> for AndBoolNode<Prev, P>
where
    Prev: ChainCall<In, Out = bool>,
    P: ProducerCall<Out = bool>,
{
    type Out = bool;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> bool {
        self.prev.call(world, input) && self.producer.call(world)
    }
}

/// Chain node for `.or()` on bool.
#[doc(hidden)]
pub struct OrBoolNode<Prev, P> {
    pub(crate) prev: Prev,
    pub(crate) producer: P,
}

impl<In, Prev, P> ChainCall<In> for OrBoolNode<Prev, P>
where
    Prev: ChainCall<In, Out = bool>,
    P: ProducerCall<Out = bool>,
{
    type Out = bool;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> bool {
        self.prev.call(world, input) || self.producer.call(world)
    }
}

/// Chain node for `.xor()` on bool.
#[doc(hidden)]
pub struct XorBoolNode<Prev, P> {
    pub(crate) prev: Prev,
    pub(crate) producer: P,
}

impl<In, Prev, P> ChainCall<In> for XorBoolNode<Prev, P>
where
    Prev: ChainCall<In, Out = bool>,
    P: ProducerCall<Out = bool>,
{
    type Out = bool;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> bool {
        self.prev.call(world, input) ^ self.producer.call(world)
    }
}

// -- Cloned nodes ------------------------------------------------------------

/// Chain node for `.cloned()` on `&T`.
#[doc(hidden)]
pub struct ClonedNode<Prev> {
    pub(crate) prev: Prev,
}

impl<'a, In, T: Clone + 'a, Prev: ChainCall<In, Out = &'a T>> ChainCall<In> for ClonedNode<Prev> {
    type Out = T;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> T {
        T::clone(self.prev.call(world, input))
    }
}

/// Chain node for `.cloned()` on `Option<&T>`.
#[doc(hidden)]
pub struct ClonedOptionNode<Prev> {
    pub(crate) prev: Prev,
}

impl<'a, In, T: Clone + 'a, Prev: ChainCall<In, Out = Option<&'a T>>> ChainCall<In>
    for ClonedOptionNode<Prev>
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<T> {
        self.prev.call(world, input).cloned()
    }
}

/// Chain node for `.cloned()` on `Result<&T, E>`.
#[doc(hidden)]
pub struct ClonedResultNode<Prev> {
    pub(crate) prev: Prev,
}

impl<'a, In, T: Clone + 'a, E, Prev: ChainCall<In, Out = Result<&'a T, E>>> ChainCall<In>
    for ClonedResultNode<Prev>
{
    type Out = Result<T, E>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<T, E> {
        self.prev.call(world, input).cloned()
    }
}

// -- DAG-specific nodes (borrow intermediate) --------------------------------
//
// DAG steps borrow `&Prev::Out` instead of consuming by value. These nodes
// parallel the pipeline nodes above but use `for<'a> StepCall<&'a T>` bounds
// and HRTB arm chains (`for<'a> ChainCall<&'a T>`).

/// Chain node for DAG `.then()` — borrows intermediate output for next step.
///
/// Unlike pipeline's [`ThenNode`] which passes by value, this borrows `&Prev::Out`
/// for the step. Used for DAG chains where intermediates are owned and borrowed.
#[doc(hidden)]
pub struct DagThenNode<Prev, S, NewOut> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> NewOut>,
}

impl<In, Prev, S, NewOut: 'static> ChainCall<In> for DagThenNode<Prev, S, NewOut>
where
    Prev: ChainCall<In>,
    Prev::Out: 'static,
    S: for<'a> StepCall<&'a Prev::Out, Out = NewOut>,
{
    type Out = NewOut;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> NewOut {
        let out = self.prev.call(world, input);
        self.step.call(world, &out)
    }
}

/// Chain node for DAG `.scan()` — scan with borrowed input.
///
/// Like [`ScanNode`] but the step receives `&Prev::Out` via [`RefScanStepCall`].
#[doc(hidden)]
pub struct RefScanNode<Prev, S, Acc> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) acc: Acc,
}

impl<In, Prev, S, Acc> ChainCall<In> for RefScanNode<Prev, S, Acc>
where
    Prev: ChainCall<In>,
    S: RefScanStepCall<Acc, Prev::Out>,
{
    type Out = S::Out;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> S::Out {
        let val = self.prev.call(world, input);
        self.step.call(world, &mut self.acc, &val)
    }
}

/// Chain node for DAG `.route()` — arms borrow `&Prev::Out` (HRTB).
///
/// Unlike pipeline's [`RouteNode`] which passes by value, this borrows
/// the value for the predicate and arms. Arms satisfy `for<'a> ChainCall<&'a Out>`.
#[doc(hidden)]
pub struct DagRouteNode<Prev, P, C0, C1, NewOut> {
    pub(crate) prev: Prev,
    pub(crate) pred: P,
    pub(crate) on_true: C0,
    pub(crate) on_false: C1,
    pub(crate) _out: PhantomData<fn() -> NewOut>,
}

impl<In, Prev, P, C0, C1, NewOut> ChainCall<In> for DagRouteNode<Prev, P, C0, C1, NewOut>
where
    Prev: ChainCall<In>,
    Prev::Out: 'static,
    P: RefStepCall<Prev::Out, Out = bool>,
    C0: for<'a> ChainCall<&'a Prev::Out, Out = NewOut>,
    C1: for<'a> ChainCall<&'a Prev::Out, Out = NewOut>,
{
    type Out = NewOut;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> NewOut {
        let val = self.prev.call(world, input);
        if self.pred.call(world, &val) {
            self.on_true.call(world, &val)
        } else {
            self.on_false.call(world, &val)
        }
    }
}

/// Chain node for DAG `.map()` on `Option<T>` — step borrows `&T`.
///
/// Like [`MapOptionNode`] but the step receives `&T` instead of `T` by value.
#[doc(hidden)]
pub struct DagMapOptionNode<Prev, S, U> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> U>,
}

impl<In, T: 'static, U: 'static, Prev, S> ChainCall<In> for DagMapOptionNode<Prev, S, U>
where
    Prev: ChainCall<In, Out = Option<T>>,
    S: for<'a> StepCall<&'a T, Out = U>,
{
    type Out = Option<U>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<U> {
        self.prev
            .call(world, input)
            .map(|ref val| self.step.call(world, val))
    }
}

/// Chain node for DAG `.and_then()` on `Option<T>` — step borrows `&T`.
#[doc(hidden)]
pub struct DagAndThenOptionNode<Prev, S, U> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> U>,
}

impl<In, T: 'static, U: 'static, Prev, S> ChainCall<In> for DagAndThenOptionNode<Prev, S, U>
where
    Prev: ChainCall<In, Out = Option<T>>,
    S: for<'a> StepCall<&'a T, Out = Option<U>>,
{
    type Out = Option<U>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<U> {
        self.prev
            .call(world, input)
            .and_then(|ref val| self.step.call(world, val))
    }
}

/// Chain node for DAG `.map()` on `Result<T, E>` — step borrows `&T`.
#[doc(hidden)]
pub struct DagMapResultNode<Prev, S, U> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> U>,
}

impl<In, T: 'static, E, U: 'static, Prev, S> ChainCall<In> for DagMapResultNode<Prev, S, U>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: for<'a> StepCall<&'a T, Out = U>,
{
    type Out = Result<U, E>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<U, E> {
        self.prev
            .call(world, input)
            .map(|ref val| self.step.call(world, val))
    }
}

/// Chain node for DAG `.and_then()` on `Result<T, E>` — step borrows `&T`.
#[doc(hidden)]
pub struct DagAndThenResultNode<Prev, S, U> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
    pub(crate) _out: PhantomData<fn() -> U>,
}

impl<In, T: 'static, E, U: 'static, Prev, S> ChainCall<In> for DagAndThenResultNode<Prev, S, U>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: for<'a> StepCall<&'a T, Out = Result<U, E>>,
{
    type Out = Result<U, E>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Result<U, E> {
        self.prev
            .call(world, input)
            .and_then(|ref val| self.step.call(world, val))
    }
}

/// Chain node for DAG `.catch()` on `Result<T, E>` — error handler borrows `&E`.
///
/// Like [`CatchNode`] but the step receives `&E` instead of consuming `E`.
#[doc(hidden)]
pub struct DagCatchNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<In, T, E: 'static, Prev, S> ChainCall<In> for DagCatchNode<Prev, S>
where
    Prev: ChainCall<In, Out = Result<T, E>>,
    S: for<'a> StepCall<&'a E, Out = ()>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) -> Option<T> {
        match self.prev.call(world, input) {
            Ok(val) => Some(val),
            Err(ref err) => {
                self.step.call(world, err);
                None
            }
        }
    }
}

// -- Terminal nodes ----------------------------------------------------------

/// Chain node for `build()` on `Option<()>` — discards the option wrapper.
#[doc(hidden)]
pub struct DiscardOptionNode<Prev> {
    pub(crate) prev: Prev,
}

impl<In, Prev: ChainCall<In, Out = Option<()>>> ChainCall<In> for DiscardOptionNode<Prev> {
    type Out = ();
    #[inline(always)]
    fn call(&mut self, world: &mut World, input: In) {
        let _ = self.prev.call(world, input);
    }
}

// =============================================================================
// PipelineBuilder — entry point
// =============================================================================

/// Entry point for building a pre-resolved step pipeline.
///
/// `In` is the pipeline input type. Call [`.then()`](Self::then) to add
/// the first step — a named function whose [`Param`] dependencies
/// are resolved from the registry at build time.
///
/// # Examples
///
/// ```
/// use nexus_rt::{WorldBuilder, Res, ResMut, PipelineBuilder, Handler, Resource};
///
/// #[derive(Resource)]
/// struct Factor(u64);
/// #[derive(Resource)]
/// struct Output(String);
///
/// let mut wb = WorldBuilder::new();
/// wb.register(Factor(10));
/// wb.register(Output(String::new()));
/// let mut world = wb.build();
///
/// fn double(factor: Res<Factor>, x: u32) -> u64 {
///     factor.0 * x as u64
/// }
/// fn store(mut out: ResMut<Output>, val: u64) {
///     out.0 = val.to_string();
/// }
///
/// let r = world.registry();
/// let mut pipeline = PipelineBuilder::<u32>::new()
///     .then(double, r)
///     .then(store, r)
///     .build();
///
/// pipeline.run(&mut world, 5);
/// assert_eq!(world.resource::<Output>().0.as_str(), "50");
/// ```
#[must_use = "a pipeline builder does nothing unless you chain steps and call .build()"]
pub struct PipelineBuilder<In>(PhantomData<fn(In)>);

impl<In> PipelineBuilder<In> {
    /// Create a new step pipeline entry point.
    pub fn new() -> Self {
        Self(PhantomData)
    }

    /// Add the first step. Params resolved from the registry.
    pub fn then<Out, Params, S: IntoStep<In, Out, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Out, ThenNode<IdentityNode, S::Step>> {
        PipelineChain {
            chain: ThenNode {
                prev: IdentityNode,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Add the first step as a scan with persistent accumulator.
    /// The step receives `&mut Acc` and the input, returning the output.
    /// State persists across invocations.
    pub fn scan<Acc, Out, Params, S>(
        self,
        initial: Acc,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Out, ScanNode<IdentityNode, S::Step, Acc>>
    where
        Acc: 'static,
        S: IntoScanStep<Acc, In, Out, Params>,
    {
        PipelineChain {
            chain: ScanNode {
                prev: IdentityNode,
                step: f.into_scan_step(registry),
                acc: initial,
            },
            _marker: PhantomData,
        }
    }
}

impl<In> Default for PipelineBuilder<In> {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// PipelineChain — typestate builder
// =============================================================================

/// Builder that composes pre-resolved pipeline steps via named chain nodes.
///
/// `In` is the pipeline's input type (fixed). `Out` is the current output.
/// `Chain` is the concrete chain type (nested named nodes, like iterator adapters).
///
/// Each combinator consumes `self`, wraps the previous chain in a new named
/// node, and returns a new `PipelineChain`. The compiler monomorphizes the
/// entire chain — zero virtual dispatch through steps. Named types (not
/// closures) preserve HRTB: `Pipeline<Chain>` can satisfy `for<'a> Handler<&'a T>`.
///
/// IntoStep-based methods (`.then()`, `.map()`, `.and_then()`, `.catch()`)
/// take `&Registry` to resolve Param state at build time. Closure-based
/// methods don't need the registry.
#[must_use = "pipeline chain does nothing until .build() is called"]
pub struct PipelineChain<In, Out, Chain> {
    pub(crate) chain: Chain,
    pub(crate) _marker: PhantomData<fn(In) -> Out>,
}

// =============================================================================
// Core — any Out
// =============================================================================

impl<In, Out, Chain: ChainCall<In, Out = Out>> PipelineChain<In, Out, Chain> {
    /// Add a step. Params resolved from the registry.
    pub fn then<NewOut, Params, S: IntoStep<Out, NewOut, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, NewOut, ThenNode<Chain, S::Step>> {
        PipelineChain {
            chain: ThenNode {
                prev: self.chain,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Run the pipeline directly. No boxing, no `'static` on `In`.
    pub fn run(&mut self, world: &mut World, input: In) -> Out {
        self.chain.call(world, input)
    }

    /// Dispatch pipeline output to a [`Handler<Out>`].
    ///
    /// Connects a pipeline's output to any handler — [`HandlerFn`](crate::HandlerFn),
    /// [`Callback`](crate::Callback), [`Pipeline`], or a combinator like
    /// [`fan_out!`](crate::fan_out).
    pub fn dispatch<H: Handler<Out>>(
        self,
        handler: H,
    ) -> PipelineChain<In, (), DispatchNode<Chain, H>> {
        PipelineChain {
            chain: DispatchNode {
                prev: self.chain,
                handler,
            },
            _marker: PhantomData,
        }
    }

    /// Conditionally wrap the output in `Option`. `Some(val)` if
    /// the predicate returns true, `None` otherwise.
    ///
    /// Enters Option-combinator land — follow with `.map()`,
    /// `.and_then()`, `.filter()`, `.unwrap_or()`, etc.
    ///
    /// # Common Mistakes
    ///
    /// Guard takes `&In`, not `In` — the value passes through unchanged.
    ///
    /// ```compile_fail
    /// # use nexus_rt::{PipelineBuilder, WorldBuilder};
    /// # let mut wb = WorldBuilder::new();
    /// # let world = wb.build();
    /// # let reg = world.registry();
    /// // ERROR: takes u32 by value, should be &u32
    /// PipelineBuilder::<u32>::new()
    ///     .then(|x: u32| x, &reg)
    ///     .guard(|x: u32| x > 10, &reg);
    /// ```
    ///
    /// Fix: take by reference:
    /// ```ignore
    /// PipelineBuilder::<u32>::new()
    ///     .then(|x: u32| x, &reg)
    ///     .guard(|x: &u32| *x > 10, &reg);
    /// ```
    pub fn guard<Params, S: IntoRefStep<Out, bool, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Option<Out>, GuardNode<Chain, S::Step>> {
        PipelineChain {
            chain: GuardNode {
                prev: self.chain,
                step: f.into_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Observe the current value without consuming or changing it.
    ///
    /// The step receives `&Out`. The value passes through unchanged.
    /// Useful for logging, metrics, or debugging mid-chain.
    ///
    /// # Common Mistakes
    ///
    /// Tap takes `&In`, not `In`:
    /// ```compile_fail
    /// # use nexus_rt::{PipelineBuilder, WorldBuilder};
    /// # let mut wb = WorldBuilder::new();
    /// # let world = wb.build();
    /// # let reg = world.registry();
    /// // ERROR: takes u32 by value
    /// PipelineBuilder::<u32>::new()
    ///     .then(|x: u32| x, &reg)
    ///     .tap(|x: u32| println!("{x}"), &reg);
    /// ```
    pub fn tap<Params, S: IntoRefStep<Out, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Out, TapNode<Chain, S::Step>> {
        PipelineChain {
            chain: TapNode {
                prev: self.chain,
                step: f.into_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Binary conditional routing. Evaluates the predicate on the
    /// current value, then moves it into exactly one of two arms.
    ///
    /// Both arms must produce the same output type. Build each arm as
    /// a sub-pipeline from [`PipelineBuilder`]. For N-ary routing, nest
    /// `route` calls in the false arm.
    ///
    /// ```ignore
    /// let large = PipelineBuilder::new().then(large_check, reg).then(submit, reg);
    /// let small = PipelineBuilder::new().then(submit, reg);
    ///
    /// PipelineBuilder::<Order>::new()
    ///     .then(validate, reg)
    ///     .route(|order: &Order| order.size > 1000, reg, large, small)
    ///     .build();
    /// ```
    pub fn route<NewOut, C0, C1, Params, Pred: IntoRefStep<Out, bool, Params>>(
        self,
        pred: Pred,
        registry: &Registry,
        on_true: PipelineChain<Out, NewOut, C0>,
        on_false: PipelineChain<Out, NewOut, C1>,
    ) -> PipelineChain<In, NewOut, RouteNode<Chain, Pred::Step, C0, C1>>
    where
        C0: ChainCall<Out, Out = NewOut>,
        C1: ChainCall<Out, Out = NewOut>,
    {
        PipelineChain {
            chain: RouteNode {
                prev: self.chain,
                pred: pred.into_ref_step(registry),
                on_true: on_true.chain,
                on_false: on_false.chain,
            },
            _marker: PhantomData,
        }
    }

    /// Fork off a multi-step side-effect chain. The arm borrows
    /// `&Out`, runs to completion (producing `()`), and the
    /// original value passes through unchanged.
    ///
    /// Multi-step version of [`tap`](Self::tap) — the arm has the
    /// full DAG combinator API with Param resolution. Build with
    /// [`DagArmSeed::new()`](crate::dag::DagArmSeed::new).
    pub fn tee<C>(self, side: DagArm<Out, (), C>) -> PipelineChain<In, Out, TeeNode<Chain, C>>
    where
        C: for<'a> ChainCall<&'a Out, Out = ()>,
    {
        PipelineChain {
            chain: TeeNode {
                prev: self.chain,
                side: side.chain,
            },
            _marker: PhantomData,
        }
    }

    /// Scan with persistent accumulator. The step receives `&mut Acc`
    /// and the current value, returning the new output. State persists
    /// across invocations.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// // Running sum — suppress values below threshold
    /// PipelineBuilder::<u64>::new()
    ///     .then(identity, reg)
    ///     .scan(0u64, |acc: &mut u64, val: u64| {
    ///         *acc += val;
    ///         if *acc > 100 { Some(*acc) } else { None }
    ///     }, reg)
    ///     .build();
    /// ```
    pub fn scan<Acc, NewOut, Params, S>(
        self,
        initial: Acc,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, NewOut, ScanNode<Chain, S::Step, Acc>>
    where
        Acc: 'static,
        S: IntoScanStep<Acc, Out, NewOut, Params>,
    {
        PipelineChain {
            chain: ScanNode {
                prev: self.chain,
                step: f.into_scan_step(registry),
                acc: initial,
            },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// Splat — tuple destructuring into individual function arguments
// =============================================================================
//
// `.splat()` transitions from a tuple output to a builder whose `.then()`
// accepts a function taking the tuple elements as individual arguments.
// After `.splat().then(f, reg)`, the user is back on PipelineChain.
//
// Builder types are `#[doc(hidden)]` — users only see `.splat().then()`.

// -- Splat builder types ------------------------------------------------------

macro_rules! define_splat_builders {
    (
        $N:literal,
        start: $SplatStart:ident,
        mid: $SplatBuilder:ident,
        node: $SplatThenNode:ident,
        into_trait: $IntoSplatStep:ident,
        call_trait: $SplatCall:ident,
        ($($T:ident),+),
        ($($idx:tt),+)
    ) => {
        /// Chain node for `.splat().then()` — destructures tuple into individual arguments.
        #[doc(hidden)]
        pub struct $SplatThenNode<Prev, S> {
            prev: Prev,
            step: S,
        }

        impl<In, $($T,)+ Prev, S> ChainCall<In> for $SplatThenNode<Prev, S>
        where
            Prev: ChainCall<In, Out = ($($T,)+)>,
            S: $SplatCall<$($T),+>,
        {
            type Out = S::Out;
            #[inline(always)]
            fn call(&mut self, world: &mut World, input: In) -> S::Out {
                let tuple = self.prev.call(world, input);
                self.step.call_splat(world, $(tuple.$idx),+)
            }
        }

        /// Splat builder at pipeline start position.
        #[doc(hidden)]
        pub struct $SplatStart<$($T),+>(PhantomData<fn(($($T,)+))>);

        impl<$($T),+> $SplatStart<$($T),+> {
            /// Add a step that receives the tuple elements as individual arguments.
            pub fn then<Out, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> PipelineChain<($($T,)+), Out, $SplatThenNode<IdentityNode, S::Step>>
            where
                S: $IntoSplatStep<$($T,)+ Out, Params>,
            {
                PipelineChain {
                    chain: $SplatThenNode {
                        prev: IdentityNode,
                        step: f.into_splat_step(registry),
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<$($T),+> PipelineBuilder<($($T,)+)> {
            /// Destructure the tuple input into individual function arguments.
            pub fn splat(self) -> $SplatStart<$($T),+> {
                $SplatStart(PhantomData)
            }
        }

        /// Splat builder at mid-chain position.
        #[doc(hidden)]
        pub struct $SplatBuilder<In, $($T,)+ Chain> {
            chain: Chain,
            _marker: PhantomData<fn(In) -> ($($T,)+)>,
        }

        impl<In, $($T,)+ Chain: ChainCall<In, Out = ($($T,)+)>> $SplatBuilder<In, $($T,)+ Chain> {
            /// Add a step that receives the tuple elements as individual arguments.
            pub fn then<Out, Params, S>(
                self,
                f: S,
                registry: &Registry,
            ) -> PipelineChain<In, Out, $SplatThenNode<Chain, S::Step>>
            where
                S: $IntoSplatStep<$($T,)+ Out, Params>,
            {
                PipelineChain {
                    chain: $SplatThenNode {
                        prev: self.chain,
                        step: f.into_splat_step(registry),
                    },
                    _marker: PhantomData,
                }
            }
        }

        impl<In, $($T,)+ Chain: ChainCall<In, Out = ($($T,)+)>> PipelineChain<In, ($($T,)+), Chain> {
            /// Destructure the tuple output into individual function arguments.
            pub fn splat(self) -> $SplatBuilder<In, $($T,)+ Chain> {
                $SplatBuilder {
                    chain: self.chain,
                    _marker: PhantomData,
                }
            }
        }
    };
}

define_splat_builders!(2,
    start: SplatStart2,
    mid: SplatBuilder2,
    node: SplatThenNode2,
    into_trait: IntoSplatStep2,
    call_trait: SplatCall2,
    (A, B),
    (0, 1)
);

define_splat_builders!(3,
    start: SplatStart3,
    mid: SplatBuilder3,
    node: SplatThenNode3,
    into_trait: IntoSplatStep3,
    call_trait: SplatCall3,
    (A, B, C),
    (0, 1, 2)
);

define_splat_builders!(4,
    start: SplatStart4,
    mid: SplatBuilder4,
    node: SplatThenNode4,
    into_trait: IntoSplatStep4,
    call_trait: SplatCall4,
    (A, B, C, D),
    (0, 1, 2, 3)
);

define_splat_builders!(5,
    start: SplatStart5,
    mid: SplatBuilder5,
    node: SplatThenNode5,
    into_trait: IntoSplatStep5,
    call_trait: SplatCall5,
    (A, B, C, D, E),
    (0, 1, 2, 3, 4)
);

// =============================================================================
// Dedup — suppress unchanged values
// =============================================================================

impl<In, Out: PartialEq + Clone, Chain: ChainCall<In, Out = Out>> PipelineChain<In, Out, Chain> {
    /// Suppress consecutive unchanged values. Returns `Some(val)`
    /// when the value differs from the previous invocation, `None`
    /// when unchanged. First invocation always returns `Some`.
    ///
    /// Requires `PartialEq + Clone` — the previous value is stored
    /// internally for comparison.
    pub fn dedup(self) -> PipelineChain<In, Option<Out>, DedupNode<Chain, Out>> {
        PipelineChain {
            chain: DedupNode {
                prev: self.chain,
                last: None,
            },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// Bool combinators
// =============================================================================

impl<In, Chain: ChainCall<In, Out = bool>> PipelineChain<In, bool, Chain> {
    /// Invert a boolean value.
    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> PipelineChain<In, bool, NotNode<Chain>> {
        PipelineChain {
            chain: NotNode { prev: self.chain },
            _marker: PhantomData,
        }
    }

    /// Short-circuit AND with a second boolean.
    ///
    /// If the chain produces `false`, the step is not called.
    pub fn and<Params, S: IntoProducer<bool, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, bool, AndBoolNode<Chain, S::Step>> {
        PipelineChain {
            chain: AndBoolNode {
                prev: self.chain,
                producer: f.into_producer(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Short-circuit OR with a second boolean.
    ///
    /// If the chain produces `true`, the step is not called.
    pub fn or<Params, S: IntoProducer<bool, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, bool, OrBoolNode<Chain, S::Step>> {
        PipelineChain {
            chain: OrBoolNode {
                prev: self.chain,
                producer: f.into_producer(registry),
            },
            _marker: PhantomData,
        }
    }

    /// XOR with a second boolean.
    ///
    /// Both sides are always evaluated.
    pub fn xor<Params, S: IntoProducer<bool, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, bool, XorBoolNode<Chain, S::Step>> {
        PipelineChain {
            chain: XorBoolNode {
                prev: self.chain,
                producer: f.into_producer(registry),
            },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// Clone helpers — &T → T transitions
// =============================================================================

impl<'a, In, T: Clone, Chain: ChainCall<In, Out = &'a T>> PipelineChain<In, &'a T, Chain> {
    /// Clone a borrowed output to produce an owned value.
    ///
    /// Transitions the pipeline from `&T` to `T`. Uses UFCS
    /// (`T::clone(val)`) — `val.clone()` on a `&&T` resolves to
    /// `<&T as Clone>::clone` and returns `&T`, not `T`.
    pub fn cloned(self) -> PipelineChain<In, T, ClonedNode<Chain>> {
        PipelineChain {
            chain: ClonedNode { prev: self.chain },
            _marker: PhantomData,
        }
    }
}

impl<'a, In, T: Clone, Chain: ChainCall<In, Out = Option<&'a T>>>
    PipelineChain<In, Option<&'a T>, Chain>
{
    /// Clone inner borrowed value. `Option<&T>` → `Option<T>`.
    pub fn cloned(self) -> PipelineChain<In, Option<T>, ClonedOptionNode<Chain>> {
        PipelineChain {
            chain: ClonedOptionNode { prev: self.chain },
            _marker: PhantomData,
        }
    }
}

impl<'a, In, T: Clone, E, Chain: ChainCall<In, Out = Result<&'a T, E>>>
    PipelineChain<In, Result<&'a T, E>, Chain>
{
    /// Clone inner borrowed Ok value. `Result<&T, E>` → `Result<T, E>`.
    pub fn cloned(self) -> PipelineChain<In, Result<T, E>, ClonedResultNode<Chain>> {
        PipelineChain {
            chain: ClonedResultNode { prev: self.chain },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// Option helpers — PipelineChain<In, Option<T>, Chain>
// =============================================================================

impl<In, T, Chain: ChainCall<In, Out = Option<T>>> PipelineChain<In, Option<T>, Chain> {
    // -- IntoStep-based (hot path) -------------------------------------------

    /// Transform the inner value. Step not called on None.
    pub fn map<U, Params, S: IntoStep<T, U, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Option<U>, MapOptionNode<Chain, S::Step>> {
        PipelineChain {
            chain: MapOptionNode {
                prev: self.chain,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Short-circuits on None. std: `Option::and_then`
    pub fn and_then<U, Params, S: IntoStep<T, Option<U>, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Option<U>, AndThenNode<Chain, S::Step>> {
        PipelineChain {
            chain: AndThenNode {
                prev: self.chain,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }

    // -- Resolved (cold path, now with Param resolution) -----------------------

    /// Side effect on None. Complement to [`inspect`](Self::inspect).
    pub fn on_none<Params, S: IntoProducer<(), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Option<T>, OnNoneNode<Chain, S::Step>> {
        PipelineChain {
            chain: OnNoneNode {
                prev: self.chain,
                producer: f.into_producer(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Keep value if predicate holds. std: `Option::filter`
    ///
    /// # Common Mistakes
    ///
    /// Filter operates on `&T` inside the Option, not `T`:
    /// ```compile_fail
    /// # use nexus_rt::{PipelineBuilder, WorldBuilder};
    /// # let mut wb = WorldBuilder::new();
    /// # let world = wb.build();
    /// # let reg = world.registry();
    /// fn to_opt(x: u32) -> Option<u32> { Some(x) }
    /// // ERROR: takes u32, should be &u32
    /// PipelineBuilder::<u32>::new()
    ///     .then(to_opt, &reg)
    ///     .filter(|x: u32| x > 10, &reg);
    /// ```
    pub fn filter<Params, S: IntoRefStep<T, bool, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Option<T>, FilterNode<Chain, S::Step>> {
        PipelineChain {
            chain: FilterNode {
                prev: self.chain,
                step: f.into_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Side effect on Some value. std: `Option::inspect`
    ///
    /// Takes `&T`, not `T` — the value passes through.
    pub fn inspect<Params, S: IntoRefStep<T, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Option<T>, InspectOptionNode<Chain, S::Step>> {
        PipelineChain {
            chain: InspectOptionNode {
                prev: self.chain,
                step: f.into_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// None becomes Err(err). std: `Option::ok_or`
    ///
    /// `Clone` required because the pipeline may run many times —
    /// the error value is cloned on each `None` invocation.
    pub fn ok_or<E: Clone>(self, err: E) -> PipelineChain<In, Result<T, E>, OkOrNode<Chain, E>> {
        PipelineChain {
            chain: OkOrNode {
                prev: self.chain,
                err,
            },
            _marker: PhantomData,
        }
    }

    /// None becomes Err(f()). std: `Option::ok_or_else`
    pub fn ok_or_else<E, Params, S: IntoProducer<E, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Result<T, E>, OkOrElseNode<Chain, S::Step>> {
        PipelineChain {
            chain: OkOrElseNode {
                prev: self.chain,
                producer: f.into_producer(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Exit Option — None becomes the default value.
    ///
    /// `Clone` required because the pipeline may run many times —
    /// the default is cloned on each `None` invocation (unlike
    /// std's `unwrap_or` which consumes the value once).
    pub fn unwrap_or(self, default: T) -> PipelineChain<In, T, UnwrapOrOptionNode<Chain, T>>
    where
        T: Clone,
    {
        PipelineChain {
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
    ) -> PipelineChain<In, T, UnwrapOrElseOptionNode<Chain, S::Step>> {
        PipelineChain {
            chain: UnwrapOrElseOptionNode {
                prev: self.chain,
                producer: f.into_producer(registry),
            },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// Result helpers — PipelineChain<In, Result<T, E>, Chain>
// =============================================================================

impl<In, T, E, Chain: ChainCall<In, Out = Result<T, E>>> PipelineChain<In, Result<T, E>, Chain> {
    // -- IntoStep-based (hot path) -------------------------------------------

    /// Transform the Ok value. Step not called on Err.
    pub fn map<U, Params, S: IntoStep<T, U, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Result<U, E>, MapResultNode<Chain, S::Step>> {
        PipelineChain {
            chain: MapResultNode {
                prev: self.chain,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Short-circuits on Err. std: `Result::and_then`
    pub fn and_then<U, Params, S: IntoStep<T, Result<U, E>, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Result<U, E>, AndThenResultNode<Chain, S::Step>> {
        PipelineChain {
            chain: AndThenResultNode {
                prev: self.chain,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Handle error and transition to Option.
    ///
    /// `Ok(val)` becomes `Some(val)` — handler not called.
    /// `Err(err)` calls the handler, then produces `None`.
    pub fn catch<Params, S: IntoStep<E, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Option<T>, CatchNode<Chain, S::Step>> {
        PipelineChain {
            chain: CatchNode {
                prev: self.chain,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }

    // -- Resolved (cold path, now with Param resolution) -----------------------

    /// Transform the error. std: `Result::map_err`
    pub fn map_err<E2, Params, S: IntoStep<E, E2, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Result<T, E2>, MapErrNode<Chain, S::Step>> {
        PipelineChain {
            chain: MapErrNode {
                prev: self.chain,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Recover from Err. std: `Result::or_else`
    pub fn or_else<E2, Params, S: IntoStep<E, Result<T, E2>, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Result<T, E2>, OrElseNode<Chain, S::Step>> {
        PipelineChain {
            chain: OrElseNode {
                prev: self.chain,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Side effect on Ok. std: `Result::inspect`
    ///
    /// Takes `&T`, not `T` — the value passes through.
    pub fn inspect<Params, S: IntoRefStep<T, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Result<T, E>, InspectResultNode<Chain, S::Step>> {
        PipelineChain {
            chain: InspectResultNode {
                prev: self.chain,
                step: f.into_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Side effect on Err. std: `Result::inspect_err`
    ///
    /// Takes `&E`, not `E` — the error passes through.
    pub fn inspect_err<Params, S: IntoRefStep<E, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, Result<T, E>, InspectErrNode<Chain, S::Step>> {
        PipelineChain {
            chain: InspectErrNode {
                prev: self.chain,
                step: f.into_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Discard error, enter Option land. std: `Result::ok`
    pub fn ok(self) -> PipelineChain<In, Option<T>, OkResultNode<Chain>> {
        PipelineChain {
            chain: OkResultNode { prev: self.chain },
            _marker: PhantomData,
        }
    }

    /// Exit Result — Err becomes the default value.
    ///
    /// `Clone` required because the pipeline may run many times —
    /// the default is cloned on each `Err` invocation (unlike
    /// std's `unwrap_or` which consumes the value once).
    pub fn unwrap_or(self, default: T) -> PipelineChain<In, T, UnwrapOrResultNode<Chain, T>>
    where
        T: Clone,
    {
        PipelineChain {
            chain: UnwrapOrResultNode {
                prev: self.chain,
                default,
            },
            _marker: PhantomData,
        }
    }

    /// Exit Result — Err becomes `f(err)`.
    pub fn unwrap_or_else<Params, S: IntoStep<E, T, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> PipelineChain<In, T, UnwrapOrElseResultNode<Chain, S::Step>> {
        PipelineChain {
            chain: UnwrapOrElseResultNode {
                prev: self.chain,
                step: f.into_step(registry),
            },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// PipelineOutput — marker trait for build()
// =============================================================================

mod pipeline_output_seal {
    pub trait Sealed {}
    impl Sealed for () {}
    impl Sealed for Option<()> {}
}

/// Sealed marker trait for valid pipeline terminal types.
///
/// Only `()` and `Option<()>` satisfy this. A pipeline can only
/// `.build()` when its output is one of these types — add a final
/// `.then()` or `.dispatch()` that consumes the output.
#[diagnostic::on_unimplemented(
    message = "`build()` requires the pipeline output to be `()` or `Option<()>`",
    label = "this pipeline produces `{Self}`, not `()` or `Option<()>`",
    note = "add a final `.then()` or `.dispatch()` that consumes the output"
)]
pub trait PipelineOutput: pipeline_output_seal::Sealed {}
impl PipelineOutput for () {}
impl PipelineOutput for Option<()> {}

// =============================================================================
// build — when Out: PipelineOutput (() or Option<()>)
// =============================================================================

impl<In, Chain: ChainCall<In, Out = ()>> PipelineChain<In, (), Chain> {
    /// Finalize the pipeline into a [`Pipeline`].
    ///
    /// The returned pipeline is a concrete, monomorphized type — no boxing,
    /// no virtual dispatch. Call `.run()` directly for zero-cost execution,
    /// or wrap in `Box<dyn Handler<In>>` when type erasure is needed.
    ///
    /// Only available when the pipeline ends with `()` or `Option<()>`.
    /// If your chain produces a value, add a final `.then()` that consumes
    /// the output.
    #[must_use = "building a pipeline without storing it does nothing"]
    pub fn build(self) -> Pipeline<Chain> {
        Pipeline { chain: self.chain }
    }
}

impl<In, Chain: ChainCall<In, Out = Option<()>>> PipelineChain<In, Option<()>, Chain> {
    /// Finalize the pipeline into a [`Pipeline`], discarding the `Option<()>`.
    ///
    /// Pipelines ending with `Option<()>` (e.g. after `.map()` on an
    /// `Option<T>` with a step that returns `()`) produce the same
    /// [`Pipeline`] as those ending with `()`.
    #[must_use = "building a pipeline without storing it does nothing"]
    pub fn build(self) -> Pipeline<DiscardOptionNode<Chain>> {
        Pipeline {
            chain: DiscardOptionNode { prev: self.chain },
        }
    }
}

// =============================================================================
// build_batch — when Out: PipelineOutput (() or Option<()>)
// =============================================================================

impl<In, Out: PipelineOutput, Chain: ChainCall<In, Out = Out>> PipelineChain<In, Out, Chain> {
    /// Finalize into a [`BatchPipeline`] with a pre-allocated input buffer.
    ///
    /// Same pipeline chain as [`build`](PipelineChain::build), but the
    /// pipeline owns an input buffer that drivers fill between dispatch
    /// cycles. Each call to [`BatchPipeline::run`] drains the buffer,
    /// running every item through the chain independently.
    ///
    /// Available when the pipeline ends with `()` or `Option<()>` (e.g.
    /// after `.catch()` or `.filter()`). Pipelines producing values need
    /// a final `.then()` that consumes the output.
    ///
    /// `capacity` is the initial allocation — the buffer can grow if needed,
    /// but sizing it for the expected batch size avoids reallocation.
    #[must_use = "building a pipeline without storing it does nothing"]
    pub fn build_batch(self, capacity: usize) -> BatchPipeline<In, Chain> {
        BatchPipeline {
            input: Vec::with_capacity(capacity),
            chain: self.chain,
        }
    }
}

// =============================================================================
// Pipeline<F> — built pipeline
// =============================================================================

/// Built step pipeline implementing [`Handler<E>`](crate::Handler).
///
/// Created by [`PipelineChain::build`]. The entire pipeline chain is
/// monomorphized at compile time — no boxing, no virtual dispatch.
/// Call `.run()` directly for zero-cost execution, or wrap in
/// `Box<dyn Handler<E>>` when you need type erasure (single box).
///
/// Implements [`Handler<E>`](crate::Handler) for any event type `E`
/// that the chain accepts — including borrowed types like `&'a [u8]`.
/// Supports `for<'a> Handler<&'a T>` for zero-copy event dispatch.
pub struct Pipeline<F> {
    chain: F,
}

impl<E, F: ChainCall<E, Out = ()> + Send> crate::Handler<E> for Pipeline<F> {
    fn run(&mut self, world: &mut World, event: E) {
        self.chain.call(world, event);
    }
}

// =============================================================================
// BatchPipeline<In, F> — pipeline with owned input buffer
// =============================================================================

/// Batch pipeline that owns a pre-allocated input buffer.
///
/// Created by [`PipelineChain::build_batch`]. Each item flows through
/// the full pipeline chain independently — the same per-item `Option`
/// and `Result` flow control as [`Pipeline`]. Errors are handled inline
/// (via `.catch()`, `.unwrap_or()`, etc.) and the batch continues to
/// the next item. No intermediate buffers between steps.
///
/// # Examples
///
/// ```
/// use nexus_rt::{WorldBuilder, ResMut, PipelineBuilder, Resource};
///
/// #[derive(Resource)]
/// struct Accum(u64);
///
/// let mut wb = WorldBuilder::new();
/// wb.register(Accum(0));
/// let mut world = wb.build();
///
/// fn accumulate(mut sum: ResMut<Accum>, x: u32) {
///     sum.0 += x as u64;
/// }
///
/// let r = world.registry();
/// let mut batch = PipelineBuilder::<u32>::new()
///     .then(accumulate, r)
///     .build_batch(64);
///
/// batch.input_mut().extend_from_slice(&[1, 2, 3, 4, 5]);
/// batch.run(&mut world);
///
/// assert_eq!(world.resource::<Accum>().0, 15);
/// assert!(batch.input().is_empty());
/// ```
pub struct BatchPipeline<In, F> {
    input: Vec<In>,
    chain: F,
}

impl<In, Out: PipelineOutput, F: ChainCall<In, Out = Out>> BatchPipeline<In, F> {
    /// Mutable access to the input buffer. Drivers fill this between
    /// dispatch cycles.
    pub fn input_mut(&mut self) -> &mut Vec<In> {
        &mut self.input
    }

    /// Read-only access to the input buffer.
    pub fn input(&self) -> &[In] {
        &self.input
    }

    /// Drain the input buffer, running each item through the pipeline.
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
// resolve_step — pre-resolve a step for manual dispatch (owned input)
// =============================================================================

/// Resolve a step for use in manual dispatch (e.g. inside an
/// [`Opaque`] closure passed to `.then()`).
///
/// Returns a closure with pre-resolved [`Param`] state — the same
/// build-time resolution that `.then()` performs, but as a standalone
/// value the caller can invoke from any context.
///
/// This is the pipeline (owned-input) counterpart of
/// [`dag::resolve_arm`](crate::dag::resolve_arm) (reference-input).
///
/// # Examples
///
/// ```ignore
/// let mut arm0 = resolve_step(handle_new, &reg);
/// let mut arm1 = resolve_step(handle_cancel, &reg);
///
/// pipeline.then(move |world: &mut World, order: Order| match order.kind {
///     OrderKind::New    => arm0(world, order),
///     OrderKind::Cancel => arm1(world, order),
/// }, &reg)
/// ```
pub fn resolve_step<In, Out, Params, S>(
    f: S,
    registry: &Registry,
) -> impl FnMut(&mut World, In) -> Out + use<In, Out, Params, S>
where
    In: 'static,
    Out: 'static,
    S: IntoStep<In, Out, Params>,
{
    let mut resolved = f.into_step(registry);
    move |world: &mut World, input: In| resolved.call(world, input)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Handler, IntoHandler, Local, Res, ResMut, WorldBuilder, fan_out};

    // =========================================================================
    // Core dispatch
    // =========================================================================

    #[test]
    fn step_pure_transform() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new().then(|x: u32| x as u64 * 2, r);
        assert_eq!(p.run(&mut world, 5), 10u64);
    }

    #[test]
    fn step_one_res() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        let mut world = wb.build();

        fn multiply(factor: Res<u64>, x: u32) -> u64 {
            *factor * x as u64
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new().then(multiply, r);
        assert_eq!(p.run(&mut world, 5), 50);
    }

    #[test]
    fn step_one_res_mut() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn accumulate(mut total: ResMut<u64>, x: u32) {
            *total += x as u64;
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new().then(accumulate, r);
        p.run(&mut world, 10);
        p.run(&mut world, 5);
        assert_eq!(*world.resource::<u64>(), 15);
    }

    #[test]
    fn step_two_params() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        wb.register::<bool>(true);
        let mut world = wb.build();

        fn conditional(factor: Res<u64>, flag: Res<bool>, x: u32) -> u64 {
            if *flag { *factor * x as u64 } else { 0 }
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new().then(conditional, r);
        assert_eq!(p.run(&mut world, 5), 50);
    }

    #[test]
    fn step_chain_two() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(2);
        let mut world = wb.build();

        fn double(factor: Res<u64>, x: u32) -> u64 {
            *factor * x as u64
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(double, r)
            .then(|val: u64| val + 1, r);
        assert_eq!(p.run(&mut world, 5), 11); // 2*5 + 1
    }

    // =========================================================================
    // Option combinators
    // =========================================================================

    #[test]
    fn option_map_on_some() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        let mut world = wb.build();

        fn add_factor(factor: Res<u64>, x: u32) -> u64 {
            *factor + x as u64
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Option<u32> { Some(x) }, r)
            .map(add_factor, r);
        assert_eq!(p.run(&mut world, 5), Some(15));
    }

    #[test]
    fn option_map_skips_none() {
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(false);
        let mut world = wb.build();

        fn mark(mut flag: ResMut<bool>, _x: u32) -> u32 {
            *flag = true;
            0
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Option<u32> { None }, r)
            .map(mark, r);
        assert_eq!(p.run(&mut world, 5), None);
        assert!(!*world.resource::<bool>());
    }

    #[test]
    fn option_and_then_chains() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        let mut world = wb.build();

        fn check(min: Res<u64>, x: u32) -> Option<u64> {
            let val = x as u64;
            if val > *min { Some(val) } else { None }
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| Some(x), r)
            .and_then(check, r);
        assert_eq!(p.run(&mut world, 20), Some(20));
    }

    #[test]
    fn option_and_then_short_circuits() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        let mut world = wb.build();

        fn check(min: Res<u64>, x: u32) -> Option<u64> {
            let val = x as u64;
            if val > *min { Some(val) } else { None }
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| Some(x), r)
            .and_then(check, r);
        assert_eq!(p.run(&mut world, 5), None);
    }

    #[test]
    fn option_on_none_fires() {
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(false);
        let mut world = wb.build();

        let r = world.registry();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Option<u32> { None }, r)
            .on_none(
                |w: &mut World| {
                    *w.resource_mut::<bool>() = true;
                },
                r,
            );
        p.run(&mut world, 0);
        assert!(*world.resource::<bool>());
    }

    #[test]
    fn option_filter_keeps() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| Some(x), r)
            .filter(|x: &u32| *x > 3, r);
        assert_eq!(p.run(&mut world, 5), Some(5));
    }

    #[test]
    fn option_filter_drops() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| Some(x), r)
            .filter(|x: &u32| *x > 10, r);
        assert_eq!(p.run(&mut world, 5), None);
    }

    // =========================================================================
    // Result combinators
    // =========================================================================

    #[test]
    fn result_map_on_ok() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        let mut world = wb.build();

        fn add_factor(factor: Res<u64>, x: u32) -> u64 {
            *factor + x as u64
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Result<u32, String> { Ok(x) }, r)
            .map(add_factor, r);
        assert_eq!(p.run(&mut world, 5), Ok(15));
    }

    #[test]
    fn result_map_skips_err() {
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(false);
        let mut world = wb.build();

        fn mark(mut flag: ResMut<bool>, _x: u32) -> u32 {
            *flag = true;
            0
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Result<u32, String> { Err("fail".into()) }, r)
            .map(mark, r);
        assert!(p.run(&mut world, 5).is_err());
        assert!(!*world.resource::<bool>());
    }

    #[test]
    fn result_catch_handles_error() {
        let mut wb = WorldBuilder::new();
        wb.register::<String>(String::new());
        let mut world = wb.build();

        fn log_error(mut log: ResMut<String>, err: String) {
            *log = err;
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Result<u32, String> { Err("caught".into()) }, r)
            .catch(log_error, r);
        assert_eq!(p.run(&mut world, 0), None);
        assert_eq!(world.resource::<String>().as_str(), "caught");
    }

    #[test]
    fn result_catch_passes_ok() {
        let mut wb = WorldBuilder::new();
        wb.register::<String>(String::new());
        let mut world = wb.build();

        fn log_error(mut log: ResMut<String>, err: String) {
            *log = err;
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Result<u32, String> { Ok(x) }, r)
            .catch(log_error, r);
        assert_eq!(p.run(&mut world, 5), Some(5));
        assert!(world.resource::<String>().is_empty());
    }

    // =========================================================================
    // Build + Handler
    // =========================================================================

    #[test]
    fn build_produces_handler() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn accumulate(mut total: ResMut<u64>, x: u32) {
            *total += x as u64;
        }

        let r = world.registry_mut();
        let mut pipeline = PipelineBuilder::<u32>::new().then(accumulate, r).build();

        pipeline.run(&mut world, 10);
        pipeline.run(&mut world, 5);
        assert_eq!(*world.resource::<u64>(), 15);
    }

    #[test]
    fn run_returns_output() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(3);
        let mut world = wb.build();

        fn multiply(factor: Res<u64>, x: u32) -> u64 {
            *factor * x as u64
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new().then(multiply, r);
        let result: u64 = p.run(&mut world, 7);
        assert_eq!(result, 21);
    }

    // =========================================================================
    // Safety
    // =========================================================================

    #[test]
    #[should_panic(expected = "not registered")]
    fn panics_on_missing_resource() {
        let mut world = WorldBuilder::new().build();

        fn needs_u64(_val: Res<u64>, _x: u32) -> u32 {
            0
        }

        let r = world.registry_mut();
        let _p = PipelineBuilder::<u32>::new().then(needs_u64, r);
    }

    // =========================================================================
    // Access conflict detection
    // =========================================================================

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn step_duplicate_access_panics() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn bad(a: Res<u64>, b: ResMut<u64>, _x: u32) -> u32 {
            let _ = (*a, &*b);
            0
        }

        let r = world.registry_mut();
        let _p = PipelineBuilder::<u32>::new().then(bad, r);
    }

    // =========================================================================
    // Integration
    // =========================================================================

    #[test]
    fn local_in_step() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn count(mut count: Local<u64>, mut total: ResMut<u64>, _x: u32) {
            *count += 1;
            *total = *count;
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new().then(count, r);
        p.run(&mut world, 0);
        p.run(&mut world, 0);
        p.run(&mut world, 0);
        assert_eq!(*world.resource::<u64>(), 3);
    }

    // =========================================================================
    // Option combinators (extended)
    // =========================================================================

    #[test]
    fn option_unwrap_or_some() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Option<u32> { Some(x) }, r)
            .unwrap_or(99);
        assert_eq!(p.run(&mut world, 5), 5);
    }

    #[test]
    fn option_unwrap_or_none() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Option<u32> { None }, r)
            .unwrap_or(99);
        assert_eq!(p.run(&mut world, 5), 99);
    }

    #[test]
    fn option_unwrap_or_else() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Option<u32> { None }, r)
            .unwrap_or_else(|| 42, r);
        assert_eq!(p.run(&mut world, 0), 42);
    }

    #[test]
    fn option_ok_or() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Option<u32> { None }, r)
            .ok_or("missing");
        assert_eq!(p.run(&mut world, 0), Err("missing"));
    }

    #[test]
    fn option_ok_or_some() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Option<u32> { Some(x) }, r)
            .ok_or("missing");
        assert_eq!(p.run(&mut world, 7), Ok(7));
    }

    #[test]
    fn option_ok_or_else() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Option<u32> { None }, r)
            .ok_or_else(|| "computed", r);
        assert_eq!(p.run(&mut world, 0), Err("computed"));
    }

    #[test]
    fn option_inspect_passes_through() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Option<u32> { Some(x) }, r)
            .inspect(|_val: &u32| {}, r);
        // inspect should pass through the value unchanged.
        assert_eq!(p.run(&mut world, 10), Some(10));
    }

    // =========================================================================
    // Result combinators (extended)
    // =========================================================================

    #[test]
    fn result_map_err() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Result<u32, i32> { Err(-1) }, r)
            .map_err(|e: i32| e.to_string(), r);
        assert_eq!(p.run(&mut world, 0), Err("-1".to_string()));
    }

    #[test]
    fn result_map_err_ok_passthrough() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Result<u32, i32> { Ok(x) }, r)
            .map_err(|e: i32| e.to_string(), r);
        assert_eq!(p.run(&mut world, 5), Ok(5));
    }

    #[test]
    fn result_or_else() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Result<u32, &str> { Err("fail") }, r)
            .or_else(|_e: &str| Ok::<u32, &str>(42), r);
        assert_eq!(p.run(&mut world, 0), Ok(42));
    }

    #[test]
    fn result_inspect_passes_through() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Result<u32, &str> { Ok(x) }, r)
            .inspect(|_val: &u32| {}, r);
        // inspect should pass through Ok unchanged.
        assert_eq!(p.run(&mut world, 7), Ok(7));
    }

    #[test]
    fn result_inspect_err_passes_through() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Result<u32, &str> { Err("bad") }, r)
            .inspect_err(|_e: &&str| {}, r);
        // inspect_err should pass through Err unchanged.
        assert_eq!(p.run(&mut world, 0), Err("bad"));
    }

    #[test]
    fn result_ok_converts() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Result<u32, &str> { Ok(x) }, r)
            .ok();
        assert_eq!(p.run(&mut world, 5), Some(5));
    }

    #[test]
    fn result_ok_drops_err() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Result<u32, &str> { Err("gone") }, r)
            .ok();
        assert_eq!(p.run(&mut world, 0), None);
    }

    #[test]
    fn result_unwrap_or() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Result<u32, &str> { Err("x") }, r)
            .unwrap_or(99);
        assert_eq!(p.run(&mut world, 0), 99);
    }

    #[test]
    fn result_unwrap_or_else() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| -> Result<u32, i32> { Err(-5) }, r)
            .unwrap_or_else(|e: i32| e.unsigned_abs(), r);
        assert_eq!(p.run(&mut world, 0), 5);
    }

    // =========================================================================
    // Batch pipeline
    // =========================================================================

    #[test]
    fn batch_accumulates() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn accumulate(mut sum: ResMut<u64>, x: u32) {
            *sum += x as u64;
        }

        let r = world.registry_mut();
        let mut batch = PipelineBuilder::<u32>::new()
            .then(accumulate, r)
            .build_batch(16);

        batch.input_mut().extend_from_slice(&[1, 2, 3, 4, 5]);
        batch.run(&mut world);

        assert_eq!(*world.resource::<u64>(), 15);
        assert!(batch.input().is_empty());
    }

    #[test]
    fn batch_retains_allocation() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut batch = PipelineBuilder::<u32>::new()
            .then(|_x: u32| {}, r)
            .build_batch(64);

        batch.input_mut().extend_from_slice(&[1, 2, 3]);
        batch.run(&mut world);

        assert!(batch.input().is_empty());
        assert!(batch.input_mut().capacity() >= 64);
    }

    #[test]
    fn batch_empty_is_noop() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn accumulate(mut sum: ResMut<u64>, x: u32) {
            *sum += x as u64;
        }

        let r = world.registry_mut();
        let mut batch = PipelineBuilder::<u32>::new()
            .then(accumulate, r)
            .build_batch(16);

        batch.run(&mut world);
        assert_eq!(*world.resource::<u64>(), 0);
    }

    #[test]
    fn batch_catch_continues_on_error() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<u32>(0);
        let mut world = wb.build();

        fn validate(x: u32) -> Result<u32, &'static str> {
            if x > 0 { Ok(x) } else { Err("zero") }
        }

        fn count_errors(mut errs: ResMut<u32>, _err: &'static str) {
            *errs += 1;
        }

        fn accumulate(mut sum: ResMut<u64>, x: u32) {
            *sum += x as u64;
        }

        let r = world.registry_mut();
        let mut batch = PipelineBuilder::<u32>::new()
            .then(validate, r)
            .catch(count_errors, r)
            .map(accumulate, r)
            .build_batch(16);

        // Items: 1, 0 (error), 2, 0 (error), 3
        batch.input_mut().extend_from_slice(&[1, 0, 2, 0, 3]);
        batch.run(&mut world);

        assert_eq!(*world.resource::<u64>(), 6); // 1 + 2 + 3
        assert_eq!(*world.resource::<u32>(), 2); // 2 errors
    }

    #[test]
    fn batch_filter_skips_items() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn accumulate(mut sum: ResMut<u64>, x: u32) {
            *sum += x as u64;
        }

        let r = world.registry_mut();
        let mut batch = PipelineBuilder::<u32>::new()
            .then(
                |x: u32| -> Option<u32> { if x > 2 { Some(x) } else { None } },
                r,
            )
            .map(accumulate, r)
            .build_batch(16);

        batch.input_mut().extend_from_slice(&[1, 2, 3, 4, 5]);
        batch.run(&mut world);

        assert_eq!(*world.resource::<u64>(), 12); // 3 + 4 + 5
    }

    #[test]
    fn batch_multiple_runs_accumulate() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn accumulate(mut sum: ResMut<u64>, x: u32) {
            *sum += x as u64;
        }

        let r = world.registry_mut();
        let mut batch = PipelineBuilder::<u32>::new()
            .then(accumulate, r)
            .build_batch(16);

        batch.input_mut().extend_from_slice(&[1, 2, 3]);
        batch.run(&mut world);
        assert_eq!(*world.resource::<u64>(), 6);

        batch.input_mut().extend_from_slice(&[4, 5]);
        batch.run(&mut world);
        assert_eq!(*world.resource::<u64>(), 15);
    }

    #[test]
    fn batch_with_world_access() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10); // multiplier
        wb.register::<Vec<u64>>(Vec::new());
        let mut world = wb.build();

        fn multiply_and_collect(factor: Res<u64>, mut out: ResMut<Vec<u64>>, x: u32) {
            out.push(x as u64 * *factor);
        }

        let r = world.registry_mut();
        let mut batch = PipelineBuilder::<u32>::new()
            .then(multiply_and_collect, r)
            .build_batch(16);

        batch.input_mut().extend_from_slice(&[1, 2, 3]);
        batch.run(&mut world);

        assert_eq!(world.resource::<Vec<u64>>().as_slice(), &[10, 20, 30]);
    }

    // =========================================================================
    // Cloned combinator
    // =========================================================================

    // Named functions for proper lifetime elision (&'a u32 → &'a u32).
    // Closures get two independent lifetimes and fail to compile.
    fn ref_identity(x: &u32) -> &u32 {
        x
    }
    #[allow(clippy::unnecessary_wraps)]
    fn ref_wrap_some(x: &u32) -> Option<&u32> {
        Some(x)
    }
    fn ref_wrap_none(_x: &u32) -> Option<&u32> {
        None
    }
    #[allow(clippy::unnecessary_wraps)]
    fn ref_wrap_ok(x: &u32) -> Result<&u32, String> {
        Ok(x)
    }
    fn ref_wrap_err(_x: &u32) -> Result<&u32, String> {
        Err("fail".into())
    }

    #[test]
    fn cloned_bare() {
        let mut world = WorldBuilder::new().build();
        // val before p — val must outlive the pipeline's In = &u32
        let val = 42u32;
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<&u32>::new()
            .then(ref_identity, r)
            .cloned();
        assert_eq!(p.run(&mut world, &val), 42u32);
    }

    #[test]
    fn cloned_option_some() {
        let mut world = WorldBuilder::new().build();
        let val = 42u32;
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<&u32>::new()
            .then(ref_wrap_some, r)
            .cloned();
        assert_eq!(p.run(&mut world, &val), Some(42u32));
    }

    #[test]
    fn cloned_option_none() {
        let mut world = WorldBuilder::new().build();
        let val = 42u32;
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<&u32>::new()
            .then(ref_wrap_none, r)
            .cloned();
        assert_eq!(p.run(&mut world, &val), None);
    }

    #[test]
    fn cloned_result_ok() {
        let mut world = WorldBuilder::new().build();
        let val = 42u32;
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<&u32>::new().then(ref_wrap_ok, r).cloned();
        assert_eq!(p.run(&mut world, &val), Ok(42u32));
    }

    #[test]
    fn cloned_result_err() {
        let mut world = WorldBuilder::new().build();
        let val = 42u32;
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<&u32>::new()
            .then(ref_wrap_err, r)
            .cloned();
        assert_eq!(p.run(&mut world, &val), Err("fail".into()));
    }

    // =========================================================================
    // Dispatch combinator
    // =========================================================================

    #[test]
    fn dispatch_to_handler() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn store(mut out: ResMut<u64>, val: u32) {
            *out = val as u64;
        }

        let r = world.registry_mut();
        let handler = PipelineBuilder::<u32>::new().then(store, r).build();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x * 2, r)
            .dispatch(handler)
            .build();

        p.run(&mut world, 5);
        assert_eq!(*world.resource::<u64>(), 10);
    }

    #[test]
    fn dispatch_to_fanout() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<i64>(0);
        let mut world = wb.build();

        fn write_u64(mut sink: ResMut<u64>, event: &u32) {
            *sink += *event as u64;
        }
        fn write_i64(mut sink: ResMut<i64>, event: &u32) {
            *sink += *event as i64;
        }

        let h1 = write_u64.into_handler(world.registry());
        let h2 = write_i64.into_handler(world.registry());
        let fan = fan_out!(h1, h2);

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x * 2, r)
            .dispatch(fan)
            .build();

        p.run(&mut world, 5);
        assert_eq!(*world.resource::<u64>(), 10);
        assert_eq!(*world.resource::<i64>(), 10);
    }

    #[test]
    fn dispatch_to_broadcast() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn write_u64(mut sink: ResMut<u64>, event: &u32) {
            *sink += *event as u64;
        }

        let mut broadcast = crate::Broadcast::<u32>::new();
        broadcast.add(write_u64.into_handler(world.registry()));
        broadcast.add(write_u64.into_handler(world.registry()));

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x + 1, r)
            .dispatch(broadcast)
            .build();

        p.run(&mut world, 4);
        assert_eq!(*world.resource::<u64>(), 10); // 5 + 5
    }

    #[test]
    fn dispatch_build_produces_handler() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn store(mut out: ResMut<u64>, val: u32) {
            *out = val as u64;
        }

        let r = world.registry_mut();
        let inner = PipelineBuilder::<u32>::new().then(store, r).build();

        let mut pipeline: Box<dyn Handler<u32>> = Box::new(
            PipelineBuilder::<u32>::new()
                .then(|x: u32| x + 1, r)
                .dispatch(inner)
                .build(),
        );

        pipeline.run(&mut world, 9);
        assert_eq!(*world.resource::<u64>(), 10);
    }

    // -- Guard combinator --

    #[test]
    fn pipeline_guard_keeps() {
        fn sink(mut out: ResMut<u64>, val: Option<u64>) {
            *out = val.unwrap_or(0);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64, reg)
            .guard(|v: &u64| *v > 3, reg)
            .then(sink, reg);

        p.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 5);
    }

    #[test]
    fn pipeline_guard_drops() {
        fn sink(mut out: ResMut<u64>, val: Option<u64>) {
            *out = val.unwrap_or(999);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64, reg)
            .guard(|v: &u64| *v > 10, reg)
            .then(sink, reg);

        p.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 999);
    }

    // -- Tap combinator --

    #[test]
    fn pipeline_tap_observes_without_changing() {
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<bool>(false);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64 * 2, reg)
            .tap(
                |w: &mut World, val: &u64| {
                    *w.resource_mut::<bool>() = *val == 10;
                },
                reg,
            )
            .then(sink, reg);

        p.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 10); // value passed through
        assert!(*world.resource::<bool>()); // tap fired
    }

    // -- Route combinator --

    #[test]
    fn pipeline_route_true_arm() {
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let arm_t = PipelineBuilder::new().then(|x: u64| x * 2, reg);
        let arm_f = PipelineBuilder::new().then(|x: u64| x * 3, reg);

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64, reg)
            .route(|v: &u64| *v > 3, reg, arm_t, arm_f)
            .then(sink, reg);

        p.run(&mut world, 5u32); // 5 > 3 → true arm → double → 10
        assert_eq!(*world.resource::<u64>(), 10);
    }

    #[test]
    fn pipeline_route_false_arm() {
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let arm_t = PipelineBuilder::new().then(|x: u64| x * 2, reg);
        let arm_f = PipelineBuilder::new().then(|x: u64| x * 3, reg);

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64, reg)
            .route(|v: &u64| *v > 10, reg, arm_t, arm_f)
            .then(sink, reg);

        p.run(&mut world, 5u32); // 5 <= 10 → false arm → triple → 15
        assert_eq!(*world.resource::<u64>(), 15);
    }

    #[test]
    fn pipeline_route_nested() {
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        // N-ary via nesting: <5 → +100, 5..10 → +200, >=10 → +300
        let inner_t = PipelineBuilder::new().then(|x: u64| x + 200, reg);
        let inner_f = PipelineBuilder::new().then(|x: u64| x + 300, reg);
        let outer_t = PipelineBuilder::new().then(|x: u64| x + 100, reg);
        let outer_f = PipelineBuilder::new().then(|x: u64| x, reg).route(
            |v: &u64| *v < 10,
            reg,
            inner_t,
            inner_f,
        );

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64, reg)
            .route(|v: &u64| *v < 5, reg, outer_t, outer_f)
            .then(sink, reg);

        p.run(&mut world, 3u32); // 3 < 5 → +100 → 103
        assert_eq!(*world.resource::<u64>(), 103);

        p.run(&mut world, 7u32); // 7 >= 5, 7 < 10 → +200 → 207
        assert_eq!(*world.resource::<u64>(), 207);

        p.run(&mut world, 15u32); // 15 >= 5, 15 >= 10 → +300 → 315
        assert_eq!(*world.resource::<u64>(), 315);
    }

    // -- Tee combinator --

    #[test]
    fn pipeline_tee_side_effect_chain() {
        use crate::dag::DagArmSeed;

        fn log_step(mut counter: ResMut<u32>, _val: &u64) {
            *counter += 1;
        }
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<u32>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let side = DagArmSeed::new().then(log_step, reg);

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64 * 2, reg)
            .tee(side)
            .then(sink, reg);

        p.run(&mut world, 5u32);
        assert_eq!(*world.resource::<u64>(), 10); // value passed through
        assert_eq!(*world.resource::<u32>(), 1); // side-effect fired

        p.run(&mut world, 7u32);
        assert_eq!(*world.resource::<u64>(), 14);
        assert_eq!(*world.resource::<u32>(), 2);
    }

    // -- Dedup combinator --

    #[test]
    fn pipeline_dedup_suppresses_unchanged() {
        fn sink(mut out: ResMut<u32>, val: Option<u64>) {
            if val.is_some() {
                *out += 1;
            }
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u32>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64 / 2, reg)
            .dedup()
            .then(sink, reg);

        p.run(&mut world, 4u32); // 2 — first, Some
        assert_eq!(*world.resource::<u32>(), 1);

        p.run(&mut world, 5u32); // 2 — same, None
        assert_eq!(*world.resource::<u32>(), 1);

        p.run(&mut world, 6u32); // 3 — changed, Some
        assert_eq!(*world.resource::<u32>(), 2);
    }

    // -- Bool combinators --

    #[test]
    fn pipeline_not() {
        fn sink(mut out: ResMut<bool>, val: bool) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(false);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x > 5, reg)
            .not()
            .then(sink, reg);

        p.run(&mut world, 3u32); // 3 > 5 = false, not = true
        assert!(*world.resource::<bool>());

        p.run(&mut world, 10u32); // 10 > 5 = true, not = false
        assert!(!*world.resource::<bool>());
    }

    #[test]
    fn pipeline_and() {
        fn sink(mut out: ResMut<bool>, val: bool) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(true);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x > 5, reg)
            .and(|w: &mut World| *w.resource::<bool>(), reg)
            .then(sink, reg);

        p.run(&mut world, 10u32); // true && true = true
        assert!(*world.resource::<bool>());

        *world.resource_mut::<bool>() = false;
        p.run(&mut world, 10u32); // true && false = false
        assert!(!*world.resource::<bool>());
    }

    #[test]
    fn pipeline_or() {
        fn sink(mut out: ResMut<bool>, val: bool) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(false);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x > 5, reg)
            .or(|w: &mut World| *w.resource::<bool>(), reg)
            .then(sink, reg);

        p.run(&mut world, 3u32); // false || false = false
        assert!(!*world.resource::<bool>());

        *world.resource_mut::<bool>() = true;
        p.run(&mut world, 3u32); // false || true = true
        assert!(*world.resource::<bool>());
    }

    #[test]
    fn pipeline_xor() {
        fn sink(mut out: ResMut<bool>, val: bool) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(true);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x > 5, reg)
            .xor(|w: &mut World| *w.resource::<bool>(), reg)
            .then(sink, reg);

        p.run(&mut world, 10u32); // true ^ true = false
        assert!(!*world.resource::<bool>());
    }

    // =========================================================================
    // Splat — tuple destructuring
    // =========================================================================

    #[test]
    fn splat2_closure_on_start() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<(u32, u64)>::new()
            .splat()
            .then(|a: u32, b: u64| a as u64 + b, r);
        assert_eq!(p.run(&mut world, (3, 7)), 10);
    }

    #[test]
    fn splat2_named_fn_with_param() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(100);
        let mut world = wb.build();

        fn process(base: Res<u64>, a: u32, b: u32) -> u64 {
            *base + a as u64 + b as u64
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<(u32, u32)>::new()
            .splat()
            .then(process, r);
        assert_eq!(p.run(&mut world, (3, 7)), 110);
    }

    #[test]
    fn splat2_mid_chain() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| (x, x * 2), r)
            .splat()
            .then(|a: u32, b: u32| a as u64 + b as u64, r);
        assert_eq!(p.run(&mut world, 5), 15); // 5 + 10
    }

    #[test]
    fn splat3_closure_on_start() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<(u32, u32, u32)>::new()
            .splat()
            .then(|a: u32, b: u32, c: u32| a + b + c, r);
        assert_eq!(p.run(&mut world, (1, 2, 3)), 6);
    }

    #[test]
    fn splat3_named_fn_with_param() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        let mut world = wb.build();

        fn process(factor: Res<u64>, a: u32, b: u32, c: u32) -> u64 {
            *factor * (a + b + c) as u64
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<(u32, u32, u32)>::new()
            .splat()
            .then(process, r);
        assert_eq!(p.run(&mut world, (1, 2, 3)), 60);
    }

    #[test]
    fn splat4_mid_chain() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| (x, x + 1, x + 2, x + 3), r)
            .splat()
            .then(|a: u32, b: u32, c: u32, d: u32| (a + b + c + d) as u64, r);
        assert_eq!(p.run(&mut world, 10), 46); // 10+11+12+13
    }

    #[test]
    fn splat5_closure_on_start() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<(u8, u8, u8, u8, u8)>::new().splat().then(
            |a: u8, b: u8, c: u8, d: u8, e: u8| {
                (a as u64) + (b as u64) + (c as u64) + (d as u64) + (e as u64)
            },
            r,
        );
        assert_eq!(p.run(&mut world, (1, 2, 3, 4, 5)), 15);
    }

    #[test]
    fn splat_build_into_handler() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn store(mut out: ResMut<u64>, a: u32, b: u32) {
            *out = a as u64 + b as u64;
        }

        let r = world.registry_mut();
        let mut pipeline = PipelineBuilder::<(u32, u32)>::new()
            .splat()
            .then(store, r)
            .build();

        pipeline.run(&mut world, (3, 7));
        assert_eq!(*world.resource::<u64>(), 10);
    }

    #[test]
    fn splat_build_batch() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn accumulate(mut sum: ResMut<u64>, a: u32, b: u32) {
            *sum += a as u64 + b as u64;
        }

        let r = world.registry_mut();
        let mut batch = PipelineBuilder::<(u32, u32)>::new()
            .splat()
            .then(accumulate, r)
            .build_batch(8);

        batch
            .input_mut()
            .extend_from_slice(&[(1, 2), (3, 4), (5, 6)]);
        batch.run(&mut world);
        assert_eq!(*world.resource::<u64>(), 21); // 3+7+11
    }

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn splat_access_conflict_detected() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn bad(a: ResMut<u64>, _b: ResMut<u64>, _x: u32, _y: u32) {
            let _ = a;
        }

        let r = world.registry_mut();
        // Should panic on duplicate ResMut<u64>
        let _ = PipelineBuilder::<(u32, u32)>::new().splat().then(bad, r);
    }

    // -- Then (previously switch) --

    #[test]
    fn pipeline_then_branching() {
        fn double(x: u32) -> u64 {
            x as u64 * 2
        }
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut pipeline = PipelineBuilder::<u32>::new()
            .then(double, reg)
            .then(|val: u64| if val > 10 { val * 100 } else { val + 1 }, reg)
            .then(sink, reg)
            .build();

        pipeline.run(&mut world, 10u32); // 20 > 10 → 2000
        assert_eq!(*world.resource::<u64>(), 2000);

        pipeline.run(&mut world, 3u32); // 6 <= 10 → 7
        assert_eq!(*world.resource::<u64>(), 7);
    }

    #[test]
    fn pipeline_then_3_way() {
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut pipeline = PipelineBuilder::<u32>::new()
            .then(
                |val: u32| match val % 3 {
                    0 => val as u64 + 100,
                    1 => val as u64 + 200,
                    _ => val as u64 + 300,
                },
                reg,
            )
            .then(sink, reg)
            .build();

        pipeline.run(&mut world, 6u32); // 6 % 3 == 0 → 106
        assert_eq!(*world.resource::<u64>(), 106);

        pipeline.run(&mut world, 7u32); // 7 % 3 == 1 → 207
        assert_eq!(*world.resource::<u64>(), 207);

        pipeline.run(&mut world, 8u32); // 8 % 3 == 2 → 308
        assert_eq!(*world.resource::<u64>(), 308);
    }

    #[test]
    fn pipeline_then_with_resolve_step() {
        fn add_offset(offset: Res<i64>, val: u32) -> u64 {
            (*offset + val as i64) as u64
        }
        fn plain_double(val: u32) -> u64 {
            val as u64 * 2
        }
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<i64>(100);
        let mut world = wb.build();
        let reg = world.registry();

        let mut arm_offset = resolve_step(add_offset, reg);
        let mut arm_double = resolve_step(plain_double, reg);

        let mut pipeline = PipelineBuilder::<u32>::new()
            .then(
                move |world: &mut World, val: u32| {
                    if val > 10 {
                        arm_offset(world, val)
                    } else {
                        arm_double(world, val)
                    }
                },
                reg,
            )
            .then(sink, reg)
            .build();

        pipeline.run(&mut world, 20u32); // > 10 → offset → 100 + 20 = 120
        assert_eq!(*world.resource::<u64>(), 120);

        pipeline.run(&mut world, 5u32); // <= 10 → double → 10
        assert_eq!(*world.resource::<u64>(), 10);
    }

    #[test]
    fn batch_pipeline_then_branching() {
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out += val;
        }

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut batch = PipelineBuilder::<u32>::new()
            .then(
                |val: u32| {
                    if val.is_multiple_of(2) {
                        val as u64 * 10
                    } else {
                        val as u64
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

    // -- IntoRefStep with Param: named functions --

    #[test]
    fn guard_named_fn_with_param() {
        fn above_threshold(threshold: Res<u64>, val: &u64) -> bool {
            *val > *threshold
        }
        fn sink(mut out: ResMut<i64>, val: Option<u64>) {
            *out = val.map_or(-1, |v| v as i64);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(5); // threshold
        wb.register::<i64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64, reg)
            .guard(above_threshold, reg)
            .then(sink, reg);

        p.run(&mut world, 10u32); // 10 > 5 → Some(10)
        assert_eq!(*world.resource::<i64>(), 10);

        p.run(&mut world, 3u32); // 3 <= 5 → None → -1
        assert_eq!(*world.resource::<i64>(), -1);
    }

    #[test]
    fn filter_named_fn_with_param() {
        fn is_allowed(allowed: Res<u64>, val: &u64) -> bool {
            *val != *allowed
        }
        fn count(mut ctr: ResMut<i64>, _val: u64) {
            *ctr += 1;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(42); // blocked value
        wb.register::<i64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Option<u64> { Some(x as u64) }, reg)
            .filter(is_allowed, reg)
            .map(count, reg)
            .unwrap_or(());

        for v in [1u32, 42, 5, 42, 10] {
            p.run(&mut world, v);
        }
        assert_eq!(*world.resource::<i64>(), 3); // 42 filtered out twice
    }

    #[test]
    fn inspect_named_fn_with_param() {
        fn log_value(mut log: ResMut<Vec<u64>>, val: &u64) {
            log.push(*val);
        }
        let mut wb = WorldBuilder::new();
        wb.register::<Vec<u64>>(Vec::new());
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| -> Option<u64> { Some(x as u64) }, reg)
            .inspect(log_value, reg)
            .unwrap_or(0);

        for v in [1u32, 2, 3] {
            p.run(&mut world, v);
        }
        assert_eq!(world.resource::<Vec<u64>>().as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn tap_named_fn_with_param() {
        fn observe(mut log: ResMut<Vec<u64>>, val: &u64) {
            log.push(*val);
        }
        fn sink(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        wb.register::<Vec<u64>>(Vec::new());
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|x: u32| x as u64, reg)
            .tap(observe, reg)
            .then(sink, reg);

        p.run(&mut world, 7u32);
        assert_eq!(*world.resource::<u64>(), 7);
        assert_eq!(world.resource::<Vec<u64>>().as_slice(), &[7]);
    }

    // -- IntoProducer with Param: named functions --

    #[test]
    fn and_named_fn_with_param() {
        fn check_enabled(flag: Res<bool>) -> bool {
            *flag
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(true);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| true, reg)
            .and(check_enabled, reg);

        assert!(p.run(&mut world, 0u32));

        *world.resource_mut::<bool>() = false;
        assert!(!p.run(&mut world, 0u32)); // short-circuit: true AND false
    }

    #[test]
    fn or_named_fn_with_param() {
        fn check_enabled(flag: Res<bool>) -> bool {
            *flag
        }
        let mut wb = WorldBuilder::new();
        wb.register::<bool>(true);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(|_x: u32| false, reg)
            .or(check_enabled, reg);

        assert!(p.run(&mut world, 0u32)); // false OR true

        *world.resource_mut::<bool>() = false;
        assert!(!p.run(&mut world, 0u32)); // false OR false
    }

    #[test]
    fn on_none_named_fn_with_param() {
        fn log_miss(mut ctr: ResMut<u64>) {
            *ctr += 1;
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(
                |x: u32| -> Option<u32> { if x > 5 { Some(x) } else { None } },
                reg,
            )
            .on_none(log_miss, reg)
            .unwrap_or(0);

        for v in [1u32, 10, 3, 20] {
            p.run(&mut world, v);
        }
        assert_eq!(*world.resource::<u64>(), 2); // 1 and 3 are None
    }

    #[test]
    fn ok_or_else_named_fn_with_param() {
        fn make_error(msg: Res<String>) -> String {
            (*msg).clone()
        }
        let mut wb = WorldBuilder::new();
        wb.register::<String>("not found".into());
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(
                |x: u32| -> Option<u32> { if x > 0 { Some(x) } else { None } },
                reg,
            )
            .ok_or_else(make_error, reg);

        let r: Result<u32, String> = p.run(&mut world, 5u32);
        assert_eq!(r, Ok(5));

        let r: Result<u32, String> = p.run(&mut world, 0u32);
        assert_eq!(r, Err("not found".into()));
    }

    #[test]
    fn unwrap_or_else_option_named_fn_with_param() {
        fn fallback(default: Res<u64>) -> u64 {
            *default
        }
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(42);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(
                |x: u32| -> Option<u64> { if x > 0 { Some(x as u64) } else { None } },
                reg,
            )
            .unwrap_or_else(fallback, reg);

        assert_eq!(p.run(&mut world, 5u32), 5);
        assert_eq!(p.run(&mut world, 0u32), 42);
    }

    // -- IntoStep with Opaque: &mut World closures --

    #[test]
    fn map_err_named_fn_with_param() {
        fn tag_error(prefix: Res<String>, err: String) -> String {
            format!("{}: {err}", &*prefix)
        }
        fn sink(mut out: ResMut<String>, val: Result<u32, String>) {
            match val {
                Ok(v) => *out = format!("ok:{v}"),
                Err(e) => *out = e,
            }
        }
        let mut wb = WorldBuilder::new();
        wb.register::<String>("ERR".into());
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u32>::new()
            .then(
                |x: u32| -> Result<u32, String> { if x > 0 { Ok(x) } else { Err("zero".into()) } },
                reg,
            )
            .map_err(tag_error, reg)
            .then(sink, reg);

        p.run(&mut world, 0u32);
        assert_eq!(world.resource::<String>().as_str(), "ERR: zero");

        p.run(&mut world, 5u32);
        assert_eq!(world.resource::<String>().as_str(), "ok:5");
    }

    // =========================================================================
    // Scan combinator
    // =========================================================================

    #[test]
    fn scan_arity0_closure_running_sum() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u64>::new().then(|x: u64| x, reg).scan(
            0u64,
            |acc: &mut u64, val: u64| {
                *acc += val;
                Some(*acc)
            },
            reg,
        );

        assert_eq!(p.run(&mut world, 10), Some(10));
        assert_eq!(p.run(&mut world, 20), Some(30));
        assert_eq!(p.run(&mut world, 5), Some(35));
    }

    #[test]
    fn scan_named_fn_with_param() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(100);
        let mut world = wb.build();
        let reg = world.registry();

        fn threshold_scan(limit: Res<u64>, acc: &mut u64, val: u64) -> Option<u64> {
            *acc += val;
            if *acc > *limit { Some(*acc) } else { None }
        }

        let mut p =
            PipelineBuilder::<u64>::new()
                .then(|x: u64| x, reg)
                .scan(0u64, threshold_scan, reg);

        assert_eq!(p.run(&mut world, 50), None);
        assert_eq!(p.run(&mut world, 30), None);
        assert_eq!(p.run(&mut world, 25), Some(105));
    }

    #[test]
    fn scan_opaque_closure() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u64>::new().then(|x: u64| x, reg).scan(
            0u64,
            |world: &mut World, acc: &mut u64, val: u64| {
                let factor = *world.resource::<u64>();
                *acc += val * factor;
                Some(*acc)
            },
            reg,
        );

        assert_eq!(p.run(&mut world, 1), Some(10));
        assert_eq!(p.run(&mut world, 2), Some(30));
    }

    #[test]
    fn scan_suppression_returns_none() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u64>::new().then(|x: u64| x, reg).scan(
            0u64,
            |acc: &mut u64, val: u64| -> Option<u64> {
                *acc += val;
                if *acc > 50 { Some(*acc) } else { None }
            },
            reg,
        );

        assert_eq!(p.run(&mut world, 20), None);
        assert_eq!(p.run(&mut world, 20), None);
        assert_eq!(p.run(&mut world, 20), Some(60));
    }

    #[test]
    fn scan_on_pipeline_start() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<u64>::new().scan(
            0u64,
            |acc: &mut u64, val: u64| {
                *acc += val;
                *acc
            },
            reg,
        );

        assert_eq!(p.run(&mut world, 5), 5);
        assert_eq!(p.run(&mut world, 3), 8);
        assert_eq!(p.run(&mut world, 2), 10);
    }

    #[test]
    fn scan_persistence_across_batch() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn store(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }

        let mut p = PipelineBuilder::<u64>::new()
            .then(|x: u64| x, reg)
            .scan(
                0u64,
                |acc: &mut u64, val: u64| {
                    *acc += val;
                    *acc
                },
                reg,
            )
            .then(store, reg)
            .build_batch(4);

        p.input_mut().extend([1, 2, 3]);
        p.run(&mut world);

        // Accumulator persists: 1, 3, 6
        assert_eq!(*world.resource::<u64>(), 6);

        p.input_mut().push(4);
        p.run(&mut world);
        // acc = 6 + 4 = 10
        assert_eq!(*world.resource::<u64>(), 10);
    }

    // =========================================================================
    // Build — Option<()> terminal
    // =========================================================================

    #[test]
    fn build_option_unit_terminal() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let r = world.registry_mut();

        fn check(x: u32) -> Option<u32> {
            if x > 5 { Some(x) } else { None }
        }
        fn store(mut out: ResMut<u64>, val: u32) {
            *out += val as u64;
        }

        // .map(store) on Option<u32> produces Option<()> — build() must work
        let mut p = PipelineBuilder::<u32>::new()
            .then(check, r)
            .map(store, r)
            .build();

        p.run(&mut world, 3); // None, skipped
        assert_eq!(*world.resource::<u64>(), 0);
        p.run(&mut world, 7); // Some, stores
        assert_eq!(*world.resource::<u64>(), 7);
        p.run(&mut world, 10);
        assert_eq!(*world.resource::<u64>(), 17);
    }

    #[test]
    fn build_option_unit_boxes_into_handler() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let r = world.registry_mut();

        fn double(x: u32) -> Option<u64> {
            if x > 0 { Some(x as u64 * 2) } else { None }
        }
        fn store(mut out: ResMut<u64>, val: u64) {
            *out += val;
        }

        let mut h: Box<dyn Handler<u32>> = Box::new(
            PipelineBuilder::<u32>::new()
                .then(double, r)
                .map(store, r)
                .build(),
        );
        h.run(&mut world, 0); // None
        assert_eq!(*world.resource::<u64>(), 0);
        h.run(&mut world, 5); // 10
        assert_eq!(*world.resource::<u64>(), 10);
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
        fn store(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }

        // msg declared before p so it outlives the pipeline (drop order).
        // Matches real-world usage: pipeline lives long, events come and go.
        let msg = vec![1u8, 2, 3];
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<&[u8]>::new()
            .then(decode, r)
            .then(store, r)
            .build();

        p.run(&mut world, &msg);
        assert_eq!(*world.resource::<u64>(), 3);
    }

    #[test]
    fn build_borrowed_event_option_unit() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn decode(msg: &[u8]) -> Option<u64> {
            if msg.is_empty() {
                None
            } else {
                Some(msg.len() as u64)
            }
        }
        fn store(mut out: ResMut<u64>, val: u64) {
            *out = val;
        }

        let empty = vec![];
        let data = vec![1u8, 2, 3];
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<&[u8]>::new()
            .then(decode, r)
            .map(store, r)
            .build();

        p.run(&mut world, &empty); // None
        assert_eq!(*world.resource::<u64>(), 0);
        p.run(&mut world, &data); // Some(3)
        assert_eq!(*world.resource::<u64>(), 3);
    }

    // =========================================================================
    // NoEvent — pipeline steps with In = () that omit the input parameter
    // =========================================================================

    #[test]
    fn no_event_step_arity_0() {
        let mut world = WorldBuilder::new().build();
        let r = world.registry_mut();
        let mut p = PipelineBuilder::<()>::new().then(|| 42u64, r);
        assert_eq!(p.run(&mut world, ()), 42);
    }

    #[test]
    fn no_event_step_arity_1() {
        use crate::no_event;

        let mut wb = WorldBuilder::new();
        wb.register::<u32>(10);
        let mut world = wb.build();

        fn read_config(config: Res<u32>) -> u64 {
            *config as u64
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<()>::new().then(no_event(read_config), r);
        assert_eq!(p.run(&mut world, ()), 10);
    }

    #[test]
    fn no_event_step_chained() {
        use crate::no_event;

        let mut wb = WorldBuilder::new();
        wb.register::<u32>(5);
        let mut world = wb.build();

        fn read_val(val: Res<u32>) -> u64 {
            *val as u64
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<()>::new()
            .then(no_event(read_val), r)
            .then(|x: u64| x * 2, r);
        assert_eq!(p.run(&mut world, ()), 10);
    }

    #[test]
    fn no_event_step_as_handler() {
        use crate::no_event;

        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();

        fn write_val(mut out: ResMut<u64>) {
            *out += 1;
        }

        let r = world.registry_mut();
        let mut p = PipelineBuilder::<()>::new()
            .then(no_event(write_val), r)
            .build();

        p.run(&mut world, ());
        p.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 2);
    }
}
