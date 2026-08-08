// Builder return types are necessarily complex — each combinator returns
// CtxPipelineChain<C, In, Out, NodeType<Chain, ...>>. Same pattern as iterator adapters.
#![allow(clippy::type_complexity)]
// Handler arity is architecturally required by the Param trait — handlers
// take N typed parameters and the macro-generated dispatch impls expand
// per-arity into call_inner functions with N + Input arguments. Module-level
// allow rather than one inline attribute per arity expansion.
#![allow(clippy::too_many_arguments)]

//! Context-aware pipeline dispatch.
//!
//! Mirrors the [`pipeline`](crate::pipeline) module but threads `&mut C`
//! (per-instance context) through every step. Designed for use inside
//! [`Callback`](crate::Callback) where each handler instance owns private
//! state that pipeline steps need to read or mutate.
//!
//! # Step function convention
//!
//! Context first, then Params, then step input last:
//!
//! ```ignore
//! fn check_retries(ctx: &mut ReconnectCtx, config: Res<Config>, _input: ()) -> Option<()> {
//!     if ctx.retries < config.max_retries { ctx.retries += 1; Some(()) } else { None }
//! }
//! fn attempt_connect(ctx: &mut ReconnectCtx, _input: ()) -> Result<TcpStream, io::Error> {
//!     TcpStream::connect(&ctx.addr)
//! }
//! ```
//!
//! # Integration with Callback
//!
//! The built [`CtxPipeline`] implements [`CtxStepCall`] — it takes
//! `&mut C`, `&mut World`, and `In`, returning `Out`.
//!
//! To use a pipeline from a [`Handler`](crate::Handler), create a normal
//! [`Callback`](crate::Callback) whose handler function owns or accesses
//! the context `C` and calls the pipeline via its `run` method, passing
//! `&mut C`, `&mut World`, and the handler input. For pipelines that
//! return a non-unit value, use [`CtxPipelineChain::run`] directly —
//! `.build()` is only available when `Out = ()` or `Out = Option<()>`.
//!
//! # Three-tier step resolution
//!
//! Each combinator accepts functions via three tiers, matching the
//! [`pipeline`](crate::pipeline) module:
//!
//! 1. **Named function with Params** — `fn(&mut C, Res<T>, In) -> Out`
//! 2. **Arity-0 closure** — `FnMut(&mut C, In) -> Out`
//! 3. **[`Opaque`] closure** — `FnMut(&mut C, &mut World, In) -> Out`
//!    (raw World access, no Param resolution)
//!
//! # Deferred combinators
//!
//! The following combinators from [`pipeline`](crate::pipeline) are not yet
//! implemented: `scan`, `dedup`, `dispatch`, `route`, `tee`, `splat`,
//! `cloned`, `not`/`and`/`or`/`xor` (bool), `ok_or_else`, `or_else`,
//! `Result::unwrap_or_else`, and `BatchPipeline`. These can be added when
//! a concrete use case requires them.

use std::marker::PhantomData;

use crate::handler::{Opaque, Param};
use crate::world::{Registry, World};

// =============================================================================
// CtxStep — pre-resolved step with Param state (context-aware)
// =============================================================================

/// Internal: pre-resolved context-aware step with cached Param state.
#[doc(hidden)]
pub struct CtxStep<F, Params: Param> {
    f: F,
    state: Params::State,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

// =============================================================================
// CtxStepCall — callable trait for context-aware resolved steps
// =============================================================================

/// Internal: callable trait for context-aware resolved steps.
///
/// Like [`StepCall`](crate::pipeline::StepCall) but with `&mut C` context.
#[doc(hidden)]
pub trait CtxStepCall<C, In> {
    /// The output type of this step.
    type Out;
    /// Call this step with context, world, and input.
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Self::Out;
}

// =============================================================================
// IntoCtxStep — converts a named function into a context-aware step
// =============================================================================

/// Converts a named function into a pre-resolved context-aware pipeline step.
///
/// Three tiers of resolution (same API for all):
///
/// | Params | Function shape | Example |
/// |--------|---------------|---------|
/// | Named | `fn(&mut C, Res<T>, In) -> Out` | `fn process(ctx: &mut Ctx, cfg: Res<Config>, x: u32) -> u64` |
/// | `()` | `FnMut(&mut C, In) -> Out` | `\|ctx: &mut Ctx, x: u32\| x * 2` |
/// | [`Opaque`] | `FnMut(&mut C, &mut World, In) -> Out` | `\|ctx: &mut Ctx, w: &mut World, x: u32\| { ... }` |
///
/// # Examples
///
/// ```ignore
/// // Arity 0 — closure works
/// let step = (|ctx: &mut Ctx, x: u32| { ctx.count += 1; x * 2 }).into_ctx_step(registry);
///
/// // Arity 1 — named function required
/// fn validate(ctx: &mut Ctx, config: Res<Config>, order: Order) -> Option<ValidOrder> { .. }
/// let step = validate.into_ctx_step(registry);
///
/// // Opaque — raw World access
/// let step = (|ctx: &mut Ctx, w: &mut World, x: u32| { ... }).into_ctx_step(registry);
/// ```
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a context-aware pipeline step",
    note = "ctx step signature: `fn(&mut C, Params..., In) -> Out` — context first, resources, input last",
    note = "for raw World access: `fn(&mut C, &mut World, In) -> Out`",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoCtxStep<C, In, Out, Params> {
    /// The concrete resolved step type.
    type Step: CtxStepCall<C, In, Out = Out>;

    /// Resolve Param state from the registry and produce a step.
    fn into_ctx_step(self, registry: &Registry) -> Self::Step;
}

// =============================================================================
// Arity 0 — fn(&mut C, In) -> Out — closures work
// =============================================================================

impl<C, In, Out, F: FnMut(&mut C, In) -> Out + 'static> CtxStepCall<C, In> for CtxStep<F, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, _world: &mut World, input: In) -> Out {
        (self.f)(ctx, input)
    }
}

impl<C, In, Out, F: FnMut(&mut C, In) -> Out + 'static> IntoCtxStep<C, In, Out, ()> for F {
    type Step = CtxStep<F, ()>;

    fn into_ctx_step(self, registry: &Registry) -> Self::Step {
        CtxStep {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// Arities 1-8 via macro — HRTB with -> Out
// =============================================================================

macro_rules! impl_into_ctx_step {
    ($($P:ident),+) => {
        impl<C, In, Out, F: 'static, $($P: Param + 'static),+>
            CtxStepCall<C, In> for CtxStep<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+ In) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+ In) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Out {
                fn call_inner<Ctx, $($P,)+ Input, Output>(
                    mut f: impl FnMut(&mut Ctx, $($P,)+ Input) -> Output,
                    ctx: &mut Ctx,
                    $($P: $P,)+
                    input: Input,
                ) -> Output {
                    f(ctx, $($P,)+ input)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, ctx, $($P,)+ input)
            }
        }

        impl<C, In, Out, F: 'static, $($P: Param + 'static),+>
            IntoCtxStep<C, In, Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+ In) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+ In) -> Out,
        {
            type Step = CtxStep<F, ($($P,)+)>;

            fn into_ctx_step(self, registry: &Registry) -> Self::Step {
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
                CtxStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_ctx_step);

// =============================================================================
// No-input impls — IntoCtxStep with In = (), no trailing input parameter
// =============================================================================

use crate::handler::NoEvent;

// Arity 0: fn(&mut C) -> Out — no params, no input
impl<C, Out, F: FnMut(&mut C) -> Out + 'static> CtxStepCall<C, ()> for CtxStep<NoEvent<F>, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, _world: &mut World, _input: ()) -> Out {
        (self.f.0)(ctx)
    }
}

impl<C, Out, F: FnMut(&mut C) -> Out + 'static> IntoCtxStep<C, (), Out, NoEvent<F>> for F {
    type Step = CtxStep<NoEvent<F>, ()>;

    fn into_ctx_step(self, registry: &Registry) -> Self::Step {
        CtxStep {
            f: NoEvent(self),
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// Arities 1-8: fn(&mut C, Params...) -> Out — no trailing input
macro_rules! impl_into_ctx_step_no_event {
    ($($P:ident),+) => {
        impl<C, Out, F: 'static, $($P: Param + 'static),+>
            CtxStepCall<C, ()> for CtxStep<NoEvent<F>, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, ctx: &mut C, world: &mut World, _input: ()) -> Out {
                fn call_inner<Ctx, $($P,)+ Output>(
                    mut f: impl FnMut(&mut Ctx, $($P,)+) -> Output,
                    ctx: &mut Ctx,
                    $($P: $P,)+
                ) -> Output {
                    f(ctx, $($P,)+)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same Registry
                // that built this World. Borrows are disjoint — enforced by
                // conflict detection at build time.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f.0, ctx, $($P,)+)
            }
        }

        impl<C, Out, F: 'static, $($P: Param + 'static),+>
            IntoCtxStep<C, (), Out, ($($P,)+)> for NoEvent<F>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+) -> Out,
        {
            type Step = CtxStep<NoEvent<F>, ($($P,)+)>;

            fn into_ctx_step(self, registry: &Registry) -> Self::Step {
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
                CtxStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_ctx_step_no_event);

// -- Opaque: FnMut(&mut C, &mut World, In) -> Out ----------------------------

/// Internal: wrapper for opaque closures used as context-aware steps.
///
/// Unlike [`CtxStep<F, P>`] which stores resolved `Param::State`, this
/// holds only the function — the closure receives `&mut World` directly.
#[doc(hidden)]
pub struct CtxOpaqueStep<F> {
    f: F,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

impl<C, In, Out, F: FnMut(&mut C, &mut World, In) -> Out + 'static> CtxStepCall<C, In>
    for CtxOpaqueStep<F>
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Out {
        (self.f)(ctx, world, input)
    }
}

impl<C, In, Out, F: FnMut(&mut C, &mut World, In) -> Out + 'static> IntoCtxStep<C, In, Out, Opaque>
    for F
{
    type Step = CtxOpaqueStep<F>;

    fn into_ctx_step(self, _registry: &Registry) -> Self::Step {
        CtxOpaqueStep {
            f: self,
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// CtxRefStepCall / IntoCtxRefStep — context-aware step taking &In
// =============================================================================

/// Internal: callable trait for context-aware steps taking input by reference.
///
/// Used by combinators like `tap`, `guard`, `filter` that observe the
/// value without consuming it.
#[doc(hidden)]
pub trait CtxRefStepCall<C, In> {
    /// The output type of this step.
    type Out;
    /// Call this step with context, world, and borrowed input.
    fn call(&mut self, ctx: &mut C, world: &mut World, input: &In) -> Self::Out;
}

/// Converts a function into a context-aware step taking input by reference.
///
/// Used by combinators like `tap`, `guard`, `filter`, `inspect` that
/// observe the value without consuming it.
///
/// | Params | Function shape | Example |
/// |--------|---------------|---------|
/// | Named | `fn(&mut C, Res<T>, &In) -> Out` | `fn check(ctx: &mut Ctx, cfg: Res<Config>, o: &Order) -> bool` |
/// | `()` | `FnMut(&mut C, &In) -> Out` | `\|ctx: &mut Ctx, o: &Order\| o.qty > 0` |
/// | [`Opaque`] | `FnMut(&mut C, &mut World, &In) -> Out` | `\|ctx: &mut Ctx, w: &mut World, o: &Order\| { ... }` |
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a context-aware reference step",
    note = "ctx ref step signature: `fn(&mut C, Params..., &In) -> Out`",
    note = "for raw World access: `fn(&mut C, &mut World, &In) -> Out`",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoCtxRefStep<C, In, Out, Params> {
    /// The concrete resolved step type.
    type Step: CtxRefStepCall<C, In, Out = Out>;

    /// Resolve Param state from the registry and produce a step.
    fn into_ctx_ref_step(self, registry: &Registry) -> Self::Step;
}

// -- Arity 0: FnMut(&mut C, &In) -> Out — closures work ----------------------

impl<C, In, Out, F: FnMut(&mut C, &In) -> Out + 'static> CtxRefStepCall<C, In> for CtxStep<F, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, _world: &mut World, input: &In) -> Out {
        (self.f)(ctx, input)
    }
}

impl<C, In, Out, F: FnMut(&mut C, &In) -> Out + 'static> IntoCtxRefStep<C, In, Out, ()> for F {
    type Step = CtxStep<F, ()>;

    fn into_ctx_ref_step(self, registry: &Registry) -> Self::Step {
        CtxStep {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// -- Arities 1-8: named functions with Param resolution -----------------------

macro_rules! impl_into_ctx_ref_step {
    ($($P:ident),+) => {
        impl<C, In, Out, F: 'static, $($P: Param + 'static),+>
            CtxRefStepCall<C, In> for CtxStep<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+ &In) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+ &In) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, ctx: &mut C, world: &mut World, input: &In) -> Out {
                fn call_inner<Ctx, $($P,)+ Input: ?Sized, Output>(
                    mut f: impl FnMut(&mut Ctx, $($P,)+ &Input) -> Output,
                    ctx: &mut Ctx,
                    $($P: $P,)+
                    input: &Input,
                ) -> Output {
                    f(ctx, $($P,)+ input)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same
                // Registry that built this World. Single-threaded sequential
                // dispatch ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, ctx, $($P,)+ input)
            }
        }

        impl<C, In, Out, F: 'static, $($P: Param + 'static),+>
            IntoCtxRefStep<C, In, Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+ &In) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+ &In) -> Out,
        {
            type Step = CtxStep<F, ($($P,)+)>;

            fn into_ctx_ref_step(self, registry: &Registry) -> Self::Step {
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
                CtxStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_ctx_ref_step);

// -- Opaque: FnMut(&mut C, &mut World, &In) -> Out ---------------------------

/// Internal: wrapper for opaque closures taking input by reference.
#[doc(hidden)]
pub struct CtxOpaqueRefStep<F> {
    f: F,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

impl<C, In, Out, F: FnMut(&mut C, &mut World, &In) -> Out + 'static> CtxRefStepCall<C, In>
    for CtxOpaqueRefStep<F>
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: &In) -> Out {
        (self.f)(ctx, world, input)
    }
}

impl<C, In, Out, F: FnMut(&mut C, &mut World, &In) -> Out + 'static>
    IntoCtxRefStep<C, In, Out, Opaque> for F
{
    type Step = CtxOpaqueRefStep<F>;

    fn into_ctx_ref_step(self, _registry: &Registry) -> Self::Step {
        CtxOpaqueRefStep {
            f: self,
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// CtxProducerCall / IntoCtxProducer — context-aware producer (no pipeline input)
// =============================================================================

/// Internal: callable trait for context-aware producers.
///
/// Used by combinators like `on_none`, `unwrap_or_else`.
#[doc(hidden)]
pub trait CtxProducerCall<C> {
    /// The output type of this producer.
    type Out;
    /// Call this producer with context and world.
    fn call(&mut self, ctx: &mut C, world: &mut World) -> Self::Out;
}

/// Converts a function into a context-aware producer step.
///
/// Used by combinators like `on_none`, `unwrap_or_else`.
///
/// | Params | Function shape | Example |
/// |--------|---------------|---------|
/// | Named | `fn(&mut C, Res<T>) -> Out` | `fn default_val(ctx: &mut Ctx, cfg: Res<Config>) -> u64` |
/// | `()` | `FnMut(&mut C) -> Out` | `\|ctx: &mut Ctx\| ctx.fallback` |
/// | [`Opaque`] | `FnMut(&mut C, &mut World) -> Out` | `\|ctx: &mut Ctx, w: &mut World\| { ... }` |
#[diagnostic::on_unimplemented(
    message = "this function cannot be used as a context-aware producer",
    note = "ctx producer signature: `fn(&mut C, Params...) -> Out`",
    note = "for raw World access: `fn(&mut C, &mut World) -> Out`",
    note = "closures with resource parameters are not supported — use a named `fn`"
)]
pub trait IntoCtxProducer<C, Out, Params> {
    /// The concrete resolved producer type.
    type Step: CtxProducerCall<C, Out = Out>;

    /// Resolve Param state from the registry and produce a step.
    fn into_ctx_producer(self, registry: &Registry) -> Self::Step;
}

// -- Arity 0: FnMut(&mut C) -> Out — closures work ----------------------------

impl<C, Out, F: FnMut(&mut C) -> Out + 'static> CtxProducerCall<C> for CtxStep<F, ()> {
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, _world: &mut World) -> Out {
        (self.f)(ctx)
    }
}

impl<C, Out, F: FnMut(&mut C) -> Out + 'static> IntoCtxProducer<C, Out, ()> for F {
    type Step = CtxStep<F, ()>;

    fn into_ctx_producer(self, registry: &Registry) -> Self::Step {
        CtxStep {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

// -- Arities 1-8: named functions with Param resolution -----------------------

macro_rules! impl_into_ctx_producer {
    ($($P:ident),+) => {
        impl<C, Out, F: 'static, $($P: Param + 'static),+>
            CtxProducerCall<C> for CtxStep<F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+) -> Out,
        {
            type Out = Out;
            #[inline(always)]
            #[allow(non_snake_case)]
            fn call(&mut self, ctx: &mut C, world: &mut World) -> Out {
                fn call_inner<Ctx, $($P,)+ Output>(
                    mut f: impl FnMut(&mut Ctx, $($P,)+) -> Output,
                    ctx: &mut Ctx,
                    $($P: $P,)+
                ) -> Output {
                    f(ctx, $($P,)+)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by Param::init() on the same
                // Registry that built this World. Single-threaded sequential
                // dispatch ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, ctx, $($P,)+)
            }
        }

        impl<C, Out, F: 'static, $($P: Param + 'static),+>
            IntoCtxProducer<C, Out, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+) -> Out +
                FnMut(&mut C, $($P::Item<'a>,)+) -> Out,
        {
            type Step = CtxStep<F, ($($P,)+)>;

            fn into_ctx_producer(self, registry: &Registry) -> Self::Step {
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
                CtxStep { f: self, state, name: std::any::type_name::<F>() }
            }
        }
    };
}

all_tuples!(impl_into_ctx_producer);

// -- Opaque: FnMut(&mut C, &mut World) -> Out --------------------------------

/// Internal: wrapper for opaque closures used as context-aware producers.
#[doc(hidden)]
pub struct CtxOpaqueProducer<F> {
    f: F,
    // Retained for future diagnostic/tracing use (step name in error messages).
    #[allow(dead_code)]
    name: &'static str,
}

impl<C, Out, F: FnMut(&mut C, &mut World) -> Out + 'static> CtxProducerCall<C>
    for CtxOpaqueProducer<F>
{
    type Out = Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World) -> Out {
        (self.f)(ctx, world)
    }
}

impl<C, Out, F: FnMut(&mut C, &mut World) -> Out + 'static> IntoCtxProducer<C, Out, Opaque> for F {
    type Step = CtxOpaqueProducer<F>;

    fn into_ctx_producer(self, _registry: &Registry) -> Self::Step {
        CtxOpaqueProducer {
            f: self,
            name: std::any::type_name::<F>(),
        }
    }
}

// =============================================================================
// CtxChainCall — callable trait for context-aware chain nodes
// =============================================================================

/// Internal: callable trait for context-aware chain nodes.
///
/// Like [`ChainCall`](crate::pipeline::ChainCall) but threads `&mut C`.
#[doc(hidden)]
pub trait CtxChainCall<C, In> {
    /// The output type of this chain node.
    type Out;
    /// Execute the chain with context, world, and input.
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Self::Out;
}

// =============================================================================
// Chain nodes — named types for context-aware pipeline composition
// =============================================================================

/// Identity passthrough node. Used as the initial chain element.
#[doc(hidden)]
pub struct CtxIdentityNode;

impl<C, In> CtxChainCall<C, In> for CtxIdentityNode {
    type Out = In;
    #[inline(always)]
    fn call(&mut self, _ctx: &mut C, _world: &mut World, input: In) -> In {
        input
    }
}

// -- Core (any Out) ----------------------------------------------------------

/// Chain node for `.then()` — transforms output via a context-aware step.
#[doc(hidden)]
pub struct CtxThenNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, Prev, S> CtxChainCall<C, In> for CtxThenNode<Prev, S>
where
    Prev: CtxChainCall<C, In>,
    S: CtxStepCall<C, Prev::Out>,
{
    type Out = S::Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> S::Out {
        let mid = self.prev.call(ctx, world, input);
        self.step.call(ctx, world, mid)
    }
}

/// Chain node for `.tap()` — side effect via `&Out`, value passes through.
#[doc(hidden)]
pub struct CtxTapNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, Prev, S> CtxChainCall<C, In> for CtxTapNode<Prev, S>
where
    Prev: CtxChainCall<C, In>,
    S: CtxRefStepCall<C, Prev::Out, Out = ()>,
{
    type Out = Prev::Out;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Prev::Out {
        let val = self.prev.call(ctx, world, input);
        self.step.call(ctx, world, &val);
        val
    }
}

/// Chain node for `.guard()` — wraps output in `Option` based on predicate.
#[doc(hidden)]
pub struct CtxGuardNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, Prev, S> CtxChainCall<C, In> for CtxGuardNode<Prev, S>
where
    Prev: CtxChainCall<C, In>,
    S: CtxRefStepCall<C, Prev::Out, Out = bool>,
{
    type Out = Option<Prev::Out>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<Prev::Out> {
        let val = self.prev.call(ctx, world, input);
        if self.step.call(ctx, world, &val) {
            Some(val)
        } else {
            None
        }
    }
}

// -- Option nodes ------------------------------------------------------------

/// Chain node for `.map()` on `Option<T>`.
#[doc(hidden)]
pub struct CtxMapOptionNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, Prev, S> CtxChainCall<C, In> for CtxMapOptionNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
    S: CtxStepCall<C, T>,
{
    type Out = Option<S::Out>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<S::Out> {
        match self.prev.call(ctx, world, input) {
            Some(val) => Some(self.step.call(ctx, world, val)),
            None => None,
        }
    }
}

/// Chain node for `.and_then()` on `Option<T>`.
#[doc(hidden)]
pub struct CtxAndThenNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, U, Prev, S> CtxChainCall<C, In> for CtxAndThenNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
    S: CtxStepCall<C, T, Out = Option<U>>,
{
    type Out = Option<U>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<U> {
        match self.prev.call(ctx, world, input) {
            Some(val) => self.step.call(ctx, world, val),
            None => None,
        }
    }
}

/// Chain node for `.filter()` on `Option<T>`.
#[doc(hidden)]
pub struct CtxFilterNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, Prev, S> CtxChainCall<C, In> for CtxFilterNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
    S: CtxRefStepCall<C, T, Out = bool>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<T> {
        match self.prev.call(ctx, world, input) {
            Some(val) if self.step.call(ctx, world, &val) => Some(val),
            _ => None,
        }
    }
}

/// Chain node for `.inspect()` on `Option<T>`.
#[doc(hidden)]
pub struct CtxInspectOptionNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, Prev, S> CtxChainCall<C, In> for CtxInspectOptionNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
    S: CtxRefStepCall<C, T, Out = ()>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<T> {
        let opt = self.prev.call(ctx, world, input);
        if let Some(ref val) = opt {
            self.step.call(ctx, world, val);
        }
        opt
    }
}

/// Chain node for `.on_none()` on `Option<T>`.
#[doc(hidden)]
pub struct CtxOnNoneNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) producer: S,
}

impl<C, In, T, Prev, S> CtxChainCall<C, In> for CtxOnNoneNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
    S: CtxProducerCall<C, Out = ()>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<T> {
        let opt = self.prev.call(ctx, world, input);
        if opt.is_none() {
            self.producer.call(ctx, world);
        }
        opt
    }
}

/// Chain node for `.unwrap_or_else()` on `Option<T>`.
#[doc(hidden)]
pub struct CtxUnwrapOrElseOptionNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) producer: S,
}

impl<C, In, T, Prev, S> CtxChainCall<C, In> for CtxUnwrapOrElseOptionNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
    S: CtxProducerCall<C, Out = T>,
{
    type Out = T;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> T {
        match self.prev.call(ctx, world, input) {
            Some(val) => val,
            None => self.producer.call(ctx, world),
        }
    }
}

// -- Result nodes ------------------------------------------------------------

/// Chain node for `.map()` on `Result<T, E>`.
#[doc(hidden)]
pub struct CtxMapResultNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, E, Prev, S> CtxChainCall<C, In> for CtxMapResultNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
    S: CtxStepCall<C, T>,
{
    type Out = Result<S::Out, E>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Result<S::Out, E> {
        match self.prev.call(ctx, world, input) {
            Ok(val) => Ok(self.step.call(ctx, world, val)),
            Err(e) => Err(e),
        }
    }
}

/// Chain node for `.and_then()` on `Result<T, E>`.
#[doc(hidden)]
pub struct CtxAndThenResultNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, U, E, Prev, S> CtxChainCall<C, In> for CtxAndThenResultNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
    S: CtxStepCall<C, T, Out = Result<U, E>>,
{
    type Out = Result<U, E>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Result<U, E> {
        match self.prev.call(ctx, world, input) {
            Ok(val) => self.step.call(ctx, world, val),
            Err(e) => Err(e),
        }
    }
}

/// Chain node for `.catch()` on `Result<T, E>` — handles error, transitions to `Option<T>`.
#[doc(hidden)]
pub struct CtxCatchNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, E, Prev, S> CtxChainCall<C, In> for CtxCatchNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
    S: CtxStepCall<C, E, Out = ()>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<T> {
        match self.prev.call(ctx, world, input) {
            Ok(val) => Some(val),
            Err(e) => {
                self.step.call(ctx, world, e);
                None
            }
        }
    }
}

/// Chain node for `.map_err()` on `Result<T, E>`.
#[doc(hidden)]
pub struct CtxMapErrNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, E, E2, Prev, S> CtxChainCall<C, In> for CtxMapErrNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
    S: CtxStepCall<C, E, Out = E2>,
{
    type Out = Result<T, E2>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Result<T, E2> {
        match self.prev.call(ctx, world, input) {
            Ok(val) => Ok(val),
            Err(e) => Err(self.step.call(ctx, world, e)),
        }
    }
}

/// Chain node for `.inspect_err()` on `Result<T, E>`.
#[doc(hidden)]
pub struct CtxInspectErrNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, E, Prev, S> CtxChainCall<C, In> for CtxInspectErrNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
    S: CtxRefStepCall<C, E, Out = ()>,
{
    type Out = Result<T, E>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Result<T, E> {
        let result = self.prev.call(ctx, world, input);
        if let Err(ref e) = result {
            self.step.call(ctx, world, e);
        }
        result
    }
}

/// Chain node for `.inspect()` on `Result<T, E>` — side effect on Ok value.
#[doc(hidden)]
pub struct CtxInspectResultNode<Prev, S> {
    pub(crate) prev: Prev,
    pub(crate) step: S,
}

impl<C, In, T, E, Prev, S> CtxChainCall<C, In> for CtxInspectResultNode<Prev, S>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
    S: CtxRefStepCall<C, T, Out = ()>,
{
    type Out = Result<T, E>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Result<T, E> {
        let result = self.prev.call(ctx, world, input);
        if let Ok(ref val) = result {
            self.step.call(ctx, world, val);
        }
        result
    }
}

/// Chain node for discarding `Option<()>` to `()`.
#[doc(hidden)]
pub struct CtxDiscardOptionNode<Prev> {
    pub(crate) prev: Prev,
}

impl<C, In, Prev> CtxChainCall<C, In> for CtxDiscardOptionNode<Prev>
where
    Prev: CtxChainCall<C, In, Out = Option<()>>,
{
    type Out = ();
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) {
        let _ = self.prev.call(ctx, world, input);
    }
}

// =============================================================================
// CtxPipelineBuilder — entry point
// =============================================================================

/// Entry point for building a context-aware pipeline.
///
/// Like [`PipelineBuilder`](crate::PipelineBuilder) but every step
/// receives `&mut C` as the first argument.
///
/// # Examples
///
/// ```ignore
/// let pipeline = CtxPipelineBuilder::<ReconnectCtx, ()>::new()
///     .then(check_retries, &reg)
///     .then(attempt_connect, &reg)
///     .build();
/// ```
#[must_use = "pipeline builder does nothing until .then() is called"]
pub struct CtxPipelineBuilder<C, In>(PhantomData<fn(&mut C, In)>);

impl<C, In> CtxPipelineBuilder<C, In> {
    /// Create a new context-aware pipeline entry point.
    pub fn new() -> Self {
        Self(PhantomData)
    }

    /// Add the first step. Params resolved from the registry.
    pub fn then<Out, Params, S: IntoCtxStep<C, In, Out, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Out, CtxThenNode<CtxIdentityNode, S::Step>> {
        CtxPipelineChain {
            chain: CtxThenNode {
                prev: CtxIdentityNode,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }
}

impl<C, In> Default for CtxPipelineBuilder<C, In> {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// CtxPipelineChain — typestate builder
// =============================================================================

/// Builder that composes context-aware pipeline steps via named chain nodes.
///
/// `C` is the context type. `In` is the pipeline's input type (fixed).
/// `Out` is the current output. `Chain` is the concrete chain type.
#[must_use = "pipeline chain does nothing until .build() is called"]
pub struct CtxPipelineChain<C, In, Out, Chain> {
    chain: Chain,
    _marker: PhantomData<fn(&mut C, In) -> Out>,
}

// =============================================================================
// Core — any Out
// =============================================================================

impl<C, In, Out, Chain: CtxChainCall<C, In, Out = Out>> CtxPipelineChain<C, In, Out, Chain> {
    /// Add a step. Params resolved from the registry.
    pub fn then<NewOut, Params, S: IntoCtxStep<C, Out, NewOut, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, NewOut, CtxThenNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxThenNode {
                prev: self.chain,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Run the pipeline directly.
    pub fn run(&mut self, ctx: &mut C, world: &mut World, input: In) -> Out {
        self.chain.call(ctx, world, input)
    }

    /// Conditionally wrap the output in `Option`. `Some(val)` if
    /// the predicate returns true, `None` otherwise.
    pub fn guard<Params, S: IntoCtxRefStep<C, Out, bool, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Option<Out>, CtxGuardNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxGuardNode {
                prev: self.chain,
                step: f.into_ctx_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Observe the current value without consuming or changing it.
    pub fn tap<Params, S: IntoCtxRefStep<C, Out, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Out, CtxTapNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxTapNode {
                prev: self.chain,
                step: f.into_ctx_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// Option helpers — CtxPipelineChain<C, In, Option<T>, Chain>
// =============================================================================

impl<C, In, T, Chain: CtxChainCall<C, In, Out = Option<T>>>
    CtxPipelineChain<C, In, Option<T>, Chain>
{
    /// Transform the inner value. Step not called on None.
    pub fn map<U, Params, S: IntoCtxStep<C, T, U, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Option<U>, CtxMapOptionNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxMapOptionNode {
                prev: self.chain,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Short-circuits on None. std: `Option::and_then`
    pub fn and_then<U, Params, S: IntoCtxStep<C, T, Option<U>, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Option<U>, CtxAndThenNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxAndThenNode {
                prev: self.chain,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Keep value if predicate holds. std: `Option::filter`
    pub fn filter<Params, S: IntoCtxRefStep<C, T, bool, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Option<T>, CtxFilterNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxFilterNode {
                prev: self.chain,
                step: f.into_ctx_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Side effect on Some value. std: `Option::inspect`
    pub fn inspect<Params, S: IntoCtxRefStep<C, T, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Option<T>, CtxInspectOptionNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxInspectOptionNode {
                prev: self.chain,
                step: f.into_ctx_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Side effect on None. Complement to [`inspect`](Self::inspect).
    pub fn on_none<Params, S: IntoCtxProducer<C, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Option<T>, CtxOnNoneNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxOnNoneNode {
                prev: self.chain,
                producer: f.into_ctx_producer(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Exit Option — None becomes `f()`.
    pub fn unwrap_or_else<Params, S: IntoCtxProducer<C, T, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, T, CtxUnwrapOrElseOptionNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxUnwrapOrElseOptionNode {
                prev: self.chain,
                producer: f.into_ctx_producer(registry),
            },
            _marker: PhantomData,
        }
    }

    /// None becomes Err(err). std: `Option::ok_or`
    pub fn ok_or<E: Clone>(
        self,
        err: E,
    ) -> CtxPipelineChain<C, In, Result<T, E>, CtxOkOrNode<Chain, E>> {
        CtxPipelineChain {
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
    ) -> CtxPipelineChain<C, In, T, CtxUnwrapOrOptionNode<Chain, T>>
    where
        T: Clone,
    {
        CtxPipelineChain {
            chain: CtxUnwrapOrOptionNode {
                prev: self.chain,
                default,
            },
            _marker: PhantomData,
        }
    }
}

/// Chain node for `.ok_or()` on `Option<T>`.
#[doc(hidden)]
pub struct CtxOkOrNode<Prev, E> {
    pub(crate) prev: Prev,
    pub(crate) err: E,
}

impl<C, In, T, E: Clone, Prev> CtxChainCall<C, In> for CtxOkOrNode<Prev, E>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
{
    type Out = Result<T, E>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Result<T, E> {
        match self.prev.call(ctx, world, input) {
            Some(val) => Ok(val),
            None => Err(self.err.clone()),
        }
    }
}

/// Chain node for `.unwrap_or()` on `Option<T>`.
#[doc(hidden)]
pub struct CtxUnwrapOrOptionNode<Prev, T> {
    pub(crate) prev: Prev,
    pub(crate) default: T,
}

impl<C, In, T: Clone, Prev> CtxChainCall<C, In> for CtxUnwrapOrOptionNode<Prev, T>
where
    Prev: CtxChainCall<C, In, Out = Option<T>>,
{
    type Out = T;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> T {
        match self.prev.call(ctx, world, input) {
            Some(val) => val,
            None => self.default.clone(),
        }
    }
}

// =============================================================================
// Result helpers — CtxPipelineChain<C, In, Result<T, E>, Chain>
// =============================================================================

impl<C, In, T, E, Chain: CtxChainCall<C, In, Out = Result<T, E>>>
    CtxPipelineChain<C, In, Result<T, E>, Chain>
{
    /// Transform the Ok value. Step not called on Err.
    pub fn map<U, Params, S: IntoCtxStep<C, T, U, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Result<U, E>, CtxMapResultNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxMapResultNode {
                prev: self.chain,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Short-circuits on Err. std: `Result::and_then`
    pub fn and_then<U, Params, S: IntoCtxStep<C, T, Result<U, E>, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Result<U, E>, CtxAndThenResultNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxAndThenResultNode {
                prev: self.chain,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Handle error and transition to Option.
    pub fn catch<Params, S: IntoCtxStep<C, E, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Option<T>, CtxCatchNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxCatchNode {
                prev: self.chain,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Transform the error. std: `Result::map_err`
    pub fn map_err<E2, Params, S: IntoCtxStep<C, E, E2, Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Result<T, E2>, CtxMapErrNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxMapErrNode {
                prev: self.chain,
                step: f.into_ctx_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Side effect on Ok value. std: `Result::inspect` (nightly)
    pub fn inspect<Params, S: IntoCtxRefStep<C, T, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Result<T, E>, CtxInspectResultNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxInspectResultNode {
                prev: self.chain,
                step: f.into_ctx_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Side effect on Err value. std: `Result::inspect_err` (nightly)
    pub fn inspect_err<Params, S: IntoCtxRefStep<C, E, (), Params>>(
        self,
        f: S,
        registry: &Registry,
    ) -> CtxPipelineChain<C, In, Result<T, E>, CtxInspectErrNode<Chain, S::Step>> {
        CtxPipelineChain {
            chain: CtxInspectErrNode {
                prev: self.chain,
                step: f.into_ctx_ref_step(registry),
            },
            _marker: PhantomData,
        }
    }

    /// Convert Result to Option, discarding the error.
    pub fn ok(self) -> CtxPipelineChain<C, In, Option<T>, CtxOkNode<Chain>> {
        CtxPipelineChain {
            chain: CtxOkNode { prev: self.chain },
            _marker: PhantomData,
        }
    }

    /// Exit Result — Err becomes the default value.
    pub fn unwrap_or(
        self,
        default: T,
    ) -> CtxPipelineChain<C, In, T, CtxUnwrapOrResultNode<Chain, T>>
    where
        T: Clone,
    {
        CtxPipelineChain {
            chain: CtxUnwrapOrResultNode {
                prev: self.chain,
                default,
            },
            _marker: PhantomData,
        }
    }
}

/// Chain node for `.ok()` on `Result<T, E>` — discards error.
#[doc(hidden)]
pub struct CtxOkNode<Prev> {
    pub(crate) prev: Prev,
}

impl<C, In, T, E, Prev> CtxChainCall<C, In> for CtxOkNode<Prev>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
{
    type Out = Option<T>;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> Option<T> {
        self.prev.call(ctx, world, input).ok()
    }
}

/// Chain node for `.unwrap_or()` on `Result<T, E>`.
#[doc(hidden)]
pub struct CtxUnwrapOrResultNode<Prev, T> {
    pub(crate) prev: Prev,
    pub(crate) default: T,
}

impl<C, In, T: Clone, E, Prev> CtxChainCall<C, In> for CtxUnwrapOrResultNode<Prev, T>
where
    Prev: CtxChainCall<C, In, Out = Result<T, E>>,
{
    type Out = T;
    #[inline(always)]
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) -> T {
        match self.prev.call(ctx, world, input) {
            Ok(val) => val,
            Err(_) => self.default.clone(),
        }
    }
}

// =============================================================================
// build — when Out is () or Option<()>
// =============================================================================

impl<C, In, Chain: CtxChainCall<C, In, Out = ()>> CtxPipelineChain<C, In, (), Chain> {
    /// Finalize the pipeline into a [`CtxPipeline`].
    #[must_use = "building a pipeline without storing it does nothing"]
    pub fn build(self) -> CtxPipeline<C, In, Chain> {
        CtxPipeline {
            chain: self.chain,
            _marker: PhantomData,
        }
    }
}

impl<C, In, Chain: CtxChainCall<C, In, Out = Option<()>>>
    CtxPipelineChain<C, In, Option<()>, Chain>
{
    /// Finalize the pipeline, discarding `Option<()>`.
    #[must_use = "building a pipeline without storing it does nothing"]
    pub fn build(self) -> CtxPipeline<C, In, CtxDiscardOptionNode<Chain>> {
        CtxPipeline {
            chain: CtxDiscardOptionNode { prev: self.chain },
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// CtxPipeline — built context-aware pipeline
// =============================================================================

/// Built context-aware pipeline.
///
/// Created by [`CtxPipelineChain::build`]. Implements [`CtxStepCall`]
/// for use inside [`Callback`](crate::Callback) dispatch.
pub struct CtxPipeline<C, In, Chain> {
    chain: Chain,
    _marker: PhantomData<fn(&mut C, In)>,
}

impl<C, In, Chain: CtxChainCall<C, In, Out = ()>> CtxStepCall<C, In> for CtxPipeline<C, In, Chain> {
    type Out = ();
    fn call(&mut self, ctx: &mut C, world: &mut World, input: In) {
        self.chain.call(ctx, world, input);
    }
}

impl<C, In, Chain: CtxChainCall<C, In, Out = ()>> CtxPipeline<C, In, Chain> {
    /// Run the pipeline with context, world, and input.
    pub fn run(&mut self, ctx: &mut C, world: &mut World, input: In) {
        self.chain.call(ctx, world, input);
    }
}

// =============================================================================
// resolve_ctx_step — free function for select! macro dispatch arms
// =============================================================================

/// Pre-resolve a context-aware step function against a [`Registry`].
///
/// Returns a closure `FnMut(&mut C, &mut World, In) -> Out` that can be
/// called directly without per-call registry lookup. Used by the
/// [`select!`](crate::select) macro to build monomorphized dispatch arms.
///
/// # Example
///
/// ```ignore
/// let mut arm = resolve_ctx_step::<SessionCtx, _, _, _, _>(on_new_order, &reg);
/// // Later, in a match arm:
/// arm(&mut ctx, &mut world, order);
/// ```
pub fn resolve_ctx_step<C, In, Out, Params, S>(
    f: S,
    registry: &Registry,
) -> impl FnMut(&mut C, &mut World, In) -> Out + use<C, In, Out, Params, S>
where
    C: 'static,
    In: 'static,
    Out: 'static,
    S: IntoCtxStep<C, In, Out, Params>,
{
    let mut resolved = f.into_ctx_step(registry);
    move |ctx: &mut C, world: &mut World, input: In| resolved.call(ctx, world, input)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Res, ResMut, WorldBuilder};

    // -- Helper types ---------------------------------------------------------

    struct ReconnectCtx {
        retries: u32,
        last_result: Option<bool>,
    }

    // -- Core dispatch --------------------------------------------------------

    #[test]
    fn ctx_pipeline_three_steps_with_context_mutation() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        let mut world = wb.build();
        let reg = world.registry();

        // Step 1: check retries (closure, arity 0)
        // Step 2: multiply by resource (named fn, arity 1)
        // Step 3: record result in context (closure, arity 0)

        fn multiply(ctx: &mut ReconnectCtx, factor: Res<u64>, input: u32) -> u64 {
            ctx.retries += 1;
            *factor * input as u64
        }

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |ctx: &mut ReconnectCtx, x: u32| {
                    ctx.retries += 1;
                    x
                },
                reg,
            )
            .then(multiply, reg)
            .then(
                |ctx: &mut ReconnectCtx, val: u64| {
                    ctx.last_result = Some(val > 0);
                },
                reg,
            )
            .build();

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        pipeline.run(&mut ctx, &mut world, 5);

        // Closure incremented once, named fn incremented once
        assert_eq!(ctx.retries, 2);
        // 10 * 5 = 50, which is > 0
        assert_eq!(ctx.last_result, Some(true));
    }

    #[test]
    fn ctx_pipeline_guard_and_map() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(|_ctx: &mut ReconnectCtx, x: u32| x, reg)
            .guard(|_ctx: &mut ReconnectCtx, x: &u32| *x > 10, reg)
            .map(
                |ctx: &mut ReconnectCtx, x: u32| {
                    ctx.retries += 1;
                    x * 2
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        // x = 5, guard fails, map not called
        let result = pipeline.run(&mut ctx, &mut world, 5);
        assert_eq!(result, None);
        assert_eq!(ctx.retries, 0);

        // x = 20, guard passes, map called
        let result = pipeline.run(&mut ctx, &mut world, 20);
        assert_eq!(result, Some(40));
        assert_eq!(ctx.retries, 1);
    }

    #[test]
    fn ctx_pipeline_and_then() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(|_ctx: &mut ReconnectCtx, x: u32| Some(x), reg)
            .and_then(
                |ctx: &mut ReconnectCtx, x: u32| {
                    ctx.retries += 1;
                    if x > 5 { Some(x * 2) } else { None }
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 3), None);
        assert_eq!(ctx.retries, 1);

        assert_eq!(pipeline.run(&mut ctx, &mut world, 10), Some(20));
        assert_eq!(ctx.retries, 2);
    }

    #[test]
    fn ctx_pipeline_catch() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| -> Result<u32, String> {
                    if x > 0 {
                        Ok(x)
                    } else {
                        Err("zero".to_string())
                    }
                },
                reg,
            )
            .catch(
                |ctx: &mut ReconnectCtx, _err: String| {
                    ctx.retries += 1;
                },
                reg,
            )
            .map(
                |ctx: &mut ReconnectCtx, val: u32| {
                    ctx.last_result = Some(true);
                    val
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        // Error path
        let result = pipeline.run(&mut ctx, &mut world, 0);
        assert_eq!(result, None);
        assert_eq!(ctx.retries, 1);
        assert_eq!(ctx.last_result, None);

        // Ok path
        let result = pipeline.run(&mut ctx, &mut world, 42);
        assert_eq!(result, Some(42));
        assert_eq!(ctx.retries, 1);
        assert_eq!(ctx.last_result, Some(true));
    }

    #[test]
    fn ctx_pipeline_with_res_mut() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(0);
        let mut world = wb.build();
        let reg = world.registry();

        fn accumulate(ctx: &mut ReconnectCtx, mut total: ResMut<u64>, val: u32) {
            *total += val as u64;
            ctx.retries += 1;
        }

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(accumulate, reg)
            .build();

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        pipeline.run(&mut ctx, &mut world, 10);
        pipeline.run(&mut ctx, &mut world, 5);

        assert_eq!(*world.resource::<u64>(), 15);
        assert_eq!(ctx.retries, 2);
    }

    #[test]
    fn ctx_pipeline_build_with_option_unit() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        // Pipeline that ends with Option<()> — should still build
        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| -> Option<u32> {
                    if x > 0 { Some(x) } else { None }
                },
                reg,
            )
            .map(|_ctx: &mut ReconnectCtx, _x: u32| {}, reg)
            .build();

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        // Should not panic
        pipeline.run(&mut ctx, &mut world, 5);
        pipeline.run(&mut ctx, &mut world, 0);
    }

    #[test]
    fn ctx_pipeline_tap() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(|_ctx: &mut ReconnectCtx, x: u32| x * 2, reg)
            .tap(
                |ctx: &mut ReconnectCtx, val: &u32| {
                    ctx.retries = *val;
                },
                reg,
            )
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| {
                    // Value should pass through tap unchanged
                    assert_eq!(x, 10);
                },
                reg,
            )
            .build();

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        pipeline.run(&mut ctx, &mut world, 5);
        assert_eq!(ctx.retries, 10);
    }

    #[test]
    fn ctx_pipeline_result_map_and_map_err() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| -> Result<u32, u32> {
                    if x > 0 { Ok(x) } else { Err(x) }
                },
                reg,
            )
            .map(|_ctx: &mut ReconnectCtx, x: u32| x * 10, reg)
            .map_err(
                |ctx: &mut ReconnectCtx, e: u32| {
                    ctx.retries += 1;
                    format!("error: {e}")
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 5), Ok(50));
        assert_eq!(
            pipeline.run(&mut ctx, &mut world, 0),
            Err("error: 0".to_string())
        );
        assert_eq!(ctx.retries, 1);
    }

    #[test]
    fn ctx_pipeline_inspect_err() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| -> Result<u32, String> {
                    if x > 0 { Ok(x) } else { Err("zero".into()) }
                },
                reg,
            )
            .inspect_err(
                |ctx: &mut ReconnectCtx, _e: &String| {
                    ctx.retries += 1;
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        let _ = pipeline.run(&mut ctx, &mut world, 0);
        assert_eq!(ctx.retries, 1);

        // Ok path — inspect_err not called
        let _ = pipeline.run(&mut ctx, &mut world, 5);
        assert_eq!(ctx.retries, 1);
    }

    #[test]
    fn ctx_pipeline_filter() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(|_ctx: &mut ReconnectCtx, x: u32| Some(x), reg)
            .filter(|_ctx: &mut ReconnectCtx, x: &u32| *x > 10, reg);

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 5), None);
        assert_eq!(pipeline.run(&mut ctx, &mut world, 20), Some(20));
    }

    #[test]
    fn ctx_pipeline_ok_or() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| {
                    if x > 0 { Some(x) } else { None }
                },
                reg,
            )
            .ok_or("was zero");

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 5), Ok(5));
        assert_eq!(pipeline.run(&mut ctx, &mut world, 0), Err("was zero"));
    }

    #[test]
    fn ctx_pipeline_unwrap_or_option() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| {
                    if x > 0 { Some(x) } else { None }
                },
                reg,
            )
            .unwrap_or(99);

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 5), 5);
        assert_eq!(pipeline.run(&mut ctx, &mut world, 0), 99);
    }

    #[test]
    fn ctx_pipeline_unwrap_or_else_option() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| {
                    if x > 0 { Some(x) } else { None }
                },
                reg,
            )
            .unwrap_or_else(
                |ctx: &mut ReconnectCtx| {
                    ctx.retries += 1;
                    42
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 5), 5);
        assert_eq!(ctx.retries, 0);
        assert_eq!(pipeline.run(&mut ctx, &mut world, 0), 42);
        assert_eq!(ctx.retries, 1);
    }

    #[test]
    fn ctx_pipeline_inspect_option() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| {
                    if x > 0 { Some(x) } else { None }
                },
                reg,
            )
            .inspect(
                |ctx: &mut ReconnectCtx, val: &u32| {
                    ctx.retries = *val;
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        // Some path — inspect fires
        let _ = pipeline.run(&mut ctx, &mut world, 7);
        assert_eq!(ctx.retries, 7);

        // None path — inspect skipped
        let _ = pipeline.run(&mut ctx, &mut world, 0);
        assert_eq!(ctx.retries, 7);
    }

    #[test]
    fn ctx_pipeline_on_none() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| {
                    if x > 0 { Some(x) } else { None }
                },
                reg,
            )
            .on_none(
                |ctx: &mut ReconnectCtx| {
                    ctx.retries += 1;
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        // Some path — on_none not called
        let result = pipeline.run(&mut ctx, &mut world, 5);
        assert_eq!(result, Some(5));
        assert_eq!(ctx.retries, 0);

        // None path — on_none called
        let result = pipeline.run(&mut ctx, &mut world, 0);
        assert_eq!(result, None);
        assert_eq!(ctx.retries, 1);
    }

    #[test]
    fn ctx_pipeline_ok_result() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| -> Result<u32, String> {
                    if x > 0 { Ok(x) } else { Err("zero".into()) }
                },
                reg,
            )
            .ok();

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 5), Some(5));
        assert_eq!(pipeline.run(&mut ctx, &mut world, 0), None);
    }

    #[test]
    fn ctx_pipeline_unwrap_or_result() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| -> Result<u32, String> {
                    if x > 0 { Ok(x) } else { Err("zero".into()) }
                },
                reg,
            )
            .unwrap_or(99);

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 5), 5);
        assert_eq!(pipeline.run(&mut ctx, &mut world, 0), 99);
    }

    #[test]
    fn ctx_pipeline_inspect_result() {
        let mut world = WorldBuilder::new().build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| -> Result<u32, String> {
                    if x > 0 { Ok(x) } else { Err("zero".into()) }
                },
                reg,
            )
            .inspect(
                |ctx: &mut ReconnectCtx, val: &u32| {
                    ctx.retries = *val;
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        // Ok path — inspect fires
        let _ = pipeline.run(&mut ctx, &mut world, 7);
        assert_eq!(ctx.retries, 7);

        // Err path — inspect skipped
        let _ = pipeline.run(&mut ctx, &mut world, 0);
        assert_eq!(ctx.retries, 7);
    }

    // -- Opaque escape hatch --------------------------------------------------

    #[test]
    fn ctx_pipeline_opaque_step() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(100);
        let mut world = wb.build();
        let reg = world.registry();

        // Opaque step: FnMut(&mut C, &mut World, In) -> Out
        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |ctx: &mut ReconnectCtx, w: &mut World, x: u32| {
                    ctx.retries += 1;
                    let scale = *w.resource::<u64>();
                    u64::from(x) * scale
                },
                reg,
            )
            .then(
                |ctx: &mut ReconnectCtx, val: u64| {
                    ctx.last_result = Some(val > 0);
                },
                reg,
            )
            .build();

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        pipeline.run(&mut ctx, &mut world, 5);
        assert_eq!(ctx.retries, 1);
        assert_eq!(ctx.last_result, Some(true));
    }

    #[test]
    fn ctx_pipeline_opaque_guard() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(10);
        let mut world = wb.build();
        let reg = world.registry();

        // Opaque ref step used as guard
        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(|_ctx: &mut ReconnectCtx, x: u32| x, reg)
            .guard(
                |_ctx: &mut ReconnectCtx, w: &mut World, x: &u32| {
                    let threshold = *w.resource::<u64>();
                    u64::from(*x) > threshold
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 5), None);
        assert_eq!(pipeline.run(&mut ctx, &mut world, 20), Some(20));
    }

    #[test]
    fn ctx_pipeline_opaque_producer() {
        let mut wb = WorldBuilder::new();
        wb.register::<u64>(42);
        let mut world = wb.build();
        let reg = world.registry();

        // Opaque producer: FnMut(&mut C, &mut World) -> Out
        let mut pipeline = CtxPipelineBuilder::<ReconnectCtx, u32>::new()
            .then(
                |_ctx: &mut ReconnectCtx, x: u32| {
                    if x > 0 { Some(x) } else { None }
                },
                reg,
            )
            .unwrap_or_else(
                |ctx: &mut ReconnectCtx, w: &mut World| {
                    ctx.retries += 1;
                    *w.resource::<u64>() as u32
                },
                reg,
            );

        let mut ctx = ReconnectCtx {
            retries: 0,
            last_result: None,
        };

        assert_eq!(pipeline.run(&mut ctx, &mut world, 5), 5);
        assert_eq!(ctx.retries, 0);
        assert_eq!(pipeline.run(&mut ctx, &mut world, 0), 42);
        assert_eq!(ctx.retries, 1);
    }
}
