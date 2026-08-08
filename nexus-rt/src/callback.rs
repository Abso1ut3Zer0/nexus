//! Context-owning handler dispatch.
//!
//! [`Callback`] is the unified dispatch type in nexus-rt. Context-free
//! handlers use `Callback<(), CtxFree<F>, P>` (via [`IntoHandler`](crate::IntoHandler));
//! context-owning handlers use `Callback<C, F, P>` (via [`IntoCallback`]).
//!
//! The function convention for context-owning callbacks is
//! `fn handler(ctx: &mut C, params: Res<T>..., event: E)` — context first,
//! [`Param`]-resolved resources in the middle, event last.
//!
//! Same HRTB double-bound pattern, same macro generation, same ~2-cycle
//! dispatch. Named functions only (same closure limitation as
//! [`IntoHandler`](crate::IntoHandler)).
//!
//! # When to use Callback
//!
//! Use [`Callback`] over [`IntoHandler`](crate::IntoHandler) when each
//! handler instance needs its own private state that isn't shared via
//! [`World`](crate::World):
//!
//! - **Per-timer context** — each timer carries its own order ID, retry
//!   count, or deadline metadata.
//! - **Per-connection state** — each socket handler carries its own codec
//!   state, read buffer, or session context.
//! - **Protocol state machines** — each handler instance tracks its own
//!   position in a protocol handshake or reconnection sequence.
//!
//! The `ctx` field is `pub`, so drivers can read or mutate it between
//! dispatches (e.g. to update a deadline or check a counter).
//!
//! # Returning callbacks from functions (Rust 2024)
//!
//! When a factory function takes `&Registry` and returns `impl Handler<E>`,
//! Rust 2024 captures the registry borrow. Use `+ use<...>` to exclude it:
//!
//! ```ignore
//! fn build_callback(
//!     ctx: MyCtx,
//!     reg: &Registry,
//! ) -> impl Handler<DataEvent> + use<> {
//!     on_data.into_callback(ctx, reg)
//! }
//! ```
//!
//! See the [crate-level docs](crate#returning-impl-handler-from-functions-rust-2024)
//! for the full explanation.

// Handler arity is architecturally required by the Param trait — handlers
// take N typed parameters and the macro-generated dispatch impls expand
// per-arity into call_inner functions with N + Input arguments. Module-level
// allow rather than one inline attribute per arity expansion.
#![allow(clippy::too_many_arguments)]

use crate::Handler;
use crate::handler::Param;
use crate::world::{Registry, World};

// =============================================================================
// Callback<C, F, Params>
// =============================================================================

/// Unified dispatch type. Stores per-callback context alongside
/// pre-resolved resource access.
///
/// - Context-free handlers: `Callback<(), CtxFree<F>, P>` — created via
///   [`IntoHandler::into_handler`](crate::IntoHandler::into_handler).
/// - Context-owning handlers: `Callback<C, F, P>` — created via
///   [`IntoCallback::into_callback`].
///
/// Both implement [`Handler<E>`].
///
/// # Examples
///
/// ```
/// use nexus_rt::{WorldBuilder, ResMut, IntoCallback, Handler, Resource};
///
/// #[derive(Resource)]
/// struct Counter(u64);
///
/// struct Ctx { count: u64 }
///
/// fn handler(ctx: &mut Ctx, mut val: ResMut<Counter>, event: u32) {
///     val.0 += event as u64;
///     ctx.count += 1;
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register(Counter(0));
/// let mut world = builder.build();
///
/// let mut cb = handler.into_callback(Ctx { count: 0 }, world.registry());
/// cb.run(&mut world, 10u32);
///
/// assert_eq!(cb.ctx.count, 1);
/// assert_eq!(world.resource::<Counter>().0, 10);
/// ```
pub struct Callback<C, F, Params: Param> {
    /// Per-callback owned state. Accessible outside dispatch.
    pub ctx: C,
    pub(crate) f: F,
    pub(crate) state: Params::State,
    pub(crate) name: &'static str,
}

// =============================================================================
// IntoCallback
// =============================================================================

/// Converts a named function into a [`Callback`].
///
/// Identical to [`IntoHandler`](crate::IntoHandler) but injects `&mut C` as
/// the first parameter. [`ResourceId`](crate::ResourceId)s resolved via
/// `registry.id::<T>()` at call time — panics if any resource is not
/// registered.
///
/// Use `IntoCallback` when each handler instance needs its own private
/// state. For stateless handlers (or state shared via [`World`](crate::World)),
/// prefer [`IntoHandler`](crate::IntoHandler).
///
/// # Named functions only
///
/// Closures do not work with `IntoCallback` due to Rust's HRTB inference
/// limitations with GATs. Use named `fn` items instead.
///
/// # Examples
///
/// ```
/// use nexus_rt::{WorldBuilder, ResMut, IntoCallback, Handler, Resource, no_event};
///
/// #[derive(Resource)]
/// struct Counter(u64);
///
/// struct TimerCtx { order_id: u64, fires: u64 }
///
/// fn on_timeout(ctx: &mut TimerCtx, mut counter: ResMut<Counter>) {
///     ctx.fires += 1;
///     counter.0 += ctx.order_id;
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register(Counter(0));
/// let mut world = builder.build();
///
/// let mut cb = no_event(on_timeout).into_callback(
///     TimerCtx { order_id: 42, fires: 0 },
///     world.registry(),
/// );
/// cb.run(&mut world, ());
///
/// assert_eq!(cb.ctx.fires, 1);
/// assert_eq!(world.resource::<Counter>().0, 42);
/// ```
///
/// # Panics
///
/// Panics if any [`Param`] resource is not registered in the
/// [`Registry`](crate::Registry).
#[diagnostic::on_unimplemented(
    message = "this function cannot be converted into a callback",
    note = "callback signature: `fn(&mut Context, Res<A>, ..., Event)` — context first, then resources, event last",
    note = "for Handler<()> with params, wrap with `no_event(fn_name)` to omit the event parameter",
    note = "closures with resource parameters are not supported — use a named `fn` when using Param resources"
)]
pub trait IntoCallback<C, E, Params> {
    /// The concrete Callback type produced.
    type Callback: Handler<E>;

    /// Convert this function + context into a Callback.
    #[must_use = "the callback must be stored or dispatched — discarding it does nothing"]
    fn into_callback(self, ctx: C, registry: &Registry) -> Self::Callback;
}

// =============================================================================
// Arity 0: fn(ctx: &mut C, E) — context + event only, no Param
// =============================================================================

impl<C: Send + 'static, E, F: FnMut(&mut C, E) + Send + 'static> IntoCallback<C, E, ()> for F {
    type Callback = Callback<C, F, ()>;

    fn into_callback(self, ctx: C, registry: &Registry) -> Self::Callback {
        Callback {
            ctx,
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

impl<C: Send + 'static, E, F: FnMut(&mut C, E) + Send + 'static> Handler<E> for Callback<C, F, ()> {
    fn run(&mut self, _world: &mut World, event: E) {
        (self.f)(&mut self.ctx, event);
    }

    fn name(&self) -> &'static str {
        self.name
    }
}

// =============================================================================
// Macro-generated impls (arities 1-8)
// =============================================================================

macro_rules! impl_into_callback {
    ($($P:ident),+) => {
        impl<C: Send + 'static, E, F: Send + 'static, $($P: Param + 'static),+>
            IntoCallback<C, E, ($($P,)+)> for F
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+ E) +
                FnMut(&mut C, $($P::Item<'a>,)+ E),
        {
            type Callback = Callback<C, F, ($($P,)+)>;

            fn into_callback(self, ctx: C, registry: &Registry) -> Self::Callback {
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
                Callback { ctx, f: self, state, name: std::any::type_name::<F>() }
            }
        }

        impl<C: Send + 'static, E, F: Send + 'static, $($P: Param + 'static),+>
            Handler<E> for Callback<C, F, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+ E) +
                FnMut(&mut C, $($P::Item<'a>,)+ E),
        {
            #[allow(non_snake_case)]
            fn run(&mut self, world: &mut World, event: E) {
                fn call_inner<Ctx, $($P,)+ Ev>(
                    mut f: impl FnMut(&mut Ctx, $($P,)+ Ev),
                    ctx: &mut Ctx,
                    $($P: $P,)+
                    event: Ev,
                ) {
                    f(ctx, $($P,)+ event);
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by init() on the same registry
                // that built this world. Single-threaded sequential dispatch
                // ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, &mut self.ctx, $($P,)+ event);
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }
    };
}

all_tuples!(impl_into_callback);

// =============================================================================
// No-event callback impls — Handler<()> without trailing `_: ()` parameter
// =============================================================================

use crate::handler::NoEvent;

// Arity 0: fn(&mut C) → Handler<()>
impl<C: Send + 'static, F: FnMut(&mut C) + Send + 'static> IntoCallback<C, (), NoEvent<F>> for F {
    type Callback = Callback<C, NoEvent<F>, ()>;

    fn into_callback(self, ctx: C, registry: &Registry) -> Self::Callback {
        Callback {
            ctx,
            f: NoEvent(self),
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
        }
    }
}

impl<C: Send + 'static, F: FnMut(&mut C) + Send + 'static> Handler<()>
    for Callback<C, NoEvent<F>, ()>
{
    fn run(&mut self, _world: &mut World, _event: ()) {
        (self.f.0)(&mut self.ctx);
    }

    fn name(&self) -> &'static str {
        self.name
    }
}

macro_rules! impl_into_callback_no_event {
    ($($P:ident),+) => {
        impl<C: Send + 'static, F: Send + 'static, $($P: Param + 'static),+>
            IntoCallback<C, (), ($($P,)+)> for NoEvent<F>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+) +
                FnMut(&mut C, $($P::Item<'a>,)+),
        {
            type Callback = Callback<C, NoEvent<F>, ($($P,)+)>;

            fn into_callback(self, ctx: C, registry: &Registry) -> Self::Callback {
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
                Callback { ctx, f: self, state, name: std::any::type_name::<F>() }
            }
        }

        impl<C: Send + 'static, F: Send + 'static, $($P: Param + 'static),+>
            Handler<()> for Callback<C, NoEvent<F>, ($($P,)+)>
        where
            for<'a> &'a mut F:
                FnMut(&mut C, $($P,)+) +
                FnMut(&mut C, $($P::Item<'a>,)+),
        {
            #[allow(non_snake_case)]
            fn run(&mut self, world: &mut World, _event: ()) {
                fn call_inner<Ctx, $($P),+>(
                    mut f: impl FnMut(&mut Ctx, $($P),+),
                    ctx: &mut Ctx,
                    $($P: $P,)+
                ) {
                    f(ctx, $($P),+);
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by init() on the same registry
                // that built this world. Single-threaded sequential dispatch
                // ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f.0, &mut self.ctx, $($P,)+);
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }
    };
}

all_tuples!(impl_into_callback_no_event);

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Local, Res, ResMut, WorldBuilder, no_event};

    // -- Helper types ---------------------------------------------------------

    struct TimerCtx {
        order_id: u64,
        call_count: u64,
    }

    struct OrderCache {
        expired: Vec<u64>,
    }
    impl crate::world::Resource for OrderCache {}

    // -- Core dispatch --------------------------------------------------------

    fn ctx_only_handler(ctx: &mut TimerCtx, _event: u32) {
        ctx.call_count += 1;
    }

    #[test]
    fn ctx_only_no_params() {
        let mut world = WorldBuilder::new().build();
        let mut cb = ctx_only_handler.into_callback(
            TimerCtx {
                order_id: 1,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.run(&mut world, 42u32);
        assert_eq!(cb.ctx.call_count, 1);
    }

    fn ctx_one_res_handler(ctx: &mut TimerCtx, cache: Res<OrderCache>, _event: u32) {
        ctx.call_count += cache.expired.len() as u64;
    }

    #[test]
    fn ctx_one_res() {
        let mut builder = WorldBuilder::new();
        builder.register::<OrderCache>(OrderCache {
            expired: vec![1, 2, 3],
        });
        let mut world = builder.build();

        let mut cb = ctx_one_res_handler.into_callback(
            TimerCtx {
                order_id: 1,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.run(&mut world, 0u32);
        assert_eq!(cb.ctx.call_count, 3);
    }

    fn ctx_one_res_mut_handler(ctx: &mut TimerCtx, mut cache: ResMut<OrderCache>, _event: u32) {
        cache.expired.push(ctx.order_id);
        ctx.call_count += 1;
    }

    #[test]
    fn ctx_one_res_mut() {
        let mut builder = WorldBuilder::new();
        builder.register::<OrderCache>(OrderCache { expired: vec![] });
        let mut world = builder.build();

        let mut cb = ctx_one_res_mut_handler.into_callback(
            TimerCtx {
                order_id: 42,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.run(&mut world, 0u32);
        assert_eq!(cb.ctx.call_count, 1);
        assert_eq!(world.resource::<OrderCache>().expired, vec![42]);
    }

    fn ctx_two_params_handler(
        ctx: &mut TimerCtx,
        counter: Res<u64>,
        mut cache: ResMut<OrderCache>,
        _event: u32,
    ) {
        cache.expired.push(*counter);
        ctx.call_count += 1;
    }

    #[test]
    fn ctx_two_params() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(99);
        builder.register::<OrderCache>(OrderCache { expired: vec![] });
        let mut world = builder.build();

        let mut cb = ctx_two_params_handler.into_callback(
            TimerCtx {
                order_id: 0,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.run(&mut world, 0u32);
        assert_eq!(cb.ctx.call_count, 1);
        assert_eq!(world.resource::<OrderCache>().expired, vec![99]);
    }

    fn ctx_three_params_handler(
        ctx: &mut TimerCtx,
        a: Res<u64>,
        b: Res<bool>,
        mut c: ResMut<OrderCache>,
        _event: u32,
    ) {
        if *b {
            c.expired.push(*a);
        }
        ctx.call_count += 1;
    }

    #[test]
    fn ctx_three_params() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(7);
        builder.register::<bool>(true);
        builder.register::<OrderCache>(OrderCache { expired: vec![] });
        let mut world = builder.build();

        let mut cb = ctx_three_params_handler.into_callback(
            TimerCtx {
                order_id: 0,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.run(&mut world, 0u32);
        assert_eq!(cb.ctx.call_count, 1);
        assert_eq!(world.resource::<OrderCache>().expired, vec![7]);
    }

    // -- Context ownership ----------------------------------------------------

    #[test]
    fn ctx_mutated_persists() {
        let mut world = WorldBuilder::new().build();
        let mut cb = ctx_only_handler.into_callback(
            TimerCtx {
                order_id: 1,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.run(&mut world, 0u32);
        cb.run(&mut world, 0u32);
        cb.run(&mut world, 0u32);
        assert_eq!(cb.ctx.call_count, 3);
    }

    #[test]
    fn ctx_accessible_outside_dispatch() {
        let mut world = WorldBuilder::new().build();
        let mut cb = ctx_only_handler.into_callback(
            TimerCtx {
                order_id: 42,
                call_count: 0,
            },
            world.registry_mut(),
        );
        assert_eq!(cb.ctx.order_id, 42);
        assert_eq!(cb.ctx.call_count, 0);
        cb.run(&mut world, 0u32);
        assert_eq!(cb.ctx.call_count, 1);
    }

    #[test]
    fn ctx_mutated_outside_dispatch() {
        let mut world = WorldBuilder::new().build();
        let mut cb = ctx_only_handler.into_callback(
            TimerCtx {
                order_id: 1,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.ctx.order_id = 99;
        cb.run(&mut world, 0u32);
        assert_eq!(cb.ctx.order_id, 99);
        assert_eq!(cb.ctx.call_count, 1);
    }

    // -- Safety validation ----------------------------------------------------

    #[test]
    #[should_panic(expected = "not registered")]
    fn panics_on_missing_resource() {
        let mut world = WorldBuilder::new().build();

        fn needs_cache(_ctx: &mut TimerCtx, _cache: Res<OrderCache>, _e: u32) {}

        let _cb = needs_cache.into_callback(
            TimerCtx {
                order_id: 0,
                call_count: 0,
            },
            world.registry_mut(),
        );
    }

    #[test]
    #[should_panic(expected = "not registered")]
    fn panics_on_second_missing() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn needs_two(_ctx: &mut TimerCtx, _a: Res<u64>, _b: Res<OrderCache>, _e: u32) {}

        let _cb = needs_two.into_callback(
            TimerCtx {
                order_id: 0,
                call_count: 0,
            },
            world.registry_mut(),
        );
    }

    // -- Access conflict detection --------------------------------------------

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn callback_duplicate_access_panics() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn bad(_ctx: &mut u64, a: Res<u64>, b: ResMut<u64>) {
            let _ = (*a, &*b);
        }

        let _cb = no_event(bad).into_callback(0u64, world.registry_mut());
    }

    // -- Handler<E> interface -------------------------------------------------

    #[test]
    fn box_dyn_handler() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn add_ctx(ctx: &mut u64, mut val: ResMut<u64>, event: u64) {
            *val += event + *ctx;
        }

        let cb = add_ctx.into_callback(10u64, world.registry_mut());
        let mut boxed: Box<dyn Handler<u64>> = Box::new(cb);
        boxed.run(&mut world, 5u64);
        // 0 + 5 + 10 = 15
        assert_eq!(*world.resource::<u64>(), 15);
    }

    #[test]
    fn callback_in_vec_dyn() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn add(ctx: &mut u64, mut val: ResMut<u64>) {
            *val += *ctx;
        }
        fn mul(ctx: &mut u64, mut val: ResMut<u64>) {
            *val *= *ctx;
        }

        let cb_add = no_event(add).into_callback(3u64, world.registry_mut());
        let cb_mul = no_event(mul).into_callback(2u64, world.registry_mut());

        let mut handlers: Vec<Box<dyn Handler<()>>> = vec![Box::new(cb_add), Box::new(cb_mul)];

        for h in &mut handlers {
            h.run(&mut world, ());
        }
        // 0 + 3 = 3, then 3 * 2 = 6
        assert_eq!(*world.resource::<u64>(), 6);
    }

    fn with_local(_ctx: &mut u64, mut local: Local<u64>, mut val: ResMut<u64>) {
        *local += 1;
        *val = *local;
    }

    #[test]
    fn callback_with_local() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut cb = no_event(with_local).into_callback(0u64, world.registry_mut());
        cb.run(&mut world, ());
        cb.run(&mut world, ());
        cb.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 3);
    }

    // -- Integration ----------------------------------------------------------

    #[test]
    fn callback_interop_with_handler() {
        use crate::IntoHandler;

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        fn sys_add(mut val: ResMut<u64>, event: u64) {
            *val += event;
        }
        fn cb_mul(ctx: &mut u64, mut val: ResMut<u64>, _e: u64) {
            *val *= *ctx;
        }

        let sys = sys_add.into_handler(world.registry_mut());
        let cb = cb_mul.into_callback(3u64, world.registry_mut());

        let mut handlers: Vec<Box<dyn Handler<u64>>> = vec![Box::new(sys), Box::new(cb)];

        for h in &mut handlers {
            h.run(&mut world, 5u64);
        }
        // 0 + 5 = 5, then 5 * 3 = 15
        assert_eq!(*world.resource::<u64>(), 15);
    }

    // =========================================================================
    // NoEvent — Callback<C, NoEvent<F>, P> as Handler<()>
    // =========================================================================

    fn no_event_ctx_only(ctx: &mut TimerCtx) {
        ctx.call_count += 1;
    }

    #[test]
    fn no_event_callback_arity_0() {
        let mut world = WorldBuilder::new().build();
        let mut cb = no_event_ctx_only.into_callback(
            TimerCtx {
                order_id: 1,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.run(&mut world, ());
        cb.run(&mut world, ());
        assert_eq!(cb.ctx.call_count, 2);
    }

    fn no_event_ctx_one_res(ctx: &mut TimerCtx, mut val: ResMut<u64>) {
        *val += ctx.order_id;
        ctx.call_count += 1;
    }

    #[test]
    fn no_event_callback_arity_1() {
        use crate::no_event;

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut cb = no_event(no_event_ctx_one_res).into_callback(
            TimerCtx {
                order_id: 42,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.run(&mut world, ());
        assert_eq!(cb.ctx.call_count, 1);
        assert_eq!(*world.resource::<u64>(), 42);
    }

    fn no_event_ctx_two_params(ctx: &mut TimerCtx, src: Res<u32>, mut dst: ResMut<u64>) {
        *dst += *src as u64 + ctx.order_id;
        ctx.call_count += 1;
    }

    #[test]
    fn no_event_callback_arity_2() {
        use crate::no_event;

        let mut builder = WorldBuilder::new();
        builder.register::<u32>(10);
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut cb = no_event(no_event_ctx_two_params).into_callback(
            TimerCtx {
                order_id: 5,
                call_count: 0,
            },
            world.registry_mut(),
        );
        cb.run(&mut world, ());
        assert_eq!(cb.ctx.call_count, 1);
        assert_eq!(*world.resource::<u64>(), 15); // 10 + 5
    }

    #[test]
    fn no_event_callback_boxed() {
        use crate::no_event;

        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let cb = no_event(no_event_ctx_one_res).into_callback(
            TimerCtx {
                order_id: 7,
                call_count: 0,
            },
            world.registry_mut(),
        );
        let mut boxed: Box<dyn Handler<()>> = Box::new(cb);
        boxed.run(&mut world, ());
        assert_eq!(*world.resource::<u64>(), 7);
    }
}
