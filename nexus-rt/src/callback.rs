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
/// # Memory Layout
///
/// ```text
/// sizeof(Callback<C, F, P>) = sizeof(C) + sizeof(F) + sizeof(P::State) + 16
/// ```
///
/// For named functions `F` is a ZST (0 bytes). `P::State` is N × 2 bytes
/// where N is the parameter arity ([`ResourceId`](crate::ResourceId) is `u16`).
/// The 16 bytes are the `&'static str` name.
///
/// | Type | Size |
/// |------|------|
/// | `HandlerFn` arity 0 | 16 bytes |
/// | `HandlerFn` arity 1–4 | 24 bytes |
/// | `HandlerFn` arity 5–8 | 32 bytes |
/// | `Callback` arity 4, 16B ctx | 40 bytes |
/// | `Callback` arity 4, 32B ctx | 56 bytes |
///
/// Struct alignment is 8 (from the `&'static str` name field), so
/// sizes round up to the next multiple of 8.
///
/// See the capacity planning section in the [crate-level docs](crate)
/// for storage recommendations.
///
/// # Examples
///
/// ```
/// use nexus_rt::{WorldBuilder, ResMut, IntoCallback, Handler};
///
/// struct Ctx { count: u64 }
///
/// fn handler(ctx: &mut Ctx, mut val: ResMut<u64>, event: u32) {
///     *val += event as u64;
///     ctx.count += 1;
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register::<u64>(0);
/// let mut world = builder.build();
///
/// let mut cb = handler.into_callback(Ctx { count: 0 }, world.registry());
/// cb.run(&mut world, 10u32);
///
/// assert_eq!(cb.ctx.count, 1);
/// assert_eq!(*world.resource::<u64>(), 10);
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
/// # Callback templates
///
/// For dispatch-time callback creation without HashMap lookups, use
/// [`resolve`](Self::resolve) at setup to pre-resolve parameter state,
/// then [`with_state`](Self::with_state) on the hot path:
///
/// ```
/// use nexus_rt::{WorldBuilder, ResMut, IntoCallback, Handler};
///
/// struct TimerCtx { order_id: u64, fires: u64 }
///
/// fn on_timeout(ctx: &mut TimerCtx, mut counter: ResMut<u64>, _event: ()) {
///     ctx.fires += 1;
///     *counter += ctx.order_id;
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register::<u64>(0);
///
/// // Pre-resolve once (cold path):
/// let state = on_timeout.resolve(builder.registry());
///
/// // Stamp out callbacks with different contexts (hot path):
/// let mut cb = on_timeout.with_state(
///     TimerCtx { order_id: 42, fires: 0 },
///     state,
/// );
/// ```
///
/// # Examples
///
/// ```
/// use nexus_rt::{WorldBuilder, ResMut, IntoCallback, Handler};
///
/// struct TimerCtx { order_id: u64, fires: u64 }
///
/// fn on_timeout(ctx: &mut TimerCtx, mut counter: ResMut<u64>, _event: ()) {
///     ctx.fires += 1;
///     *counter += ctx.order_id;
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register::<u64>(0);
/// let mut world = builder.build();
///
/// let mut cb = on_timeout.into_callback(
///     TimerCtx { order_id: 42, fires: 0 },
///     world.registry(),
/// );
/// cb.run(&mut world, ());
///
/// assert_eq!(cb.ctx.fires, 1);
/// assert_eq!(*world.resource::<u64>(), 42);
/// ```
///
/// # Panics
///
/// Panics if any [`Param`] resource is not registered in the
/// [`Registry`](crate::Registry).
pub trait IntoCallback<C, E, Params> {
    /// The concrete Callback type produced.
    type Callback: Handler<E>;

    /// Pre-resolve parameter state from the registry.
    ///
    /// Returns the cached state ([`ResourceId`](crate::ResourceId)s) needed
    /// to construct callbacks without HashMap lookups. Validates access
    /// conflicts.
    ///
    /// # Panics
    ///
    /// Panics if any required resource is not registered, or if
    /// parameter accesses conflict.
    fn resolve(&self, registry: &Registry) -> <Params as Param>::State
    where
        Params: Param,
    {
        let _ = registry;
        unimplemented!(
            "IntoCallback::resolve not implemented for {}",
            std::any::type_name::<Self>(),
        )
    }

    /// Construct a callback from context and pre-resolved parameter state.
    ///
    /// Zero HashMap lookups. The `state` must have been produced by
    /// [`resolve`](Self::resolve) on a compatible registry.
    fn with_state(self, ctx: C, state: <Params as Param>::State) -> Self::Callback
    where
        Params: Param,
        Self: Sized,
    {
        let _ = (ctx, state);
        unimplemented!(
            "IntoCallback::with_state not implemented for {}",
            std::any::type_name::<Self>(),
        )
    }

    /// Convert this function + context into a Callback.
    fn into_callback(self, ctx: C, registry: &Registry) -> Self::Callback;
}

// =============================================================================
// Arity 0: fn(ctx: &mut C, E) — context + event only, no Param
// =============================================================================

impl<C: Send + 'static, E, F: FnMut(&mut C, E) + Send + 'static> IntoCallback<C, E, ()> for F {
    type Callback = Callback<C, F, ()>;

    fn resolve(&self, registry: &Registry) -> <() as Param>::State {
        <() as Param>::init(registry);
    }

    fn with_state(self, ctx: C, _state: <() as Param>::State) -> Self::Callback {
        Callback {
            ctx,
            f: self,
            state: (),
            name: std::any::type_name::<F>(),
        }
    }

    fn into_callback(self, ctx: C, registry: &Registry) -> Self::Callback {
        self.resolve(registry);
        self.with_state(ctx, ())
    }
}

impl<C: Send + 'static, E, F: FnMut(&mut C, E) + Send + 'static> Handler<E> for Callback<C, F, ()> {
    fn run(&mut self, _world: &mut World, event: E) {
        (self.f)(&mut self.ctx, event);
    }

    fn inputs_changed(&self, _world: &World) -> bool {
        // Context-only callback — no resource dependencies to check.
        // Always returns true so the drivers never skip it.
        true
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

            #[allow(non_snake_case)]
            fn resolve(&self, registry: &Registry) -> <($($P,)+) as Param>::State {
                let state = <($($P,)+) as Param>::init(registry);
                {
                    let ($($P,)+) = &state;
                    registry.check_access(&[
                        $(
                            (<$P as Param>::resource_id($P),
                             std::any::type_name::<$P>()),
                        )+
                    ]);
                }
                state
            }

            fn with_state(self, ctx: C, state: <($($P,)+) as Param>::State) -> Self::Callback {
                Callback { ctx, f: self, state, name: std::any::type_name::<F>() }
            }

            fn into_callback(self, ctx: C, registry: &Registry) -> Self::Callback {
                let state = self.resolve(registry);
                self.with_state(ctx, state)
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
                #[allow(clippy::too_many_arguments)]
                fn call_inner<Ctx, $($P,)+ Ev>(
                    mut f: impl FnMut(&mut Ctx, $($P,)+ Ev),
                    ctx: &mut Ctx,
                    $($P: $P,)+
                    event: Ev,
                ) {
                    f(ctx, $($P,)+ event);
                }

                // SAFETY: state was produced by init() on the same registry
                // that built this world. Single-threaded sequential dispatch
                // ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, &mut self.ctx, $($P,)+ event);
            }

            fn inputs_changed(&self, world: &World) -> bool {
                <($($P,)+) as Param>::any_changed(&self.state, world)
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }
    };
}

// Reuse all_tuples — re-declared here since macros are module-scoped.
macro_rules! all_tuples {
    ($m:ident) => {
        $m!(P0);
        $m!(P0, P1);
        $m!(P0, P1, P2);
        $m!(P0, P1, P2, P3);
        $m!(P0, P1, P2, P3, P4);
        $m!(P0, P1, P2, P3, P4, P5);
        $m!(P0, P1, P2, P3, P4, P5, P6);
        $m!(P0, P1, P2, P3, P4, P5, P6, P7);
    };
}

all_tuples!(impl_into_callback);

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Local, Res, ResMut, WorldBuilder};

    // -- Helper types ---------------------------------------------------------

    struct TimerCtx {
        order_id: u64,
        call_count: u64,
    }

    struct OrderCache {
        expired: Vec<u64>,
    }

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

        fn bad(_ctx: &mut u64, a: Res<u64>, b: ResMut<u64>, _e: ()) {
            let _ = (*a, &*b);
        }

        let _cb = bad.into_callback(0u64, world.registry_mut());
    }

    // -- Change detection -----------------------------------------------------

    fn reads_resource(_ctx: &mut u64, _val: Res<u64>, _e: ()) {}

    #[test]
    fn inputs_changed_delegates() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let cb = reads_resource.into_callback(0u64, world.registry_mut());

        // Seq 0: changed_at=0, current_sequence=0 → changed
        assert!(cb.inputs_changed(&world));

        world.next_sequence();
        assert!(!cb.inputs_changed(&world));

        *world.resource_mut::<u64>() = 42;
        assert!(cb.inputs_changed(&world));
    }

    #[test]
    fn inputs_changed_true_no_params() {
        let mut world = WorldBuilder::new().build();
        let cb = ctx_only_handler.into_callback(
            TimerCtx {
                order_id: 0,
                call_count: 0,
            },
            world.registry_mut(),
        );
        // Context-only callbacks always run — scheduler must not skip them.
        assert!(cb.inputs_changed(&world));
    }

    fn stamps_writer(_ctx: &mut u64, mut val: ResMut<u64>, _e: ()) {
        *val = 99;
    }

    #[test]
    fn mut_stamps_changed_at() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut cb = stamps_writer.into_callback(0u64, world.registry_mut());

        world.next_sequence(); // tick=1
        let id = world.id::<u64>();
        unsafe {
            assert_eq!(world.changed_at(id), crate::Sequence(0));
        }

        cb.run(&mut world, ());
        unsafe {
            assert_eq!(world.changed_at(id), crate::Sequence(1));
        }
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

        fn add(ctx: &mut u64, mut val: ResMut<u64>, _e: ()) {
            *val += *ctx;
        }
        fn mul(ctx: &mut u64, mut val: ResMut<u64>, _e: ()) {
            *val *= *ctx;
        }

        let cb_add = add.into_callback(3u64, world.registry_mut());
        let cb_mul = mul.into_callback(2u64, world.registry_mut());

        let mut handlers: Vec<Box<dyn Handler<()>>> = vec![Box::new(cb_add), Box::new(cb_mul)];

        for h in handlers.iter_mut() {
            h.run(&mut world, ());
        }
        // 0 + 3 = 3, then 3 * 2 = 6
        assert_eq!(*world.resource::<u64>(), 6);
    }

    fn with_local(_ctx: &mut u64, mut local: Local<u64>, mut val: ResMut<u64>, _e: ()) {
        *local += 1;
        *val = *local;
    }

    #[test]
    fn callback_with_local() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut cb = with_local.into_callback(0u64, world.registry_mut());
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

        for h in handlers.iter_mut() {
            h.run(&mut world, 5u64);
        }
        // 0 + 5 = 5, then 5 * 3 = 15
        assert_eq!(*world.resource::<u64>(), 15);
    }
}
