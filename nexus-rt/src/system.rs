//! Reconciliation systems with boolean propagation.
//!
//! [`System`] is the dispatch trait for per-pass reconciliation logic.
//! Unlike [`Handler`](crate::Handler) (reactive, per-event, no return
//! value), systems return `bool` to control DAG traversal in a
//! [`SystemScheduler`](crate::scheduler::SystemScheduler).
//!
//! # When to use System vs Handler
//!
//! Use **Handler** when reacting to external events (market data, IO,
//! timers). Use **System** when reconciling derived state after events
//! have been processed. The typical pattern:
//!
//! 1. Event handler writes to resources (`ResMut<MidPrice>`)
//! 2. Scheduler runs systems in stage order
//! 3. Systems read upstream resources, compute derived state, return
//!    `bool` to propagate or skip downstream stages
//!
//! Systems are converted from plain functions via [`IntoSystem`], using
//! the same HRTB double-bound pattern as [`IntoHandler`](crate::IntoHandler).
//!
//! # Supported signatures
//!
//! - `fn(params...) -> bool` — returns propagation decision for
//!   staged scheduling
//! - `fn(params...)` — void return, always propagates (`true`). Useful
//!   for [`World::run_startup`] and systems that unconditionally
//!   propagate.

// Handler arity is architecturally required by the Param trait — handlers
// take N typed parameters and the macro-generated dispatch impls expand
// per-arity into call_inner functions with N + Input arguments. Module-level
// allow rather than one inline attribute per arity expansion.
#![allow(clippy::too_many_arguments)]

use crate::handler::Param;
use crate::world::{Registry, World};

// =============================================================================
// System trait
// =============================================================================

/// Object-safe dispatch trait for reconciliation systems.
///
/// Returns `bool` to control downstream propagation in a DAG scheduler.
/// `true` means "my outputs changed, run downstream systems."
/// `false` means "nothing changed, skip downstream."
///
/// # Difference from [`Handler`](crate::Handler)
///
/// | | Handler | System |
/// |---|---------|--------|
/// | Trigger | Per-event | Per-scheduler-pass |
/// | Event param | Yes (`E`) | No |
/// | Return | `()` | `bool` |
/// | Purpose | React | Reconcile |
pub trait System: Send {
    /// Run this system. Returns `true` if downstream systems should run.
    fn run(&mut self, world: &mut World) -> bool;

    /// Returns the system's name for diagnostics.
    fn name(&self) -> &'static str {
        "<unnamed>"
    }
}

// =============================================================================
// SystemFn — concrete dispatch wrapper
// =============================================================================

/// Concrete system wrapper produced by [`IntoSystem`].
///
/// Stores the function, pre-resolved parameter state, and a diagnostic
/// name. Users rarely name this type directly — use `Box<dyn System>`
/// for type-erased storage, or let inference handle the concrete type.
///
/// The `Marker` parameter distinguishes bool-returning systems from
/// void-returning ones, avoiding overlapping `System` impls.
pub struct SystemFn<F, Params: Param, Marker = bool> {
    f: F,
    state: Params::State,
    name: &'static str,
    _marker: std::marker::PhantomData<Marker>,
}

// =============================================================================
// IntoSystem — conversion trait
// =============================================================================

/// Converts a plain function into a [`System`].
///
/// Accepts two signatures:
/// - `fn(params...) -> bool` — returns propagation decision
/// - `fn(params...)` — void return, always propagates (`true`)
///
/// The `Marker` type parameter (defaulting to `bool`) distinguishes
/// between the two. Existing code using `IntoSystem<Params>` continues
/// to require `-> bool` with no changes.
///
/// Parameters are resolved from a [`Registry`] at conversion time.
///
/// # Closures vs named functions
///
/// Zero-parameter systems accept closures. For parameterized systems
/// (one or more [`Param`] arguments), Rust's HRTB + GAT inference
/// fails on closures — use named functions. Same limitation as
/// [`IntoHandler`](crate::IntoHandler).
///
/// # Examples
///
/// Bool-returning (scheduler propagation):
///
/// ```
/// use nexus_rt::{WorldBuilder, Res, ResMut, IntoSystem, System, Resource};
///
/// #[derive(Resource)]
/// struct Val(u64);
/// #[derive(Resource)]
/// struct Flag(bool);
///
/// fn reconcile(val: Res<Val>, mut flag: ResMut<Flag>) -> bool {
///     if val.0 > 10 {
///         flag.0 = true;
///         true
///     } else {
///         false
///     }
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register(Val(42));
/// builder.register(Flag(false));
/// let mut world = builder.build();
///
/// let mut sys = reconcile.into_system(world.registry());
/// assert!(sys.run(&mut world));
/// assert!(world.resource::<Flag>().0);
/// ```
///
/// Void-returning (startup, unconditional propagation):
///
/// ```
/// use nexus_rt::{WorldBuilder, ResMut, IntoSystem, System, Resource};
///
/// #[derive(Resource)]
/// struct Val(u64);
///
/// fn initialize(mut val: ResMut<Val>) {
///     val.0 = 42;
/// }
///
/// let mut builder = WorldBuilder::new();
/// builder.register(Val(0));
/// let mut world = builder.build();
///
/// let mut sys = initialize.into_system(world.registry());
/// assert!(sys.run(&mut world)); // void → always true
/// assert_eq!(world.resource::<Val>().0, 42);
/// ```
///
/// # Panics
///
/// Panics if any [`Param`] resource is not registered in
/// the [`Registry`].
pub trait IntoSystem<Params, Marker = bool> {
    /// The concrete system type produced.
    type System: System + 'static;

    /// Convert this function into a system, resolving parameters from the registry.
    fn into_system(self, registry: &Registry) -> Self::System;
}

// =============================================================================
// Arity 0: fn() -> bool
// =============================================================================

impl<F: FnMut() -> bool + Send + 'static> IntoSystem<()> for F {
    type System = SystemFn<F, ()>;

    fn into_system(self, registry: &Registry) -> Self::System {
        SystemFn {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: FnMut() -> bool + Send + 'static> System for SystemFn<F, ()> {
    fn run(&mut self, _world: &mut World) -> bool {
        (self.f)()
    }

    fn name(&self) -> &'static str {
        self.name
    }
}

// =============================================================================
// Arity 0: fn() — void return (always propagates)
// =============================================================================

impl<F: FnMut() + Send + 'static> IntoSystem<(), ()> for F {
    type System = SystemFn<F, (), ()>;

    fn into_system(self, registry: &Registry) -> Self::System {
        SystemFn {
            f: self,
            state: <() as Param>::init(registry),
            name: std::any::type_name::<F>(),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: FnMut() + Send + 'static> System for SystemFn<F, (), ()> {
    fn run(&mut self, _world: &mut World) -> bool {
        (self.f)();
        true
    }

    fn name(&self) -> &'static str {
        self.name
    }
}

// =============================================================================
// Macro-generated impls (arities 1-8)
// =============================================================================

macro_rules! impl_into_system {
    ($($P:ident),+) => {
        impl<F: Send + 'static, $($P: Param + 'static),+> IntoSystem<($($P,)+)> for F
        where
            for<'a> &'a mut F: FnMut($($P,)+) -> bool
                              + FnMut($($P::Item<'a>,)+) -> bool,
        {
            type System = SystemFn<F, ($($P,)+)>;

            fn into_system(self, registry: &Registry) -> Self::System {
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
                SystemFn {
                    f: self,
                    state,
                    name: std::any::type_name::<F>(),
                    _marker: std::marker::PhantomData,
                }
            }
        }

        impl<F: Send + 'static, $($P: Param + 'static),+> System
            for SystemFn<F, ($($P,)+)>
        where
            for<'a> &'a mut F: FnMut($($P,)+) -> bool
                              + FnMut($($P::Item<'a>,)+) -> bool,
        {
            #[allow(non_snake_case)]
            fn run(&mut self, world: &mut World) -> bool {
                fn call_inner<$($P),+>(
                    mut f: impl FnMut($($P),+) -> bool,
                    $($P: $P,)+
                ) -> bool {
                    f($($P),+)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by init() on the same registry
                // that built this world. Single-threaded sequential dispatch
                // ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P),+)
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }
    };
}

all_tuples!(impl_into_system);

// =============================================================================
// Macro-generated void impls (arities 1-8) — always returns true
// =============================================================================

macro_rules! impl_into_system_void {
    ($($P:ident),+) => {
        impl<F: Send + 'static, $($P: Param + 'static),+> IntoSystem<($($P,)+), ()> for F
        where
            for<'a> &'a mut F: FnMut($($P,)+)
                              + FnMut($($P::Item<'a>,)+),
        {
            type System = SystemFn<F, ($($P,)+), ()>;

            fn into_system(self, registry: &Registry) -> Self::System {
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
                SystemFn {
                    f: self,
                    state,
                    name: std::any::type_name::<F>(),
                    _marker: std::marker::PhantomData,
                }
            }
        }

        impl<F: Send + 'static, $($P: Param + 'static),+> System
            for SystemFn<F, ($($P,)+), ()>
        where
            for<'a> &'a mut F: FnMut($($P,)+)
                              + FnMut($($P::Item<'a>,)+),
        {
            #[allow(non_snake_case)]
            fn run(&mut self, world: &mut World) -> bool {
                fn call_inner<$($P),+>(
                    mut f: impl FnMut($($P),+),
                    $($P: $P,)+
                ) {
                    f($($P),+)
                }

                #[cfg(debug_assertions)]
                world.clear_borrows();
                // SAFETY: state was produced by init() on the same registry
                // that built this world. Single-threaded sequential dispatch
                // ensures no mutable aliasing across params.
                let ($($P,)+) = unsafe {
                    <($($P,)+) as Param>::fetch(world, &mut self.state)
                };
                call_inner(&mut self.f, $($P),+);
                true
            }

            fn name(&self) -> &'static str {
                self.name
            }
        }
    };
}

all_tuples!(impl_into_system_void);

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Local, Res, ResMut, WorldBuilder};

    // -- Arity 0 ----------------------------------------------------------

    fn always_true() -> bool {
        true
    }

    #[test]
    fn arity_0_system() {
        let mut world = WorldBuilder::new().build();
        let mut sys = always_true.into_system(world.registry());
        assert!(sys.run(&mut world));
    }

    // -- Single param -----------------------------------------------------

    fn check_threshold(val: Res<u64>) -> bool {
        *val > 10
    }

    #[test]
    fn single_param_system() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);
        let mut world = builder.build();

        let mut sys = check_threshold.into_system(world.registry());
        assert!(sys.run(&mut world));
    }

    #[test]
    fn single_param_system_false() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(5);
        let mut world = builder.build();

        let mut sys = check_threshold.into_system(world.registry());
        assert!(!sys.run(&mut world));
    }

    // -- Two params -------------------------------------------------------

    fn reconcile(val: Res<u64>, mut flag: ResMut<bool>) -> bool {
        if *val > 10 {
            *flag = true;
            true
        } else {
            false
        }
    }

    #[test]
    fn two_param_system() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);
        builder.register::<bool>(false);
        let mut world = builder.build();

        let mut sys = reconcile.into_system(world.registry());
        assert!(sys.run(&mut world));
        assert!(*world.resource::<bool>());
    }

    // -- Box<dyn System> --------------------------------------------------

    #[test]
    fn box_dyn_system() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);
        let mut world = builder.build();

        let mut boxed: Box<dyn System> = Box::new(check_threshold.into_system(world.registry()));
        assert!(boxed.run(&mut world));
    }

    // -- Access conflict detection ----------------------------------------

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn system_access_conflict_panics() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let world = builder.build();

        fn bad(a: Res<u64>, b: ResMut<u64>) -> bool {
            let _ = (*a, &*b);
            true
        }

        let _sys = bad.into_system(world.registry());
    }

    // -- Local<T> in systems ----------------------------------------------

    fn counting_system(mut count: Local<u64>, mut val: ResMut<u64>) -> bool {
        *count += 1;
        *val = *count;
        *count < 3
    }

    #[test]
    fn local_in_system() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut sys = counting_system.into_system(world.registry());
        assert!(sys.run(&mut world)); // count=1 < 3
        assert!(sys.run(&mut world)); // count=2 < 3
        assert!(!sys.run(&mut world)); // count=3, not < 3
        assert_eq!(*world.resource::<u64>(), 3);
    }

    // -- Name -------------------------------------------------------------

    #[test]
    fn system_has_name() {
        let world = WorldBuilder::new().build();
        let sys = always_true.into_system(world.registry());
        assert!(sys.name().contains("always_true"));
    }

    // -- Void-returning systems -----------------------------------------------

    fn noop() {}

    #[test]
    fn arity_0_void_system() {
        let mut world = WorldBuilder::new().build();
        let mut sys = noop.into_system(world.registry());
        assert!(sys.run(&mut world));
    }

    fn write_val(mut v: ResMut<u64>) {
        *v = 99;
    }

    #[test]
    fn arity_n_void_system() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut sys = write_val.into_system(world.registry());
        assert!(sys.run(&mut world));
        assert_eq!(*world.resource::<u64>(), 99);
    }

    #[test]
    fn box_dyn_void_system() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut boxed: Box<dyn System> = Box::new(write_val.into_system(world.registry()));
        assert!(boxed.run(&mut world));
        assert_eq!(*world.resource::<u64>(), 99);
    }

    fn void_read_only(val: Res<u64>, flag: Res<bool>) {
        let _ = (*val, *flag);
    }

    #[test]
    fn void_two_params_read_only() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(42);
        builder.register::<bool>(true);
        let mut world = builder.build();

        let mut sys = void_read_only.into_system(world.registry());
        assert!(sys.run(&mut world));
    }

    fn void_two_params_write(mut a: ResMut<u64>, mut b: ResMut<bool>) {
        *a = 77;
        *b = true;
    }

    #[test]
    fn void_two_params_mixed() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        builder.register::<bool>(false);
        let mut world = builder.build();

        let mut sys = void_two_params_write.into_system(world.registry());
        assert!(sys.run(&mut world));
        assert_eq!(*world.resource::<u64>(), 77);
        assert!(*world.resource::<bool>());
    }

    fn void_with_local(mut count: Local<u64>, mut out: ResMut<u64>) {
        *count += 1;
        *out = *count;
    }

    #[test]
    fn void_local_persists() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let mut world = builder.build();

        let mut sys = void_with_local.into_system(world.registry());
        assert!(sys.run(&mut world));
        assert_eq!(*world.resource::<u64>(), 1);
        assert!(sys.run(&mut world));
        assert_eq!(*world.resource::<u64>(), 2);
        assert!(sys.run(&mut world));
        assert_eq!(*world.resource::<u64>(), 3);
    }

    #[test]
    fn void_system_has_name() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let world = builder.build();

        let sys = write_val.into_system(world.registry());
        assert!(sys.name().contains("write_val"));
    }

    #[test]
    #[should_panic(expected = "conflicting access")]
    fn void_system_access_conflict_panics() {
        let mut builder = WorldBuilder::new();
        builder.register::<u64>(0);
        let world = builder.build();

        fn bad_void(a: Res<u64>, b: ResMut<u64>) {
            let _ = (*a, &*b);
        }

        let _sys = bad_void.into_system(world.registry());
    }
}
