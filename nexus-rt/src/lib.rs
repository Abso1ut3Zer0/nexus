//! # nexus-rt
//!
//! Runtime primitives for single-threaded, event-driven systems.
//!
//! `nexus-rt` provides the building blocks for constructing runtimes where
//! user code runs as handlers dispatched over shared state. It is **not** an
//! async runtime — there is no task scheduler, no work stealing, no `Future`
//! polling. Instead, it provides:
//!
//! - **World** — [`World`] is a unified type-erased singleton store. Each
//!   registered type gets a direct pointer ([`ResourceId`]) — dispatch-time
//!   access is a single pointer deref with zero framework overhead.
//!
//! - **Resources** — [`Res`] and [`ResMut`] are what users see in handler
//!   function signatures. They deref to the inner value transparently.
//!
//! - **Handlers** — The [`Param`] trait resolves state at build time
//!   and produces references at dispatch time. [`IntoHandler`] converts
//!   plain functions into [`Handler`] trait objects for type-erased dispatch.
//!
//! - **Pipeline** — [`PipelineBuilder`] begins a typed per-event composition
//!   chain. Steps transform data using `Option` and `Result` for flow
//!   control. [`Pipeline`] implements [`Handler`] for direct or boxed dispatch.
//!   [`BatchPipeline`] owns a pre-allocated input buffer and runs each item
//!   through the same chain independently — errors on one item don't affect
//!   subsequent items.
//!
//! - **DAG Pipeline** — [`DagBuilder`] builds a monomorphized data-flow graph
//!   with fan-out and merge. Topology is encoded in the type system — no
//!   vtable dispatch, no arena allocation. [`Dag`] implements [`Handler`]
//!   for direct or boxed dispatch. [`BatchDag`] owns a pre-allocated input
//!   buffer and runs each item through the same DAG independently.
//!
//! - **Installer** — [`Installer`] is the install-time trait for event sources.
//!   `install()` registers resources into [`WorldBuilder`] and returns a
//!   concrete poller whose `poll()` method drives the event lifecycle.
//!
//! - **Templates** — [`HandlerTemplate`] and [`CallbackTemplate`] resolve
//!   parameters once, then stamp out handlers via [`generate()`](HandlerTemplate::generate)
//!   by copying pre-resolved state (a single memcpy). Use when handlers are
//!   created repeatedly on the hot path (IO re-registration, timer
//!   rescheduling).
//!
//! - **Plugin** — [`Plugin`] is a composable unit of resource registration.
//!   [`WorldBuilder::install_plugin`] consumes a plugin to configure state.
//!   Closures `FnOnce(&mut WorldBuilder)` implement `Plugin` automatically.
//!
//! - **Reactors** *(feature: `reactors`)* — Interest-based per-instance
//!   dispatch. Event handlers call `ReactorNotify::mark` to signal data
//!   changes. Subscribed reactors wake with O(1) dedup — per-instrument,
//!   per-strategy granularity. Replaces per-resource change detection with
//!   explicit, fine-grained notification. `SourceRegistry` maps domain
//!   keys to data sources for runtime routing.
//!
//! - **Derive macros** — `#[derive(Resource)]` marks types for World storage.
//!   `#[derive(Param)]` bundles multiple resources into a single handler
//!   parameter (sidesteps the 8-param arity limit). `#[derive(Deref, DerefMut)]`
//!   provides newtype ergonomics. [`new_resource!`] is a shorthand for
//!   newtype + Resource + Deref + From.
//!
//! # Quick Start
//!
//! ```
//! use nexus_rt::{WorldBuilder, ResMut, IntoHandler, Handler, Resource};
//!
//! #[derive(Resource)]
//! struct Counter(u64);
//!
//! let mut builder = WorldBuilder::new();
//! builder.register(Counter(0));
//! let mut world = builder.build();
//!
//! fn tick(mut counter: ResMut<Counter>, event: u32) {
//!     counter.0 += event as u64;
//! }
//!
//! let mut handler = tick.into_handler(world.registry());
//!
//! handler.run(&mut world, 10u32);
//!
//! assert_eq!(world.resource::<Counter>().0, 10);
//! ```
//!
//! # Safety
//!
//! The low-level `get` / `get_mut` methods on [`World`] are `unsafe` and
//! intended for framework internals. The caller must ensure:
//!
//! 1. The ID was obtained from the same builder that produced the container.
//! 2. The type parameter matches the type registered at that ID.
//! 3. No mutable aliasing — at most one `&mut T` exists per value at any time.
//!
//! User-facing APIs (`resource`, `resource_mut`, `Handler::run`) are fully safe.
//!
//! # Returning `impl Handler` from functions (Rust 2024)
//!
//! In Rust 2024, `impl Trait` in return position captures **all** in-scope
//! lifetimes by default. If a function takes `&Registry` and returns
//! `impl Handler<E>`, the returned type captures the registry borrow —
//! blocking subsequent `WorldBuilder` calls.
//!
//! Add `+ use<...>` to list only the type parameters the return type holds.
//! The `&Registry` is consumed during build — it is **not** retained:
//!
//! ```ignore
//! use nexus_rt::{Handler, PipelineBuilder, Res, ResMut};
//! use nexus_rt::world::Registry;
//!
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
//! Without `+ use<C>`, the compiler assumes the return type borrows
//! `reg`, and subsequent `wb.install_driver(...)` / `wb.build()` calls
//! fail with a borrow conflict.
//!
//! This applies to any factory function pattern — pipelines, DAGs,
//! handlers, callbacks, and templates. List every type parameter the
//! return type captures; omit the `&Registry` lifetime.
//!
//! # Bevy Analogies
//!
//! nexus-rt borrows heavily from Bevy ECS's system model. If you know
//! Bevy, these mappings may help:
//!
//! | nexus-rt | Bevy | Notes |
//! |----------|------|-------|
//! | [`Param`] | `SystemParam` | Two-phase init/fetch |
//! | [`Res<T>`] | `Res<T>` | Shared resource read |
//! | [`ResMut<T>`] | `ResMut<T>` | Exclusive resource write |
//! | [`Local<T>`] | `Local<T>` | Per-handler state |
//! | [`Handler<E>`] | `System` trait | Object-safe dispatch |
//! | [`IntoHandler`] | `IntoSystem` | fn → handler conversion |
//! | [`Plugin`] | `Plugin` | Composable registration |
//! | [`World`] | `World` | Singletons only (no ECS) |
//! | [`HandlerTemplate`] | *(no equivalent)* | Resolve-once, stamp-many |
//! | `ReactorNotify` | `Observer` (partial) | Interest-based per-instance dispatch |

#![warn(missing_docs)]
// SystemParam types (Res, ResMut, Local, Option<Res<T>>) must be passed by value
// for the HRTB double-bound inference pattern to work. Same pattern as Bevy.
#![allow(clippy::needless_pass_by_value)]
#![allow(clippy::trivially_copy_pass_by_ref)]
// Macro-generated codegen audit tests declare types inline within test functions.
#![allow(clippy::items_after_statements)]

#[macro_use]
mod tuples;

mod adapt;
mod callback;
mod catch_unwind;
/// Clock abstractions for event-driven runtimes.
pub mod clock;
mod combinator;
pub mod ctx_dag;
pub mod ctx_pipeline;
pub mod dag;
mod driver;
mod handler;
#[cfg(feature = "mio")]
pub mod mio;
pub mod pipeline;
mod plugin;
#[cfg(feature = "reactors")]
pub mod reactor;
mod resource;
pub mod scheduler;
pub mod shutdown;
pub mod system;
pub mod template;
pub mod testing;
#[cfg(feature = "timer")]
pub mod timer;
mod view;
mod world;

#[cfg(feature = "codegen-audit")]
pub mod codegen_audit;

pub use adapt::{Adapt, ByRef, Cloned, Owned};

pub use callback::{Callback, IntoCallback};
pub use catch_unwind::CatchAssertUnwindSafe;
pub use combinator::{Broadcast, FanOut};
pub use dag::{BatchDag, Dag, DagBuilder, resolve_arm};
pub use driver::Installer;
pub use handler::{
    CtxFree, Handler, HandlerFn, IntoHandler, Local, NoEvent, Opaque, OpaqueHandler, Param,
    RegistryRef, Resolved, no_event,
};
#[cfg(feature = "reactors")]
pub use reactor::{
    DataSource, DeferredRemovals, IntoReactor, PipelineReactor, Reactor, ReactorFn, ReactorNotify,
    ReactorRegistration, ReactorSystem, SourceRegistry,
};
// Note: `Param` derive macro and `Param` trait coexist — Rust's macro
// namespace is separate from the type namespace.
// Note: `View` derive macro and `View` trait coexist — Rust's macro
// namespace is separate from the type namespace (same as `Param`).
pub use ctx_dag::{
    CtxDag, CtxDagArm, CtxDagArmFork, CtxDagArmSeed, CtxDagBuilder, CtxDagChain, CtxDagChainFork,
    CtxMergeStepCall, IntoCtxMergeStep,
};
pub use ctx_pipeline::{
    CtxChainCall, CtxPipeline, CtxPipelineBuilder, CtxPipelineChain, CtxStepCall, IntoCtxProducer,
    IntoCtxRefStep, IntoCtxStep, resolve_ctx_step,
};
pub use nexus_rt_derive::{Deref, DerefMut, Param, Resource, View, select};
pub use pipeline::{
    BatchPipeline, ChainCall, IntoProducer, IntoRefScanStep, IntoRefStep, IntoScanStep, Pipeline,
    PipelineBuilder, PipelineChain, PipelineOutput, resolve_producer, resolve_ref_scan_step,
    resolve_ref_step, resolve_scan_step, resolve_step,
};
pub use plugin::Plugin;
pub use resource::{Res, ResMut, Seq, SeqMut};
pub use scheduler::{SchedulerBuilder, SystemScheduler};
pub use shutdown::{Shutdown, ShutdownHandle};
pub use system::{IntoSystem, System, SystemFn};
pub use template::{
    Blueprint, CallbackBlueprint, CallbackTemplate, HandlerTemplate, TemplatedCallback,
    TemplatedHandler,
};
pub use view::{View, ViewScope};
pub use world::{Registry, Resource, ResourceId, Sequence, World, WorldBuilder};

/// Declare a newtype resource with `Deref`/`DerefMut` to the inner type.
///
/// Generates a struct that implements [`Resource`], `Deref`, `DerefMut`,
/// and `From<Inner>`.
///
/// ```
/// use nexus_rt::new_resource;
///
/// new_resource!(
///     /// My custom counter.
///     #[derive(Debug, Default)]
///     pub MyCounter(u64)
/// );
///
/// let mut c = MyCounter::from(0u64);
/// *c += 1;
/// assert_eq!(*c, 1);
/// ```
#[macro_export]
macro_rules! new_resource {
    (
        $(#[$meta:meta])*
        $vis:vis $name:ident($inner:ty)
    ) => {
        $(#[$meta])*
        #[derive($crate::Resource)]
        $vis struct $name(pub $inner);

        impl ::core::ops::Deref for $name {
            type Target = $inner;

            #[inline]
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl ::core::ops::DerefMut for $name {
            #[inline]
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }

        impl ::core::convert::From<$inner> for $name {
            #[inline]
            fn from(inner: $inner) -> Self {
                Self(inner)
            }
        }
    };
}

/// Type alias for a boxed, type-erased [`Handler`].
///
/// Use `Virtual<E>` when you need to store heterogeneous handlers in a
/// collection (e.g. `Vec<Virtual<E>>`). One heap allocation per handler.
///
/// For inline storage (no heap), see `FlatVirtual` (panics if handler
/// doesn't fit) or `FlexVirtual` (inline with heap fallback). Both
/// require the `smartptr` feature.
pub type Virtual<E> = Box<dyn Handler<E>>;

/// Type alias for an inline [`Handler`] using [`nexus_smartptr::Flat`].
///
/// Stores the handler inline (no heap allocation). Panics if the concrete
/// handler doesn't fit in the buffer.
#[cfg(feature = "smartptr")]
pub type FlatVirtual<E, B = nexus_smartptr::B64> = nexus_smartptr::Flat<dyn Handler<E>, B>;

/// Type alias for an inline [`Handler`] with heap fallback using [`nexus_smartptr::Flex`].
///
/// Stores inline if the handler fits, otherwise heap-allocates.
#[cfg(feature = "smartptr")]
pub type FlexVirtual<E, B = nexus_smartptr::B64> = nexus_smartptr::Flex<dyn Handler<E>, B>;

#[cfg(feature = "mio")]
pub use self::mio::{BoxedMio, MioConfig, MioDriver, MioInstaller, MioPoller};

#[cfg(all(feature = "mio", feature = "smartptr"))]
pub use self::mio::{FlexMio, InlineMio};

#[cfg(feature = "timer")]
pub use timer::{
    BoundedTimerInstaller, BoundedTimerPoller, BoundedTimerWheel, BoundedWheel,
    BoundedWheelBuilder, BoxedTimers, ConfigError, Full, Periodic, TimerConfig, TimerHandle,
    TimerInstaller, TimerPoller, TimerWheel, UnboundedWheelBuilder, Wheel, WheelBuilder,
    WheelEntry,
};

#[cfg(all(feature = "timer", feature = "smartptr"))]
pub use timer::{
    BoundedFlexTimerWheel, BoundedInlineTimerWheel, FlexTimerWheel, FlexTimers, InlineTimerWheel,
    InlineTimers,
};
