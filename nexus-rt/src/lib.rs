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
//!   registered type gets a dense index ([`ResourceId`]) for ~3-cycle
//!   dispatch-time access.
//!
//! - **Resources** — [`Res`] and [`ResMut`] are what users see in handler
//!   function signatures. They deref to the inner value transparently.
//!
//! - **Handlers** — The [`Param`] trait resolves state at build time
//!   and produces references at dispatch time. [`IntoHandler`] converts
//!   plain functions into [`Handler`] trait objects for type-erased dispatch.
//!
//! - **Pipeline** — [`PipelineStart`] begins a typed per-event composition
//!   chain. Stages transform data using `Option` and `Result` for flow
//!   control. [`Pipeline`] implements [`Handler`] for direct or boxed dispatch.
//!   [`BatchPipeline`] owns a pre-allocated input buffer and runs each item
//!   through the same chain independently — errors on one item don't affect
//!   subsequent items.
//!
//! - **Installer** — [`Installer`] is the install-time trait for event sources.
//!   `install()` registers resources into [`WorldBuilder`] and returns a
//!   concrete poller whose `poll()` method drives the event lifecycle.
//!
//! - **Plugin** — [`Plugin`] is a composable unit of resource registration.
//!   [`WorldBuilder::install_plugin`] consumes a plugin to configure state.
//!
//! # Quick Start
//!
//! ```
//! use nexus_rt::{WorldBuilder, ResMut, IntoHandler, Handler};
//!
//! let mut builder = WorldBuilder::new();
//! builder.register::<u64>(0);
//! let mut world = builder.build();
//!
//! fn tick(mut counter: ResMut<u64>, event: u32) {
//!     *counter += event as u64;
//! }
//!
//! let mut handler = tick.into_handler(world.registry());
//!
//! handler.run(&mut world, 10u32);
//!
//! assert_eq!(*world.resource::<u64>(), 10);
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
//!
//! # Capacity Planning
//!
//! When storing handlers as `dyn Handler<E>` you choose between heap
//! allocation ([`Virtual`] = `Box`) or inline storage ([`FlatVirtual`] /
//! [`FlexVirtual`]). Inline storage avoids heap allocation on the hot
//! path but requires the concrete handler to fit in a fixed buffer.
//! This section explains what determines handler size so you can pick
//! the right buffer.
//!
//! ## What determines size
//!
//! Every handler stores:
//!
//! - **[`ResourceId`] state** — 2 bytes per `Res<T>` or `ResMut<T>`
//!   parameter (one `u16` index into [`World`]). Optional params
//!   (`Option<Res<T>>`) cost 4 bytes. [`Local<T>`] costs `sizeof(T)`.
//! - **Name** — `&'static str` (16 bytes) for diagnostics.
//! - **Context** — `sizeof(C)` for context-owning [`Callback`]s, zero
//!   for context-free [`HandlerFn`]s.
//! - **Function** — named functions are ZSTs (0 bytes). Closures are
//!   not supported by [`IntoHandler`] / [`IntoCallback`].
//!
//! [`TemplatedHandler`] adds type-erasure overhead: 3 function pointers
//! (24 bytes) and a second name copy, wrapped around an inline buffer
//! that holds the [`Callback`] struct.
//!
//! [`Pipeline`] size grows linearly with the number of stages (~24
//! bytes per stage). [`BatchPipeline`] adds a `Vec<In>` (24 bytes
//! header + heap buffer) on top.
//!
//! ## Reference table (measured, 64-bit)
//!
//! | Type | Size | Notes |
//! |------|------|-------|
//! | `HandlerFn` arity 0 | 16 B | event-only, no params |
//! | `HandlerFn` arity 1–4 | 24 B | |
//! | `HandlerFn` arity 5–8 | 32 B | max supported arity |
//! | `Callback` arity 4, 16 B ctx | 40 B | e.g. two `u64` fields |
//! | `Callback` arity 4, 32 B ctx | 56 B | |
//! | `Pipeline` 1 stage | 24 B | +24 B per additional stage |
//! | `TemplatedHandler` | 112 B | fixed, independent of arity |
//! | `HandlerTemplate` | 96 B | stored in World as resource |
//!
//! Struct alignment is 8 bytes (from `&'static str`), so all sizes
//! are multiples of 8. `TemplatedHandler` has 16-byte alignment
//! (from its inline buffer).
//!
//! ## Choosing storage
//!
//! | Storage | Size | Allocation | Best for |
//! |---------|------|------------|----------|
//! | `Virtual<E>` (Box) | 16 B | heap | simplest, rare creation |
//! | `FlatVirtual<E>` (B64) | 64 B | none | `HandlerFn`, `Callback` |
//! | `FlatVirtual<E, B128>` | 128 B | none | `TemplatedHandler` |
//! | `FlexVirtual<E>` | 64 B | fallback | mixed handler types |
//! | `FlexVirtual<E, B128>` | 128 B | fallback | mixed + templates |
//! | Concrete type | exact | none | when type is known |
//!
//! **`B64`** (default) — fits all `HandlerFn` and `Callback` types
//! through arity 8 with contexts up to ~24 bytes. Use this when all
//! your handlers are built via [`IntoHandler`] or [`IntoCallback`].
//!
//! **`B128`** — required for [`TemplatedHandler`] (112 bytes). Use
//! when mixing templates with regular handlers in the same collection,
//! or when callback contexts exceed ~24 bytes.
//!
//! **`FlexVirtual`** — stores inline when possible, falls back to
//! heap for oversized handlers. Useful when pipeline handlers (whose
//! size depends on chain depth) coexist with fixed-size handlers.
//!
//! **Concrete type** — when you know the handler type at compile time,
//! skip type erasure entirely. `HandlerFn` and `Callback` implement
//! [`Handler<E>`] directly.
//!
//! ## Verifying at compile time
//!
//! Use a const assertion to catch sizing mismatches early:
//!
//! ```
//! use nexus_rt::TemplatedHandler;
//!
//! const _: () = assert!(
//!     std::mem::size_of::<TemplatedHandler<u32>>() <= 128,
//!     "TemplatedHandler exceeds B128"
//! );
//! ```
//!
//! For concrete handlers whose type is hard to name, use
//! `std::mem::size_of_val` in a test:
//!
//! ```
//! use nexus_rt::{WorldBuilder, Res, ResMut, IntoHandler};
//!
//! fn my_handler(a: Res<u64>, b: ResMut<bool>, _event: u32) {}
//!
//! let mut wb = WorldBuilder::new();
//! wb.register::<u64>(0);
//! wb.register::<bool>(false);
//! let world = wb.build();
//!
//! let handler = my_handler.into_handler(world.registry());
//! assert!(std::mem::size_of_val(&handler) <= 64, "handler exceeds B64");
//! ```

#![warn(missing_docs)]

mod adapt;
mod callback;
mod catch_unwind;
mod driver;
mod handler;
#[cfg(feature = "mio")]
pub mod mio;
pub mod pipeline;
mod plugin;
mod resource;
mod template;
pub mod testing;
#[cfg(feature = "timer")]
pub mod timer;
mod world;

pub use adapt::Adapt;
pub use callback::{Callback, IntoCallback};
pub use catch_unwind::CatchAssertUnwindSafe;
pub use driver::Installer;
pub use handler::{CtxFree, Handler, HandlerFn, IntoHandler, Local, Param, RegistryRef};
pub use pipeline::{
    BatchPipeline, IntoStage, Pipeline, PipelineBuilder, PipelineOutput, PipelineStart,
};
pub use plugin::Plugin;
pub use resource::{Res, ResMut};
pub use template::{
    Blueprint, CallbackBlueprint, CallbackTemplate, HandlerTemplate, TemplatedHandler,
};
pub use world::{Registry, ResourceId, Sequence, World, WorldBuilder};

/// Type alias for a boxed, type-erased [`Handler`].
///
/// Use `Virtual<E>` when you need to store heterogeneous handlers in a
/// collection (e.g. `Vec<Virtual<E>>`). One heap allocation per handler.
///
/// For inline storage (no heap), see [`FlatVirtual`] (panics if handler
/// doesn't fit) or [`FlexVirtual`] (inline with heap fallback). Both
/// require the `smartptr` feature.
pub type Virtual<E> = Box<dyn Handler<E>>;

/// Type alias for an inline [`Handler`] using [`nexus_smartptr::Flat`].
///
/// Stores the handler inline (no heap allocation). Panics if the concrete
/// handler doesn't fit in the buffer.
///
/// # Buffer sizing
///
/// The default `B64` (64 bytes) fits all [`HandlerFn`] and [`Callback`]
/// types up to arity 8. For [`TemplatedHandler`], use `B128` (112 bytes
/// including fn ptrs and name). [`Pipeline`](pipeline::Pipeline) sizes
/// depend on chain depth — use [`FlexVirtual`] or measure with
/// `std::mem::size_of_val`.
#[cfg(feature = "smartptr")]
pub type FlatVirtual<E, B = nexus_smartptr::B64> = nexus_smartptr::Flat<dyn Handler<E>, B>;

/// Type alias for an inline [`Handler`] with heap fallback using [`nexus_smartptr::Flex`].
///
/// Stores inline if the handler fits, otherwise heap-allocates.
/// See [`FlatVirtual`] for buffer sizing guidance.
#[cfg(feature = "smartptr")]
pub type FlexVirtual<E, B = nexus_smartptr::B64> = nexus_smartptr::Flex<dyn Handler<E>, B>;

#[cfg(feature = "mio")]
pub use self::mio::{BoxedMio, MioConfig, MioDriver, MioInstaller, MioPoller, MioToken};

#[cfg(all(feature = "mio", feature = "smartptr"))]
pub use self::mio::{FlexMio, InlineMio};

#[cfg(feature = "timer")]
pub use timer::{BoxedTimers, Periodic, TimerConfig, TimerInstaller, TimerPoller, TimerWheel};

#[cfg(all(feature = "timer", feature = "smartptr"))]
pub use timer::{FlexTimerWheel, FlexTimers, InlineTimerWheel, InlineTimers};
