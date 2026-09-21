# nexus-rt Documentation

Event-driven runtime with zero-cost dispatch.

## Architecture

- [Architecture](ARCHITECTURE.md) — Design philosophy, component map, data flow
- [Unsafe & Soundness](UNSAFE_AND_SOUNDNESS.md) — Every unsafe pattern, invariants, miri coverage

## User Guide

- [Getting Started](getting-started.md) — Build your first nexus-rt application
- [World & Resources](world.md) — The resource model: registration, access, lifetimes
- [Handlers](handlers.md) — Writing handlers, parameter resolution, named functions
- [Callbacks](callbacks.md) — Handlers with owned mutable state
- [Pipelines](pipelines.md) — Linear processing chains with combinators
- [DAGs](dag.md) — Data-flow graphs with fan-out and merge
- [Dispatch](dispatch.md) — Runtime keyed dispatch: `#[derive(Dispatchable)]`, `.dispatch_variant`, `.dispatch_on`
- [Reactors](reactors.md) — Interest-based dynamic dispatch (feature: reactors)
- [Templates](templates.md) — Stamping handlers from blueprints
- [Drivers](drivers.md) — The installer/poller pattern for IO and timers
- [Writing Your Own Driver](writing-drivers.md) — Implementing custom drivers, the self-referential dispatch problem, take/return and deferred-operations patterns
- [Clock](clock.md) — Time sources: realtime, test, historical
- [Poll Loop](poll-loop.md) — Building your event loop
- [Testing Guide](testing-guide.md) — TestHarness, TestTimerDriver, deterministic replay
- [Derive Macros](derives.md) — Resource, Param, Deref/DerefMut derives and new_resource!

## Internal Reference

These documents explain internal design decisions for contributors:

- [Annotation Traits](annotation-traits.md) — Compile-time config via marker traits
- [Chain Types](chain-types.md) — Why pipelines use named types, not closures
- [Codegen Audit](codegen-audit.md) — Assembly verification of zero-cost dispatch
