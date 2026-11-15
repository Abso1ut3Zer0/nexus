# nexus-async-rt Documentation

Single-threaded async executor for nexus-rt. Slab-allocated tasks, zero-cost
wakers, mio-driven IO, and a tokio bridge for ecosystem code on cold paths.

## Architecture

- [Architecture](ARCHITECTURE.md) — Executor, task layout, wakers, cross-thread
  wake queue, free action state machine
- [Unsafe & Soundness](UNSAFE_AND_SOUNDNESS.md) — Every unsafe pattern,
  invariants, miri coverage

## User Guide

- [API Guide](API_GUIDE.md) — Top-level usage: RuntimeBuilder, block_on,
  spawn, JoinHandle
- [Task Spawning](task-spawning.md) — `spawn_boxed`, `spawn_slab`,
  `SlabClaim`, JoinHandle, detachment, abort
- [Timers and Time](timers-and-time.md) — `sleep`, `timeout`, `interval`,
  `event_time`, `yield_now`
- [Cancellation](cancellation.md) — `CancellationToken`, hierarchical
  cancellation, `ShutdownSignal`
- [Channels](channels.md) — `local`, `spsc`, `mpsc`, byte-oriented variants
- [Integration with nexus-rt](integration-with-nexus-rt.md) — `WorldCtx`,
  `WorldCtx::current()`, pre-resolved handler dispatch from async tasks
- [Tokio Compatibility](tokio-compat.md) — `with_tokio`, `spawn_on_tokio`,
  bridging ecosystem crates
- [Patterns](patterns.md) — Cookbook: event loops, per-connection tasks,
  heartbeats, reconnect, fan-in, pre-resolved dispatch

## See Also

- [nexus-rt docs](../../nexus-rt/docs/INDEX.md) — Dispatch framework that
  this runtime drives
- [BENCHMARKS.md](../BENCHMARKS.md) — Measured latencies and throughput
