# Nexus

Low-latency primitives for building high-performance systems.

## Philosophy

These crates are born from years of building trading infrastructure, where certain patterns become clear: most systems don't need unbounded queues, dynamic allocation, or multi-producer flexibility. They need **predictable, bounded, specialized primitives** that do one thing well and never surprise you at runtime.

The core philosophy is **predictability over generality**:

- **SPSC over MPMC** — When you have one producer and one consumer, don't pay for synchronization you don't need
- **Pre-allocation over dynamic growth** — Allocate at startup, never on the hot path
- **Bounded over unbounded** — Know your capacity, reject rather than allocate
- **Specialization over abstraction** — A conflation slot isn't a queue of size 1, it's a different thing entirely

The goal isn't "fastest in microbenchmarks." It's **consistent, low-latency behavior** under real workloads — minimizing tail latency, avoiding syscalls, eliminating allocation jitter.

Each crate is small, focused, and honest about its constraints. No kitchen sinks.

## Crates

### Communication

| Crate | Description |
|-------|-------------|
| [**nexus-queue**](./nexus-queue) | Lock-free SPSC ring buffer with per-slot lap counters. Sub-microsecond latency for bounded message passing. |
| [**nexus-channel**](./nexus-channel) | Blocking SPSC channel built on nexus-queue. Adds backpressure with optimized parking that minimizes syscalls. |
| [**nexus-slot**](./nexus-slot) | Single-value conflation slot. Writer always overwrites, reader gets latest value exactly once. For "latest wins" patterns like market data snapshots. |

### Storage

| Crate | Description |
|-------|-------------|
| [**nexus-slab**](./nexus-slab) | Pre-allocated slab with page-aligned memory, prefaulting, and optional mlock. O(1) insert/remove with stable keys. |

### Planned

| Crate | Description | Status |
|-------|-------------|--------|
| **nexus-hash** | Integer-optimized hashers for structured keys (packed IDs, snowflakes). Better distribution than identity hashing without full cryptographic overhead. | Planned |
| **nexus-pool** | Object pool with borrow/return semantics over nexus-slab. Acquire returns a guard, drop returns to pool. | Planned |
| **nexus-id** | Snowflake-style ID generator with const generic bit layout. Lock-free, monotonic, embeds timestamp and worker ID. | Planned |
| **nexus-ascii** | Fixed-capacity ASCII strings. Zero UTF-8 overhead for symbols, order IDs, and protocol fields that are always ASCII. | Planned |
| **nexus-collections** | Index-linked data structures: list, skip list, heap. Base types take external storage (slab-backed, composable). `Owned*` variants for self-contained use. | Planned |

## Design Principles

### No allocation on the hot path

Every crate that manages memory supports pre-allocation. You pay the cost at startup, not when processing the millionth message.

### Honest constraints

SPSC means SPSC. Don't sneak in an extra producer and expect it to work. The constraints enable the performance.

### Benchmark what matters

Synthetic throughput is easy to game. We optimize for realistic workloads: ping-pong latency, p99/p999 tail latency, jitter under load.

### Minimal dependencies

These are foundational crates. Dependency trees are kept small and intentional.

## Platform Support

- **Linux** — Primary target, fully supported
- **macOS** — Supported
- **Windows** — Experimental where noted, typically behind feature flags

## Contributing

Please read [CONTRIBUTING.md](./CONTRIBUTING.md) before submitting changes.

The short version: we build specialized primitives, not general-purpose ones. Different constraints mean different problems, and different problems deserve different solutions. If you're proposing a feature, be ready to justify why it belongs in a tuned, minimal implementation.

We also have specific benchmarking standards — cycles not time, turbo boost disabled, cores pinned, jitter eliminated. Details in the contributing guide.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT) at your option.
