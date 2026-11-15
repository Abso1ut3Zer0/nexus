# Onboarding to the Nexus Workspace

Welcome. This document is a 20-minute tour for a new engineer joining
the team. Read it start to finish before opening any code. When you
finish you should know what lives where, what to reach for when, and
how to validate a change.

---

## 1. Philosophy

Nexus is a set of low-latency primitives and runtime pieces for
systems that care about p99 tail latency. A few ideas run through
every crate:

- **Sans-IO.** Protocol state machines don't know about sockets.
  Parsers feed bytes in, frames out. IO lives at the edge.
- **Single-writer principle.** One thread owns mutable state. If a
  data structure has more than one writer, it pays for synchronization
  that a single-writer version wouldn't.
- **No allocation on the hot path.** Ever. Pre-allocate at startup,
  recycle via pools/slabs, reject rather than grow.
- **Bounded over unbounded.** An unbounded queue is a design smell —
  it means you haven't thought about backpressure.
- **Predictability over generality.** We don't build general-purpose
  abstractions. A conflation slot is not "a queue of size 1" — it has
  different semantics and we name it differently.
- **Honest constraints.** SPSC means SPSC. If you need more producers,
  pay for MPSC. Don't sneak extra producers into an SPSC API.

If a design decision doesn't line up with one of these, push back on
the design. These are load-bearing.

---

## 2. The Big Picture

There are three layers:

```
┌───────────────────────────────────────────────────┐
│  Application layer                                │
│  (strategies, market data gateways, order routers)│
└─────────────────┬─────────────────────────────────┘
                  │
┌─────────────────┴─────────────────────────────────┐
│  Runtime layer                                    │
│  nexus-rt        — sync dispatch (handlers, World)│
│  nexus-async-rt  — single-threaded async executor │
│  nexus-web       — sans-IO WebSocket / HTTP / TLS │
│  nexus-async-web — tokio adapter for nexus-net    │
└─────────────────┬─────────────────────────────────┘
                  │
┌─────────────────┴─────────────────────────────────┐
│  Primitive layer                                  │
│  Data movement:  queue, channel, slot, logbuf,    │
│                  notify, net                      │
│  Memory:         slab, pool, smartptr             │
│  Data:           collections, bits, ascii, id,    │
│                  decimal                          │
│  Stats/rate:     stats (+ subcrates), rate        │
│  Time:           timer                            │
└───────────────────────────────────────────────────┘
```

**Primitives don't depend on runtime.** The runtime crates consume
primitives. Applications sit on top. It is fine for an app to use
primitives directly and skip the runtime layer when that's simpler.

---

## 3. Crate Map

See the table in the workspace [`README.md`](../README.md) for the
canonical list. Short form, organized by category:

**Data movement**
- `nexus-queue` — SPSC / MPSC / SPMC ring buffers
- `nexus-channel` — blocking SPSC channel (parking, backoff)
- `nexus-slot` — SPSC conflation slot (latest value wins)
- `nexus-logbuf` — SPSC / MPSC byte ring buffer (variable length)
- `nexus-notify` — cross-thread event queue with dedup

**Memory management**
- `nexus-slab` — pre-allocated slab allocator (bounded + growable)
- `nexus-pool` — object pools (local + sync, RAII + manual)
- `nexus-smartptr` — inline/flexible smart pointers

**Data structures**
- `nexus-collections` — slab-backed List, Heap, RbTree, BTree
- `nexus-bits` / `nexus-bits-derive` — bit-packed newtypes
- `nexus-ascii` — fixed-capacity ASCII strings with precomputed hash
- `nexus-id` — Snowflake, UUID, ULID, MixedId, string IDs

**Numeric**
- `nexus-decimal` — fixed-point decimals (i32/i64/i128, const D)
- `nexus-stats` (+ `-core`, `-smoothing`, `-detection`,
  `-regression`, `-control`) — streaming statistics
- `nexus-rate` — GCRA, token bucket, sliding window rate limiters

**Networking**
- `nexus-net` — sans-IO WebSocket/HTTP/TLS
- `nexus-async-web` — tokio adapter for `nexus-net`

**Runtime**
- `nexus-rt` (+ `nexus-rt-derive`) — sync handler runtime (World,
  Handler, Pipeline, DAG, templates)
- `nexus-async-rt` — single-threaded async executor
- `nexus-timer` — timer wheel

---

## 4. "If I need X, look in Y"

Use this as a decision tree when you don't know where to start.

| Need | Reach for |
|------|-----------|
| Send a message SPSC between threads, lossless | `nexus-queue` SPSC, or `nexus-channel` if you want blocking |
| Send a message from many producers to one consumer | `nexus-queue` MPSC |
| Publish "latest value only" (conflation) | `nexus-slot` |
| Cross-thread wake with dedup (like mio `Events`) | `nexus-notify` |
| Move variable-length bytes off the hot path (archival) | `nexus-logbuf` |
| Allocate objects without touching `malloc` | `nexus-pool` (reusable, RAII) or `nexus-slab` (stable keys) |
| Intrusive data structure (list/heap/trees) with external storage | `nexus-collections` |
| Typed identifier (snowflake / UUIDv4 / UUIDv7 / ULID) | `nexus-id` |
| Fast symbol or small string with zero-cost hash | `nexus-ascii` |
| Pack fields into a wire-format integer | `nexus-bits` + `nexus-bits-derive` |
| Exact decimal arithmetic (prices, quantities) | `nexus-decimal` |
| Streaming mean / variance / percentile / smoother / detector | `nexus-stats` |
| Rate limit outbound requests | `nexus-rate` |
| Timer wheel (scheduled callbacks) | `nexus-timer` |
| Dispatch events to handlers with resource injection | `nexus-rt` |
| Single-threaded async executor | `nexus-async-rt` |
| Connect to an exchange WebSocket | `nexus-async-web` (tokio), or `nexus-net` (sans-IO) |

If you find yourself reaching outside the workspace for something
foundational, **stop and ask**. There's a good chance we either
already have it, decided not to build it, or it's on the roadmap.

---

## 5. Design Principles for New Code

When you write a new primitive or extend an existing one:

1. **Start with the data.** What is it? How many are there? How often
   does it change? Who reads, who writes? Draw the memory layout
   before writing types.
2. **Write the contract first.** A doc comment with
   `# Guarantees`, `# Panics`, and `# Examples` — reviewed before
   implementation. If the contract is awkward, the API is wrong.
3. **Pre-allocate.** No `Vec::push` on the hot path. If a buffer
   grows, that growth is a benchmark case, not a background fact.
4. **Let the caller own the failure policy.** Return `Result`.
   Callers decide whether to `.unwrap()`, `.ok()`, or match.
5. **Single-writer by default.** If you need multiple writers, the
   type name says MPSC/MPMC explicitly.
6. **Measure before optimizing.** Read [benchmarking.md](./benchmarking.md)
   first. Your intuition about the bottleneck is probably wrong.
7. **`cargo clippy --workspace -- -D warnings` is the merge bar.**
   Run it before every commit.
8. **Unsafe needs a `// SAFETY:` comment** that justifies every
   invariant. If you can't write the comment, the code is wrong.
9. **Tests ship with the code.** Unit tests in-file, integration in
   `tests/`, miri coverage for unsafe, criterion benches for hot
   paths.
10. **Documentation is a deliverable.** An unshipped doc is a
    shipped bug. If you add a subsystem, add the doc in the same PR.

---

## 6. Running Tests

From the workspace root:

```bash
# Build everything
cargo build --workspace

# Run every test
cargo test --workspace

# Lint — must be clean
cargo clippy --workspace -- -D warnings

# Format check
cargo fmt --check

# Benchmarks (see benchmarking.md for controlled conditions)
cargo bench --workspace
```

For crates with `unsafe`, run miri:

```bash
MIRIFLAGS="-Zmiri-ignore-leaks" \
  cargo +nightly miri test -p nexus-slab --test miri_tests
```

`-Zmiri-ignore-leaks` is required because our slab backing memory
uses `Box::leak` to get stable addresses.

---

## 7. "Is this already built?"

Before you write something new, check:

1. **The crate table in `README.md`.** Quick scan of names.
2. **The crate's `docs/` directory.** Many crates have an `INDEX.md`.
3. **`cargo doc --workspace --no-deps --open`** — rustdoc is the
   source of truth for the API surface.
4. **`CONTRIBUTING.md`** — the philosophy and the standards a change is
   reviewed against.
5. **The issue tracker** — open issues carry the design discussion;
   search it before duplicating something already decided.

---

## 8. Where Architectural Decisions Live

Different kinds of decisions live in different places. When you need
to understand **why**, look here before guessing:

- **`CONTRIBUTING.md`** at the workspace root — philosophy, forbidden
  patterns, benchmarking standards.
- **The issue tracker** — future work and the reasoning behind it; there
  is no separate roadmap document.
- **Per-crate `ARCHITECTURE.md`** — the "why" for a crate's internal
  design (e.g. `nexus-rt/docs/ARCHITECTURE.md`).
- **`nexus-rt/docs/`** — extensive — this is the largest docs set.
  Start at `INDEX.md` and follow the breadcrumbs.
- **`nexus-stats/docs/reference/performance.md`** — cycle counts and
  methodology for stats.
- **`nexus-async-rt/BENCHMARKS.md`** — runtime perf history.

---

## 9. Next Steps

- Read [`benchmarking.md`](./benchmarking.md) before you run a bench.
- Pick a cookbook that matches what you're about to build:
  - Market data in? → [cookbook-market-data-gateway.md](./cookbook-market-data-gateway.md)
  - Writing a strategy? → [cookbook-strategy-handler.md](./cookbook-strategy-handler.md)
  - Monitoring? → [cookbook-latency-monitoring.md](./cookbook-latency-monitoring.md)
  - Exchange connectivity? → [cookbook-exchange-connection.md](./cookbook-exchange-connection.md)
- Open the crate `docs/` for whatever you're touching first.
- When in doubt: write the contract, review it, *then* implement.
