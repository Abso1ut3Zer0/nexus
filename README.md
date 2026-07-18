# Nexus

Low-latency primitives and runtime for building high-performance systems.

## Philosophy

These crates are born from years of building trading infrastructure, where
certain patterns become clear: most systems don't need unbounded queues,
dynamic allocation, or multi-producer flexibility. They need **predictable,
bounded, specialized primitives** that do one thing well and never surprise
you at runtime.

The core philosophy is **predictability over generality**:

- **SPSC over MPMC** — When you have one producer and one consumer, don't pay for synchronization you don't need
- **Pre-allocation over dynamic growth** — Allocate at startup, never on the hot path
- **Bounded over unbounded** — Know your capacity, reject rather than allocate
- **Specialization over abstraction** — A conflation slot isn't a queue of size 1, it's a different thing entirely

The goal isn't "fastest in microbenchmarks." It's **consistent, low-latency
behavior** under real workloads — minimizing tail latency, avoiding syscalls,
eliminating allocation jitter.

Each crate is small, focused, and honest about its constraints. No kitchen sinks.

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                        *Runtime*                        │
│             rt · async-rt* · timer · + tokio            │
├─────────────────────────────────────────────────────────┤
│                     *FIX Protocol*                      │
│       fix-codec · fix-engine · async-fix-engine         │
├─────────────────────────────────────────────────────────┤
│                       *Analytics*                       │
│                   stats-* · inference                   │
├─────────────────────────────────────────────────────────┤
│                       *Networking*                      │
│                     net · async-net                     │
├─────────────────────────────────────────────────────────┤
│                      *Concurrency*                      │
│         queue · channel · slot · notify · logbuf        │
├─────────────────────────────────────────────────────────┤
│                 *Collections & Flow Control*            │
│                    collections · rate                   │
├─────────────────────────────────────────────────────────┤
│                        *Storage*                        │
│             slab · pool · smartptr · journal            │
├─────────────────────────────────────────────────────────┤
│                         *Types*                         │
│               bits · ascii · id · decimal               │
└─────────────────────────────────────────────────────────┘

* async-rt is experimental — use tokio for production async workloads
```

## Crates

### Types & Encoding

| Crate | Description |
|-------|-------------|
| [**nexus-bits**](./nexus-bits) | Bit-packed integer newtypes via derive macros. Structs, tagged enums, `IntEnum` for discriminants. Zero-cost `#[repr(transparent)]` with compile-time validation. |
| [**nexus-ascii**](./nexus-ascii) | Fixed-capacity ASCII strings. Stack-allocated, immutable, with precomputed 48-bit XXH3 hash. Identity-hashable via `nohash` feature for zero-cost lookups. |
| [**nexus-id**](./nexus-id) | High-performance ID generators: Snowflake, UUID v4/v7, ULID. SIMD-accelerated hex encode/decode. Fibonacci mixing for identity hashers. |
| [**nexus-decimal**](./nexus-decimal) | Fixed-point decimal arithmetic with compile-time precision. `Decimal<i64, 8>` for prices, `Decimal<i128, 12>` for DeFi. Const fn, `no_std`, zero allocation. Financial methods: midpoint, tick rounding, basis points. Chunked magic division avoids `__divti3`. |

### Storage & Allocation

| Crate | Description |
|-------|-------------|
| [**nexus-slab**](./nexus-slab) | Manual memory management with SLUB-style slab allocation. `bounded::Slab` (fixed capacity) and `unbounded::Slab` (growable via chunks). `rc` feature adds `RcSlot` with borrow guards for shared ownership. 1 cycle alloc, sub-cycle free ([benchmarks](./nexus-slab/BENCHMARKS.md)). |
| [**nexus-pool**](./nexus-pool) | Object pools with RAII guards. Single-threaded `BoundedPool` and thread-safe `sync::Pool` (one acquirer, any returner). |
| [**nexus-smartptr**](./nexus-smartptr) | Inline and flexible smart pointers for type-erased storage. `FlatBox` (fixed inline), `FlexBox` (inline or heap). Avoids boxing for small handler types. |
| [**nexus-journal**](./nexus-journal) | Append-only and bounded-rotation mmap'd journals for trading systems. Segment-based, fsync-free on the write path, crash-safe. Used by `nexus-fix-engine` for outbound message persistence and replay. |

### Collections

| Crate | Description |
|-------|-------------|
| [**nexus-collections**](./nexus-collections) | Slab-backed intrusive collections. O(1) linked lists, O(log n) heaps, red-black trees, B-trees. External allocation via `nexus-slab` — user owns the slab, collection wires pointers. 2-3 cycle list operations, 15 cycle tree lookups ([benchmarks](./nexus-collections/BENCHMARKS.md)). |

### Flow Control

| Crate | Description |
|-------|-------------|
| [**nexus-rate**](./nexus-rate) | Rate limiting. GCRA, token bucket, sliding window counter. Single-threaded and thread-safe variants. Weighted requests. ~2-4 cycle hot path ([benchmarks](./nexus-rate/BENCHMARKS.md)). |

### Concurrency & Communication

| Crate | Description |
|-------|-------------|
| [**nexus-queue**](./nexus-queue) | Lock-free SPSC, MPSC, and SPMC ring buffers with per-slot lap counters. Index-based (NUMA-friendly) and slot-based (shared-L3 friendly) implementations. |
| [**nexus-channel**](./nexus-channel) | Blocking SPSC channel built on nexus-queue. Three-phase backoff (spin → yield → park) minimizes syscalls under load. |
| [**nexus-slot**](./nexus-slot) | Single-value conflation slot. Writer always overwrites, reader gets latest value exactly once. For "latest wins" patterns like market data snapshots. |
| [**nexus-notify**](./nexus-notify) | Cross-thread event queue with conflation and FIFO delivery. Non-blocking `event_queue` and blocking `event_channel`. Dedup flags + MPSC ring buffer — O(limit) poll, ~5 cycles/token ([benchmarks](./nexus-notify/BENCHMARKS.md)). |
| [**nexus-logbuf**](./nexus-logbuf) | Bounded SPSC and MPSC byte ring buffers. Claim-based API for variable-length messages. The hot-path primitive for getting data off the event loop without syscalls. |

### Networking

| Crate | Description |
|-------|-------------|
| [**nexus-net**](./nexus-net) | Low-latency networking primitives: buffers (`ReadBuf`, `WriteBuf`), TLS codec (rustls), wire abstractions (`WireStream`, `ParserSink`), `MaybeTls` transport. Foundation for nexus-web and nexus-async-web. |
| [**nexus-net-tokio**](./nexus-net-tokio) | Tokio async wire transport for nexus-net: `AsyncReadAdapter<S>` (wraps `tokio::io::AsyncRead + AsyncWrite` as a `WireStream`) and async `MaybeTls` (transparent plaintext/TLS). Keeps nexus-net runtime-free; shared by nexus-async-web and nexus-async-fix-engine. |
| [**nexus-web**](./nexus-web) | Sans-IO WebSocket (RFC 6455), HTTP/1.1, and REST primitives. Zero-copy, SIMD-accelerated. 3x faster than tungstenite, 3x faster than reqwest. Typestate request builder, chunked transfer encoding, connection poisoning. 517/517 Autobahn + 16/16 httpbin conformance. |
| [**nexus-async-web**](./nexus-async-web) | Async adapters for nexus-web. Tokio-compatible. WebSocket `WsReader`/`WsWriter`, HTTP `HttpConnection<S>`, and `ClientPool`/`AtomicClientPool` with self-healing reconnect. `try_acquire` (fast path) and `acquire` (patient path with backoff). 3.5x faster than tokio-tungstenite ([benchmarks](./nexus-async-web/BENCHMARKS.md)). |

### FIX Protocol

| Crate | Description |
|-------|-------------|
| [**nexus-fix-codec**](./nexus-fix-codec) | Zero-copy FIX 4.x read/write primitives. SIMD-accelerated field scanning and checksum validation. `FrameFormatter` for outbound encoding, `FieldReader` and `validate_checksum` for inbound parsing. Dictionary-independent at the framing layer. |
| [**nexus-fix-engine**](./nexus-fix-engine) | Sans-IO FIX 4.4 session layer. Handles Logon/Logout, heartbeat supervision, sequence number management, gap detection, and durable recovery via `FixJournal`. `FixConnection` drives framing and session dispatch with no runtime or async dependency. |
| [**nexus-fix-codegen**](./nexus-fix-codegen) | Dictionary-driven code generator for `nexus-fix-codec`. Produces typed decode/encode implementations from FIX XML spec files. |
| [**nexus-async-fix-engine**](./nexus-async-fix-engine) | Tokio async adapter for `nexus-fix-engine`. Wraps `FixConnection` in a task-friendly interface without altering session semantics. |

### Platform

| Crate | Description |
|-------|-------------|
| [**nexus-platform**](./nexus-platform) | Platform-specific OS primitives behind a portable Rust API. File locking and memory-mapped I/O with consistent semantics across Linux, macOS, and Windows. |
| [**nexus-shm**](./nexus-shm) | Shared-memory IPC primitives for multi-process trading systems. Zero-copy data transfer across process boundaries. |

### Runtime

| Crate | Description |
|-------|-------------|
| [**nexus-rt**](./nexus-rt) | Event-driven runtime. World/ECS resource model, handler dispatch, pipelines, DAGs, driver system, clock. No async/await — explicit poll loops with monomorphized zero-cost dispatch. |
| [**nexus-async-rt**](./nexus-async-rt) | **Experimental.** Single-threaded async executor. Slab-allocated tasks, zero-allocation waker vtable, mio-backed IO driver, timer wheel, signal handling. Not under active development — use tokio for production async workloads. |
| [**nexus-timer**](./nexus-timer) | Hierarchical timer wheel with O(1) insert and cancel. No-cascade design inspired by the Linux kernel. Slab-backed, zero allocation after init. |

### Streaming Statistics

Fixed-memory, zero-allocation streaming analytics. All types are O(1) per
update, designed for hot-path integration. The `nexus-stats` umbrella crate
re-exports everything; the subcrates allow fine-grained dependency control.

| Crate | Description |
|-------|-------------|
| [**nexus-stats**](./nexus-stats) | Umbrella crate — re-exports all subcrates below under a unified namespace. |
| [**nexus-stats-core**](./nexus-stats-core) | Foundation types and core algorithms. Welford moments, EMA/AsymEMA, covariance, drawdown, min/max, percentile (P²), normalization (ZScore, MinMax, Quantile), microstructure (Amihud, KyleLambda, RollSpread, Bipower, TwoScaleRv), monitoring (CoDel, Jitter, Liveness, EventRate, Hawkes intensity). |
| [**nexus-stats-smoothing**](./nexus-stats-smoothing) | Advanced smoothing. KAMA, Holt double exponential, Spring (critically damped), Kalman1d, Hampel filter, HuberEMA, ConditionalEMA, WindowedMedian. |
| [**nexus-stats-detection**](./nexus-stats-detection) | Change detection and signal analysis. CUSUM, MOSUM, BOCPD, Shiryaev-Roberts, ADWIN, Page-Hinkley, distribution shift/drift, adaptive threshold, trend alert, entropy, transfer entropy, predictive information bound, autocorrelation, cross-correlation. |
| [**nexus-stats-regression**](./nexus-stats-regression) | Online regression, learning, and estimation. Linear/polynomial/power/log/exponential regression (OLS + EW), Huber-robust regression, RLS/LMS/NLMS adaptive filters, logistic regression, online K-means, Kalman 2d/3d, online gradient descent, AdaGrad, Adam. |
| [**nexus-stats-control**](./nexus-stats-control) | Control and frequency primitives. Dead band, hysteresis, debounce, level crossing, peak detector, bool window, TopK, proportion tracking, decay accumulator. |

### Inference

Real-time CPU inference for small, pre-trained models. Train in Python
(PyTorch, LightGBM), load once via `from_parts` or SafeTensors, predict
millions of times. Sub-microsecond latency, zero allocation after
construction, SIMD-accelerated (SSE2/AVX2/AVX-512).

| Crate | Description |
|-------|-------------|
| [**nexus-inference**](./nexus-inference) | 12 model types across stateless and stateful inference. **Stateless:** GBDT (branchless traversal, NaN-aware, LightGBM-compatible), MLP (SIMD-tiled matmul, LayerNorm, 8 activations), LUT (O(1) lookup table), BNN (binary neural network, XNOR+popcount), QuantizedMLP (i8 weights, i32 accumulation). **Stateful:** LSTM, GRU, stacked LSTM/GRU, linear state-space model (S4/S4D), causal 1D convolution, temporal convolutional network (TCN). Stateless models use interior mutability (`&self`) for zero-contention sharing; stateful models carry hidden state between calls. SafeTensors and LightGBM JSON loaders. |

## Design Principles

### No allocation on the hot path

Every crate that manages memory supports pre-allocation. You pay the cost
at startup, not when processing the millionth message.

### Honest constraints

SPSC means SPSC. Don't sneak in an extra producer and expect it to work.
The constraints enable the performance.

### Benchmark what matters

Synthetic throughput is easy to game. We optimize for realistic workloads:
ping-pong latency, p99/p999 tail latency, jitter under load. See
individual crate `BENCHMARKS.md` files for methodology and results.

### Minimal dependencies

These are foundational crates. Dependency trees are kept small and intentional.

## Benchmark Conditions

Performance numbers are measured on an Intel Core Ultra 7 165U (12C/14T,
12MB L3) running Arch Linux with `rustc 1.94.0`. Comparative numbers
(speedup ratios) are measured with turbo boost disabled and cores pinned
via `taskset`; finalized cycle counts are with turbo boost enabled. Results
vary by hardware — each crate's `BENCHMARKS.md` records the specific
machine, toolchain, comparison-crate versions, and reproduction steps.

## Platform Support

- **Linux** — Primary target, fully supported
- **macOS** — Supported
- **Windows** — Experimental where noted, typically behind feature flags

## Contributing

Please read [CONTRIBUTING.md](./CONTRIBUTING.md) before submitting changes.

The short version: we build specialized primitives, not general-purpose ones.
Different constraints mean different problems, and different problems deserve
different solutions. If you're proposing a feature, be ready to justify why
it belongs in a tuned, minimal implementation.

We also have specific benchmarking standards — cycles not time, turbo boost
disabled, cores pinned, jitter eliminated. Details in the contributing guide.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT) at your option.
