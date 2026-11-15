# Performance

The async adapter adds almost nothing on top of the sans-IO codec.
The numbers in [nexus-web/docs/performance.md](../../nexus-web/docs/performance.md)
apply directly for parse / encode / mask / UTF-8 validation — only
the read/write boundary is different.

Absolute values depend on CPU and configuration. Ratios against
`tokio-tungstenite` are stable across machines we've tested.

## WebSocket vs `tokio-tungstenite`

End-to-end round-trip over loopback TLS, measured on a single
`current_thread` runtime with a `LocalSet`:

| Workload | tokio-tungstenite | nexus-async-web | Ratio |
|----------|-------------------|-----------------|-------|
| 40B binary echo (TLS) | 1.0x baseline | 3.5x faster | **3.5x** |
| 77B JSON quote tick | 1.0x baseline | 1.7x faster | **1.7x** |

The difference has two sources:

1. **Zero-copy parsing.** tokio-tungstenite allocates a `Vec<u8>`
   per frame; nexus-async-web returns `Message::Text(&str)` borrowing
   into the internal `ReadBuf`. At 40–77 bytes, the allocator is a
   large fraction of total cost. As payloads grow, the ratio narrows
   because the per-byte constant factor (TLS record decrypt,
   kernel read) starts to dominate.
2. **Direct `recv()`/`send_text()` path.** The default
   `Stream`/`Sink` adapter path goes through `OwnedMessage` (which
   allocates). Our fast path does not.

If you use `futures::StreamExt::next()` on `WsStream`, you're
implicitly on the slower path because each yielded item is an
owned message. For latency-critical code, call `ws.recv().await`
directly.

## REST

Async REST numbers track nexus-net sync REST closely:

| Workload | reqwest | nexus-async-web | Ratio |
|----------|---------|-----------------|-------|
| Loopback GET (mock server) | 1.0x | ~3x faster | **3x** |

`AtomicClientPool` adds a negligible cost per acquire vs
`ClientPool` on a single thread. If you need cross-thread
sharing, `AtomicClientPool` inside a `Mutex` is still faster
than round-tripping requests through a channel to a single-thread
worker.

## `current_thread` + `LocalSet` is the fast path

All benchmarks use:

```rust
tokio::runtime::Builder::new_current_thread()
    .enable_all()
    .build()?
    .block_on(async move {
        let local = tokio::task::LocalSet::new();
        local.run_until(async move { /* ... */ }).await
    })
```

Why this configuration wins for trading hot paths:

- **No work-stealing.** Multi-thread tokio moves futures between
  workers to balance load. That's the right choice for a web
  server; it's wrong for a latency-sensitive feed where every
  cross-core trip costs cache misses.
- **No `Send` bounds.** `spawn_local` lets you hold
  `Rc<RefCell<_>>`, `Cell<_>`, and other non-Send types without
  synthetic wrappers.
- **Predictable ordering.** Tasks polled in spawn order give you
  the deterministic behavior you need for replay testing.

Pin the runtime to a physical core (not a hyperthread sibling)
for production:

```rust
let core = core_affinity::CoreId { id: 2 };
core_affinity::set_for_current(core);
```

## Cost of the async wrapper

On top of the bare nexus-net codec (which runs ~38 cycles to parse
a 128B unmasked text frame), the tokio backend adds:

- Task poll cost: ~30-60 cycles
- Waker bookkeeping: ~20 cycles
- `AsyncRead::poll_read` call chain: ~20 cycles

Total overhead ~80 cycles per frame. At ~100M cycles/sec on a
4GHz core, that's ~25 ns — nowhere near the dominant cost
(kernel syscall or TLS record decrypt).

## Bench programs

The crate ships runnable benchmarks under `examples/`:

- `bench_pool_throughput` — REST pool throughput
- `perf_async_ws_nexus` / `perf_async_ws` — WebSocket latency on
  nexus and tokio backends
- `perf_ws_cycles_nexus` / `perf_ws_cycles_tokio` — cycle-level
  WebSocket head-to-head

Run with:

```bash
cargo run --release --example perf_ws_cycles_nexus
```

## Tuning knobs

The three recv-path knobs (`buffer_capacity`, `compact_at`,
`max_read_size`) are documented in [tuning.md](./tuning.md).

## See also

- [tuning.md](./tuning.md) — recv path knobs
- [nexus-web/docs/performance.md](../../nexus-web/docs/performance.md) — codec-level numbers
