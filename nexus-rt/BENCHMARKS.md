# nexus-rt Performance

Measured on Linux, single core (taskset -c 0), turbo boost disabled.
Criterion benchmarks in `benches/dispatch.rs`, rdtsc benchmarks in `examples/perf_*.rs`.

## Handler Dispatch

Pre-resolved `ResourceId` — single pointer deref per resource, no HashMap lookup.

| Operation | Latency | Cycles | Notes |
|-----------|---------|--------|-------|
| Handler 0 params | 222 ps | <1 | Closure, no resource access |
| Handler 1 param (Res) | 359 ps | ~1.3 | One shared read |
| Handler 2 params (Res + ResMut) | 477 ps | ~1.7 | Read + write |

## Callback Dispatch (Context-Owning)

Same as Handler but with per-instance `&mut C` context threading.

| Operation | Latency | Cycles | Notes |
|-----------|---------|--------|-------|
| Callback 0 params | 472 ps | ~1.7 | Context mutation only |
| Callback 2 params | 712 ps | ~2.5 | Context + Res + ResMut |

## Pipeline Dispatch

Monomorphized chain — all steps inlined, zero vtable calls.
Codegen verified via `cargo asm` (see `examples/perf_pipeline.rs`).

| Operation | Latency | Cycles | Notes |
|-----------|---------|--------|-------|
| 3-stage bare | 668 ps | ~2.3 | Closures, no resource access |
| 3-stage world access | 512 ps | ~1.8 | Named fns with Res<T> params |
| 5-stage + guard (Option flow) | 5.16 ns | ~18 | Guard branch + 4 Option maps |

The 3→5 stage jump is due to Option flow: each `.map()` after the
guard does `match Some(val) => Some(f(val)), None => None`. With
`black_box`, the compiler cannot prove the None path is dead code.
Assembly inspection confirms the codegen is optimal — no unnecessary
wrapping/unwrapping.

## Runtime Keyed Dispatch

Flat-array dispatch tables (`#[derive(Dispatchable)]` + `.dispatch_variant` /
`.dispatch_on` / `.dispatch_map`), benchmarked against the compile-time
`select!` jump table and a hand-rolled `FxHashMap`. Cycles per dispatch, 8 keys.
Every arm is a **distinct function** doing the same shape of minimal work, and
keys arrive in a **precomputed random order**, so the indirect-call target
varies per dispatch (a realistic mispredict rate, not a perfectly-predicted
loop). See `examples/perf_dispatch.rs`.

| Dispatch | p50 | p90 | p99 | p999 | p9999 |
|---|---|---|---|---|---|
| `select!` (compile-time, inlined) | 28 | 29 | ~32 | ~78 | ~110 |
| `.dispatch_variant` (ordinal array, typed) | 31 | 33 | ~37 | ~85 | ~130 |
| `.dispatch_on` (ordinal array, whole value) | 38 | 40 | ~45 | ~93 | ~125 |
| `.dispatch_on` (tuple-product key) | 38 | 40 | ~44 | ~97 | ~130 |
| raw `FxHashMap` (hand-rolled) | 45 | 48 | ~52 | ~106 | ~145 |
| `.dispatch_map` (FxHashMap combinator) | 50 | 53 | ~57 | ~110 | ~150 |

**Caveat:** unlike the other tables here, these were taken with **turbo boost
ON** (could not be disabled on the measurement box), best of 3 runs, timed with
`rdtsc` (raw TSC ticks) and reported as percentiles of per-batch means.
**p50/p90 are the reliable per-op signal; p99+ is system noise** (scheduler tick,
IRQ, throttling), not the mechanism: beyond p99 every method including `select!`
converges to the same noisy ~80-160-cycle band. Re-run `examples/perf_dispatch.rs`
under `taskset -c 0` with turbo disabled for publication-grade numbers.

Takeaways: `.dispatch_variant` costs a few cycles over inlined `select!` (about
+3 to +6, ~10-20% at p50): a runtime-composable typed table, with `select!`
keeping the edge by inlining the arm. The ordinal tables beat the hashmaps at
this size (`.dispatch_variant` 31 / `.dispatch_on` 38 vs `FxHashMap` 45 /
`.dispatch_map` 50 at p50); this is measured only at N=8, and no scaling claim
beyond it is measured. `.dispatch_map` is the slowest (hash + probe), so prefer
`.dispatch_on` when the key is a `Dispatchable` enum. Full discussion in
[docs/dispatch.md](docs/dispatch.md#performance).

## System Dispatch

Boolean-returning reconciliation systems for scheduler DAG propagation.

| Operation | Latency | Cycles | Notes |
|-----------|---------|--------|-------|
| System 2 params + bool | 738 ps | ~2.6 | Res + ResMut + bool return |

## Reactor Dispatch

Interest-based notification with dedup. Cost includes: mark fan-out →
LocalNotify bitset dedup → poll → move-out → vtable call → Param
fetch → move-back → deferred removal check.

| Operation | Total | Per-reactor | Cycles/reactor |
|-----------|-------|-------------|----------------|
| 1 reactor (noop) | 24.4 ns | 24.4 ns | ~85 |
| 10 reactors (noop) | 72.0 ns | 7.2 ns | ~25 |
| 50 reactors (noop) | 269 ns | 5.4 ns | ~19 |
| 10 reactors (1 Res) | 75.9 ns | 7.6 ns | ~27 |

Per-reactor cost amortizes: 85 cycles for 1 (dominated by mark/poll
overhead), down to 19 cycles at 50 reactors. Adding `Res<T>` costs
~2 extra cycles per reactor (pre-resolved access).

## World Resource Access (Cold Path)

HashMap lookup by `TypeId`. Use pre-resolved `ResourceId` on the hot
path instead — that's what Handler/Pipeline/Reactor dispatch does.

| Operation | Latency | Cycles | Notes |
|-----------|---------|--------|-------|
| resource::\<T\>() | 1.31 ns | ~4.6 | TypeId HashMap lookup |
| resource_mut::\<T\>() | 1.18 ns | ~4.1 | Same + exclusive access |

## Template Stamping

Resolve params once, stamp handlers via memcpy of pre-resolved state.

| Operation | Latency | Cycles | Notes |
|-----------|---------|--------|-------|
| stamp + dispatch | 1.33 ns | ~4.7 | memcpy state + handler run |

## LocalNotify (nexus-notify)

Single-threaded dedup notification. See `examples/perf_local_notify.rs`.

| Operation | Per-token | Notes |
|-----------|-----------|-------|
| mark + poll (1 token) | 14 cy | Overhead floor |
| mark + poll (10 tokens) | 5.7 cy | Amortized |
| mark + poll (200 tokens) | 5.2 cy | Steady state |
| Dedup (100x same token) | 1.3 cy/mark | Bit test + no-op |
| Bitset scaling (5 of 4096) | 37 cy | Constant — independent of total |

## Running Benchmarks

```bash
# Criterion (statistical, automated regression detection)
taskset -c 0 cargo bench -p nexus-rt --bench dispatch

# With reactors
taskset -c 0 cargo bench -p nexus-rt --bench dispatch --all-features

# rdtsc cycle-level (manual, finer granularity)
taskset -c 0 cargo run --release -p nexus-rt --example perf_pipeline
taskset -c 0 cargo run --release -p nexus-rt --example perf_dispatch
taskset -c 0 cargo run --release -p nexus-rt --example perf_fetch
taskset -c 0 cargo run --release -p nexus-rt --features reactors --example perf_reactors
taskset -c 0 cargo run --release -p nexus-notify --example perf_local_notify

# Disable turbo boost for stable measurements
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
# Re-enable after
echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```
