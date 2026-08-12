# Timer-wheel walk locality & cache behavior (audit for #669)

## TL;DR

The poll / rebalance entry-walk is **compute-bound and cache-resident for
realistic workloads**. Cancel-churn fragments the slab free list, but that only
degrades the walk once the **live working set exceeds L3** (~200k timers on this
machine). At the sizes that ship (≤ 50k) it is a non-issue — measured IPC ~3
with ≈ 0 cache misses per poll. **No slab-layout change is justified.**

## The question (#669)

An earlier measurement on the pre-rebalance wheel reported ~45 ns per entry on a
poll that scanned a slot's entries, and hypothesized slab **free-list
fragmentation** under cancel churn. This audit answers, with `perf` counters:

- Is the per-entry walk **cache-miss-bound** or compute-bound?
- Does cancel **churn** fragment the slab enough to matter, and at what scale?

## Method

Two benches, both counting hardware events with `perf_event` (not `rdtsc`), so we
see cache misses, not just cycles. Pinned to a **P-core** (`taskset -c 0`) — the
CPU is hybrid, so counters must read the `cpu_core` PMU.

- **`benches/perf_669_walk.rs`** — isolates the `rebalance` walk: counters wrap
  *only* the `rebalance` call, so setup (and, in mode `b`, the fragmenting churn)
  is not counted. Two layouts, swept 10k → 1M live entries:
  - **mode `a` (contiguous):** N entries scheduled into a fresh slab → contiguous,
    insertion-ordered slots.
  - **mode `b` (scattered):** the free list is first fragmented by scheduling and
    cancelling batches in shuffled order, so the live entries land in scattered
    slots (worst case — uniform scatter).
- **`benches/perf_server_scenarios.rs` → `realistic_cache`** — the realistic
  server driver (spread deadlines, cancel-heavy one-shots + periodic events,
  FIFO-ish cancel), with counters wrapping the `poll_and_rebalance` call across
  the measured window. Reports IPC and misses/poll at 2k / 15k / 50k.

### Environment

- Intel Core Ultra 7 165U (Meteor Lake, hybrid). P-cores 0–3 up to 4.9 GHz.
- L1d 32 KiB/core, L2 ~2 MiB/P-core module, **L3 12 MiB shared**.
- `WheelEntry` ≈ 60 B ⇒ L3 holds ~200k entries (matches the measured crossover).
- `perf_event_paranoid = 2` (user-space counters, no sudo).

## Results

### Isolated `rebalance` walk — contiguous vs worst-case scatter

Wall-clock per entry, single unbounded `rebalance` of the whole population:

| live entries | contiguous (a) | scattered (b) | penalty | b IPC |
|---|---|---|---|---|
| 10k  | 5.6 ns | 5.7 ns | ~1×  | 3.6 |
| 50k  | 5.6 ns | 9.2 ns | 1.6× | 3.2 |
| 200k | 7 ns   | 25 ns  | 3.6× | 1.0 |
| 500k | 8 ns   | 73 ns  | 9×   | 0.32 |
| 1M   | 8.5 ns | 91 ns  | 11×  | 0.29 |

Contiguous stays ~6–9 ns/entry all the way to 1M — the hardware prefetcher hides
the misses on sequential access (IPC ~3.5 even at 1 miss/entry). Scattered is
identical up to 50k, then falls off a cliff as the working set spills past L3.

### Realistic server workload — poll cache behavior

| env | IPC | miss/poll | miss/fired |
|---|---|---|---|
| edge (2k, 90% cxl)    | 2.3 | ~0.006 | ~0.02 |
| app (15k, 75% cxl)    | 3.0 | ~0.05  | ~0.02 |
| gateway (50k, 95% cxl)| 2.4 | ~0.05  | ~0.17 |

Realistic workloads sit next to the *contiguous* column: **IPC ~2.3–3.0, ≈ 0
cache misses per poll.** Gateway (50k) shows the first hint of L3 pressure
(0.17 miss/fired) but is still nowhere near the 1+/entry of the memory-bound
regime.

## Interpretation

- **The penalty tracks which cache level the working set lives in, not the
  degree of scatter.** Below L3 (~200k entries here), even uniform worst-case
  scatter is an L3 hit → ~6–9 ns/entry. Above L3, scattered access becomes a
  dependent-load chain to DRAM → ~90 ns/entry, IPC collapses to ~0.3. Software
  prefetch can't help a dependent pointer chase.
- **The move is a DLL splice, not a queue push.** Rebalancing an entry unlinks it
  from the source slot (writes `prev.next`, `next.prev`) and links it into the
  target slot (writes `tail.next`) — ~4 different nodes touched per entry. In the
  DRAM regime that's ~3–4 back-to-back misses, which is the 91 ns.
- **Realistic workloads stay compact.** The slab's LIFO free list reuses the
  hottest recently-freed slot, and real cancel patterns are FIFO-ish
  (completions roughly track arrivals), so the live set doesn't scatter the way
  the synthetic uniform-shuffle does.

## Conclusions & decisions

- **No layout work is justified** for the sizes that ship. Realistic polls are
  compute-bound and cache-resident.
- **Free-list ordering is rejected.** Address-ordering the free list to keep
  reallocation contiguous would move cache misses onto the **hot path**
  (`schedule`/`cancel`) and break the slab's O(1) alloc/free and its LIFO
  allocation locality — a net loss, since schedule/cancel are the high-frequency
  ops and the walk is the cold path.
- **Packed per-slot array is parked, gated.** A contiguous per-slot
  `(deadline, ptr)` array is the *only* fix that doesn't rob the hot path (it
  fixes both the scan and the splice), but it's a slot-representation rewrite that
  duplicates the deadline and puts array growth on `schedule`. Only worth it for a
  caller with a genuine **> L3 working set** (~100k+ live timers) under churn —
  which does not occur in the realistic envs.

## Reproduce

```sh
cargo build --release --bench perf_669_walk --bench perf_server_scenarios

# Isolated walk: contiguous (a) vs scattered (b), swept by population.
BIN=$(find target/release/deps -name 'perf_669_walk-*' -type f -executable | head -1)
for mode in a b; do for n in 10000 50000 200000 500000 1000000; do
  taskset -c 0 "$BIN" $mode $n
done; done

# Realistic-workload poll cache behavior (last section of the output).
BIN=$(find target/release/deps -name 'perf_server_scenarios-*' -type f -executable | head -1)
taskset -c 0 "$BIN"
```

Requires Linux + `perf_event` (`perf_event_paranoid <= 2`) and pinning to a
P-core on a hybrid CPU. Numbers are hardware-specific; the *shape* (flat
contiguous, cliff past L3, realistic ≈ contiguous) is the portable result.
