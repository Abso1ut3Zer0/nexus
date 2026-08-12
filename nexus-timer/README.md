# nexus-timer

High-performance timer wheel with O(1) insert and cancel.

## Why This Crate?

Standard timer implementations (priority queues, sorted trees) have
O(log n) insert or O(log n) cancel. Timer wheels give O(1) for both by
hashing deadlines into coarse-grained slots across multiple levels.

`nexus-timer` is a hierarchical, rebalancing timer wheel:

- **Collect + rebalance** — a timer is placed in the coarsest level that fits
  its deadline, then **rebalanced** down to finer levels as its deadline nears,
  so `poll` collects ready timers from small, exact fine-level slots instead of
  walking a fat coarse slot on every call. Rebalancing folds into the poll
  (`poll_and_rebalance`), can be bounded (`max_rebalances_per_poll`), or run
  proactively off the hot path (`rebalance`) to keep the poll tail flat under a
  large number of timers. Timers fire at their exact tick.
- **Intrusive active-slot lists** — only non-empty slots are visited
  during poll and next-deadline queries. No bitmap, no full scan.
- **Embedded refcounting** — lightweight `Cell<u8>` refcount per entry
  enables fire-and-forget timers alongside cancellable timers without
  external reference-counting machinery.
- **Slab-backed storage** — entries live in a
  [`nexus-slab`](https://crates.io/crates/nexus-slab) allocator. No
  heap allocation per timer after init.

## Quick Start

```rust
use std::time::{Duration, Instant};
use nexus_timer::Wheel;

let now = Instant::now();
let mut wheel: Wheel<u64> = Wheel::unbounded(4096, now);

// Schedule a timer 100ms from now
let handle = wheel.schedule(now + Duration::from_millis(100), 42u64);

// Cancel before it fires — get the value back
let value = wheel.cancel(handle);
assert_eq!(value, Some(42));
```

## Configuration

Default parameters match the Linux kernel timer wheel (1ms tick,
64 slots/level, 8x multiplier, 7 levels — ~4.7 hour range).

```rust
use std::time::{Duration, Instant};
use nexus_timer::{Wheel, WheelBuilder};

let now = Instant::now();

// Custom tick duration and slot count
let wheel: Wheel<u64> = WheelBuilder::default()
    .tick_duration(Duration::from_micros(100))
    .slots_per_level(32)
    .unbounded(4096)
    .build(now);
```

The builder uses a typestate pattern — configuration setters are only
available before selecting bounded or unbounded mode:

```text
WheelBuilder  ─.unbounded(chunk_cap)─▶  UnboundedWheelBuilder  ─.build(now)─▶  Wheel<T>
              ─.bounded(cap)──────────▶  BoundedWheelBuilder    ─.build(now)─▶  BoundedWheel<T>
```

## Bounded vs Unbounded

| | `Wheel<T>` (unbounded) | `BoundedWheel<T>` |
|---|---|---|
| Storage | Growable slab (chunks) | Fixed-capacity slab |
| Schedule | `schedule()` — always succeeds | `try_schedule()` — returns `Err(Full)` |
| Use case | Unknown timer count | Known upper bound, zero growth |

```rust
use std::time::{Duration, Instant};
use nexus_timer::BoundedWheel;

let now = Instant::now();
let mut wheel: BoundedWheel<u64> = BoundedWheel::bounded(1024, now);

let handle = wheel.try_schedule(now + Duration::from_millis(50), 42).unwrap();
wheel.cancel(handle);
```

## API

### Scheduling

| Method | Wheel | Returns | Notes |
|---|---|---|---|
| `schedule(deadline, value)` | All | `TimerHandle<T>` | Panics if bounded slab is full |
| `schedule_forget(deadline, value)` | All | `()` | Fire-and-forget; panics if bounded slab is full |
| `try_schedule(deadline, value)` | Bounded | `Result<TimerHandle<T>, Full<T>>` | Fails at capacity |
| `try_schedule_forget(deadline, value)` | Bounded | `Result<(), Full<T>>` | Fire-and-forget, fails at capacity |

### Cancellation & Rescheduling

| Method | Returns | Notes |
|---|---|---|
| `cancel(handle)` | `Option<T>` | `Some(T)` if active, `None` if already fired |
| `free(handle)` | `()` | Releases handle, timer stays as fire-and-forget |
| `reschedule(handle, new_deadline)` | `TimerHandle<T>` | Moves active timer to new deadline without rebuilding value |

### Polling

| Method | Returns | Notes |
|---|---|---|
| `poll(now, buf)` | `usize` | Fires all expired, appends values to `buf` |
| `poll_with_limit(now, limit, buf)` | `usize` | Fires up to `limit`, resumable on next call |

### Query

| Method | Returns | Notes |
|---|---|---|
| `next_deadline()` | `Option<Instant>` | Lower bound on the earliest deadline (never later; may read early after cancel/fire) |
| `len()` | `usize` | Number of active timers |
| `is_empty()` | `bool` | Whether the wheel is empty |

## TimeoutList — Fixed-Duration Variant

The wheel's poll is O(active population): it walks every entry of every
active slot to prove which are due. That is the right trade when deadlines
are *arbitrary*. But many callers schedule **one fixed timeout for
everything** — a flat 5 s deadline on every item. For that workload the
wheel buckets by deadline to solve an ordering problem that does not exist.

`TimeoutList<T>` exploits the single duration. A constant timeout plus a
monotone clock means deadlines are monotone in insertion order, so a new
entry is always appended at the tail of one intrusive list, keeping it
sorted with no comparisons. Poll walks from the head and stops at the first
not-due entry — **O(fired)**. `next_deadline()` is the head's deadline:
exact, O(1), no cache.

The timeout is fixed at construction, so there is **no `deadline` parameter**
anywhere in the API — out-of-order insertion is unrepresentable rather than
merely discouraged.

```rust
use std::time::{Duration, Instant};
use nexus_timer::{TimeoutList, TimeoutListBuilder};

let now = Instant::now();

// Every timer gets the same 5-second timeout.
let mut list: TimeoutList<u64> = TimeoutListBuilder::new(Duration::from_secs(5))
    .unbounded(4096)
    .build(now);

let handle = list.schedule(now, 42);   // fires at now + 5s
let value = list.cancel(handle);       // O(1) mid-list unlink
assert_eq!(value, Some(42));
```

Same `schedule` / `schedule_forget` / `try_schedule` / `cancel` / `free` /
`poll` / `poll_with_limit` / `next_deadline` surface as the wheel, backed by
the same slab storage, handle refcount protocol, and DLL splice logic. There
is no `reschedule` (cancel and re-schedule instead — rescheduling *earlier*
would break the sort) and no `min_deadline` cache (the head *is* the min).

Nothing-due poll is flat across population — the whole point:

| Live population | wheel poll (0-fire) | `TimeoutList` poll (0-fire) |
|---|---|---|
| 100 | 0.2 µs | ~12 cycles |
| 1,000 | 5.6 µs | ~12 cycles |
| 10,000 | 454 µs | ~12 cycles |
| 50,000 | 2.4 ms | ~12 cycles |

Amortized cycles/op — a single-op `rdtsc` bracket carries a ~20-cycle
measurement floor, so the bench reports that floor and the percentile tails
alongside these amortized figures to keep them honest.

```bash
cargo build --release --bench perf_timeout_list -p nexus-timer
taskset -c 0 ./target/release/deps/perf_timeout_list-*
```

## Design

### Level Structure

```text
Level 0:  64 slots × 1ms   =     64ms range
Level 1:  64 slots × 8ms   =    512ms range
Level 2:  64 slots × 64ms  =  4,096ms range
Level 3:  64 slots × 512ms = 32,768ms range
  ...
Level 6:                    ≈  4.7 hour range
```

Each level covers 8x the time range of the previous (configurable via
`clk_shift`). A timer is placed in the coarsest level that can represent
its deadline, and rebalanced down to finer levels as its deadline nears.

### Handle Lifecycle

Handles returned by `schedule()` / `try_schedule()` are move-only tokens
that **must** be consumed via `cancel()` or `free()`. Dropping a handle
without consuming it is a programming error (caught by `debug_assert!`
in debug builds).

```text
schedule() ─▶ TimerHandle ─┬─ cancel()     ─▶ Option<T>
                            ├─ free()       ─▶ (fire-and-forget)
                            └─ reschedule() ─▶ TimerHandle (new deadline)
```

## Performance

All measurements in CPU cycles, Intel Core Ultra 7 155H, pinned to
physical core, turbo boost disabled. 50k samples, 5k warmup.

| Operation | p50 | p90 | p99 | p999 |
|---|---|---|---|---|
| schedule + cancel (paired) | **48** | 50 | 80 | 82 |
| schedule_forget | **40** | 42 | 44 | 72 |
| cancel (pre-scheduled) | **26** | 28 | 30 | 38 |
| poll (per entry, 100 batch) | **8** | 8 | 16 | 30 |
| poll (empty wheel) | **54** | 56 | 58 | 116 |
| sched+cancel @100k active | **48** | 52 | 58 | 92 |

Schedule + cancel is **48 cycles** at p50 regardless of wheel population
(100k active timers shows identical p50). Poll fires at **8 cycles per
entry** in batch. Tail latency stays tight — p999 for the core
schedule+cancel path is 82 cycles.

```bash
cargo build --release --example perf_timer -p nexus-timer
taskset -c 0 ./target/release/examples/perf_timer
```

### Overflow Handling

`ticks_to_instant` uses saturating arithmetic when converting tick counts back to `Instant` values. If the tick count would overflow the `Duration` representation, it saturates to `Duration::MAX` rather than panicking. This prevents crashes when timers are scheduled far into the future or when the wheel has been running for extended periods.

### Thread Safety

`Send` (if `T: Send`), `!Sync`. Timer wheels can be moved to another
thread at setup time, but are designed for single-threaded event
loops — no locking, no atomic operations on the hot path.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT License](LICENSE-MIT) at your option.
