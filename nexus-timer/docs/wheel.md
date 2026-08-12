# The `Wheel` API

## Construction

```rust
use std::time::Instant;
use nexus_timer::{Wheel, BoundedWheel, WheelBuilder};

let now = Instant::now();

// Unbounded (growable slab), default config
let wheel: Wheel<u64> = Wheel::unbounded(4096, now);

// Bounded (fixed capacity), default config
let wheel: BoundedWheel<u64> = BoundedWheel::bounded(4096, now);

// Custom config via builder
let wheel: Wheel<u64> = WheelBuilder::new()
    .tick_duration(std::time::Duration::from_micros(100))
    .slots_per_level(32)
    .clk_shift(4)           // 16x per level
    .num_levels(6)
    .unbounded(4096)
    .build(now)
    .unwrap();
```

The builder validates at `.build()` time, returning `Err(ConfigError)` on a bad
config — `slots_per_level` must be a power of 2 and ≤ 64, `num_levels` must be
≤ 8, `2^clk_shift` must be `< slots_per_level` (so rebalancing always relocates
to a strictly finer level), `tick_duration` must be non-zero and fit in u64
nanoseconds, and the total range
(`slots_per_level << ((num_levels-1) * clk_shift)`) must not overflow u64. The
convenience constructors (`Wheel::unbounded`, `Wheel::bounded`) use the default
config and are infallible.

`chunk_capacity` (unbounded) is the slab chunk size — how many entries the
underlying slab allocates per chunk as it grows. `capacity` (bounded) is
the total maximum number of concurrent timers.

## Scheduling

```rust
use std::time::{Duration, Instant};
use nexus_timer::{Wheel, TimerHandle};

let now = Instant::now();
let mut wheel: Wheel<OrderId> = Wheel::unbounded(1024, now);
# #[derive(Clone, Copy)] struct OrderId(u64);

// Cancellable timer — returns a handle
let handle: TimerHandle<OrderId> = wheel.schedule(
    now + Duration::from_millis(500),
    OrderId(42),
);

// Fire-and-forget — no handle, cannot be cancelled
wheel.schedule_forget(now + Duration::from_millis(250), OrderId(43));
```

`schedule` returns a `TimerHandle<T>`. The handle must be consumed — via
`cancel`, `free`, or `reschedule`. Dropping a handle is a programming error
(debug-assert fires).

Bounded wheels also expose `try_schedule` / `try_schedule_forget` which
return `Result<_, Full<T>>` on capacity exhaustion. Use these when you want
graceful handling rather than a panic.

## Cancelling

```rust
# use std::time::{Duration, Instant};
# use nexus_timer::Wheel;
# let now = Instant::now();
# let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);
# let handle = wheel.schedule(now + Duration::from_millis(500), 42u64);
// cancel: unlinks the entry, returns the value if the timer hadn't fired yet
match wheel.cancel(handle) {
    Some(value) => { /* timer was still pending, you get T back */ }
    None        => { /* timer already fired — handle is a "zombie" */ }
}
```

The handle is consumed either way. If the timer already fired during a
prior `poll`, the value was already delivered to the poll buffer; `cancel`
on a zombie handle just frees the slab entry.

## Free (convert to fire-and-forget)

```rust
# use std::time::{Duration, Instant};
# use nexus_timer::Wheel;
# let now = Instant::now();
# let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);
# let handle = wheel.schedule(now + Duration::from_millis(500), 42u64);
// Drop cancellation rights without cancelling the timer
wheel.free(handle);
```

Useful when you scheduled a timer cancellable-by-default but have decided
you no longer care about cancellation.

## Reschedule

```rust
# use std::time::{Duration, Instant};
# use nexus_timer::Wheel;
# let now = Instant::now();
# let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);
# let handle = wheel.schedule(now + Duration::from_millis(500), 42u64);
let handle = wheel.reschedule(handle, now + Duration::from_millis(1000));
```

Moves the entry from its current slot to the slot for the new deadline
*without reconstructing the value*. This is the fast path for
retransmission timers ("bump the TCP retransmit deadline each time we get
data").

Panics if called on a zombie handle (timer already fired).

## Polling

```rust
# use std::time::{Duration, Instant};
# use nexus_timer::Wheel;
let now = Instant::now();
let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);
wheel.schedule_forget(now + Duration::from_millis(5), 1);
wheel.schedule_forget(now + Duration::from_millis(10), 2);

let mut fired: Vec<u64> = Vec::with_capacity(64);
wheel.poll_and_rebalance(now + Duration::from_millis(12), &mut fired);
// fired contains [1, 2] — all expired timer values
```

`poll(now, buf)` collects every ready (expired) timer and appends its value
to `buf`. It does **not** reorganize the wheel — see `poll_and_rebalance`
below.

`poll_with_limit(now, limit, buf)` is the budgeted version: collect up to
`limit` timers and return how many. Useful in a poll loop where you want to
cap the work done in one iteration. If the limit is hit, the next call with
the same `now` resumes wherever you left off.

`poll_and_rebalance(now, buf)` is the batteries-included poll: it collects
ready timers **and** rebalances the wheel — moving not-yet-due entries down
to finer levels so future polls stay cheap under a large number of timers.
Rebalancing here is bounded by `WheelBuilder::max_rebalances_per_poll` and
never delays a fire. Reach for this by default.

`rebalance(now, limit)` does the reorganizing on its own, so a
latency-sensitive loop can `poll` cheaply on the hot path and `rebalance`
during slack (for example, only when a poll comes back empty). See the
`rebalance` rustdoc for the recommended pattern.

## `next_deadline`

```rust
# use std::time::{Duration, Instant};
# use nexus_timer::Wheel;
# let now = Instant::now();
# let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);
# wheel.schedule_forget(now + Duration::from_millis(10), 1);
let next: Option<Instant> = wheel.next_deadline();
// Use this to compute how long your event loop should sleep before polling again
```

Walks only *active* (non-empty) slots, so the cost is O(active_slots),
typically tens of cycles even for wheels holding thousands of timers.
