# Patterns

## Request timeouts

The classic timer-wheel workload: every outgoing request gets a deadline,
most are cancelled when the response arrives, the survivors fire as
timeouts.

```rust
use std::time::{Duration, Instant};
use nexus_timer::{Wheel, TimerHandle};
use std::collections::HashMap;

pub struct RequestTracker {
    wheel: Wheel<RequestId>,
    pending: HashMap<RequestId, TimerHandle<RequestId>>,
}
# #[derive(Clone, Copy, Hash, PartialEq, Eq)] pub struct RequestId(u64);

impl RequestTracker {
    pub fn new(now: Instant) -> Self {
        Self {
            wheel: Wheel::unbounded(4096, now),
            pending: HashMap::new(),
        }
    }

    pub fn start(&mut self, id: RequestId, timeout_at: Instant) {
        let handle = self.wheel.schedule(timeout_at, id);
        self.pending.insert(id, handle);
    }

    /// Response arrived before deadline — cancel the timer.
    pub fn complete(&mut self, id: RequestId) {
        if let Some(handle) = self.pending.remove(&id) {
            self.wheel.cancel(handle);
        }
    }

    /// Periodic poll — returns IDs whose timers fired.
    pub fn poll(&mut self, now: Instant, fired: &mut Vec<RequestId>) {
        let start = fired.len();
        self.wheel.poll_and_rebalance(now, fired);
        for id in &fired[start..] {
            self.pending.remove(id);
        }
    }
}
```

The hot path here is `start` + `complete` — both are O(1). Timeouts
(`poll_and_rebalance` + fire) are the exception. `poll_and_rebalance` both
collects the ready timers *and* keeps the wheel tidy so the next poll stays
cheap — see [Keeping poll cheap with many timers](#keeping-poll-cheap-with-many-timers)
for when to manage that yourself.

## Keeping poll cheap with many timers

`poll` only *collects* ready timers — it does not reorganize the wheel. If you
call bare `poll` and nothing else, entries stay in the coarse level they were
scheduled into, and a poll that lands on a fat coarse slot walks the whole slot
to find the few ready timers — an O(population) spike on a busy wheel. To avoid
that, keep entries flowing down to fine, exact slots. There are three ways,
from simplest to most control.

**1. `poll_and_rebalance` — the default.** Collects *and* rebalances in one
call, so future polls stay cheap. Reach for this unless you have a reason not
to:

```rust
use std::time::Instant;
use nexus_timer::Wheel;

fn tick<T>(wheel: &mut Wheel<T>, now: Instant, fired: &mut Vec<T>) {
    wheel.poll_and_rebalance(now, fired);
}
```

**2. Bound the rebalancing per poll.** If a single `poll_and_rebalance` can
spike when a dense slot comes due, cap how much reorganizing one poll does with
`WheelBuilder::max_rebalances_per_poll`. The rest is spread across later polls;
it never delays a fire:

```rust
use std::time::Instant;
use nexus_timer::{Wheel, WheelBuilder};

fn build<T: 'static>(now: Instant) -> Wheel<T> {
    WheelBuilder::default()
        .max_rebalances_per_poll(64) // smooth the rebalance burst
        .unbounded(4096)
        .build(now)
        .expect("default-derived config is valid")
}
```

**3. Disperse the work opportunistically — the lowest-tail option.** For the
flattest possible collect path under a large number of timers, split the two:
`poll` cheaply on the hot path, and `rebalance` only during genuine slack —
e.g. whenever a poll comes back empty. Bound each call so a run of empty polls
spreads the work instead of stalling on one sweep (`rebalance` is resumable):

```rust
use std::time::Instant;
use nexus_timer::Wheel;

const REBALANCE_BUDGET: usize = 64;

fn tick<T>(wheel: &mut Wheel<T>, now: Instant, fired: &mut Vec<T>) {
    let collected = wheel.poll(now, fired);
    if collected == 0 {
        // Nothing to deliver — use the slack to maintain, a bounded slice.
        wheel.rebalance(now, REBALANCE_BUDGET);
    }
}
```

This keeps busy polls doing only the cheap collect and pushes the reorganizing
onto the idle ones, which measurably flattens the collect tail at scale. It
self-tunes to load: no cadence to pick, and maintenance happens exactly when
there is nothing else to do. Just don't `rebalance` on *every* poll — that
re-walks the look-ahead window and is pure overhead. See the `rebalance` API
docs for the full rationale.

## Exchange heartbeats

Heartbeats are periodic fire-and-forget timers. Use `schedule_forget` and
let them fire naturally.

```rust
use std::time::{Duration, Instant};
use nexus_timer::Wheel;

pub struct Heartbeat;

pub fn schedule_heartbeat(wheel: &mut Wheel<Heartbeat>, now: Instant) {
    wheel.schedule_forget(now + Duration::from_secs(10), Heartbeat);
}

// In your poll loop:
fn on_heartbeat_tick<F: FnMut()>(mut send: F) {
    send();
}
```

For *recurring* heartbeats, re-schedule from the fire handler:

```rust
# use std::time::{Duration, Instant};
# use nexus_timer::Wheel;
# pub struct Heartbeat;
fn tick(wheel: &mut Wheel<Heartbeat>, _fired: Heartbeat, now: Instant) {
    // Do the heartbeat work...
    send_heartbeat();

    // Re-arm for the next interval
    wheel.schedule_forget(now + Duration::from_secs(10), Heartbeat);
}
# fn send_heartbeat() {}
```

## Deadline-driven event loop

Use `next_deadline` to compute how long to sleep between polls:

```rust
use std::time::{Duration, Instant};
use nexus_timer::Wheel;

fn event_loop_step<T>(wheel: &mut Wheel<T>, fired: &mut Vec<T>) -> Duration {
    let now = Instant::now();
    wheel.poll_and_rebalance(now, fired);

    match wheel.next_deadline() {
        Some(next) => next.saturating_duration_since(Instant::now()),
        None       => Duration::from_millis(100),  // idle
    }
}
```

Caller can then sleep (or epoll-wait) for the returned duration before the
next iteration. This gives you accurate wakeups without constant polling.

## Budgeted fire cap for bounded tail latency

If you have thousands of timers firing in a burst, an unbounded poll can spike
your event-loop iteration time. Cap the number collected per iteration with
`poll_and_rebalance_with_limit` (or `poll_with_limit` for the collect-only
variant):

```rust
use std::time::Instant;
use nexus_timer::Wheel;

const MAX_TIMERS_PER_TICK: usize = 32;

fn drain<T>(wheel: &mut Wheel<T>, now: Instant, buf: &mut Vec<T>) {
    let fired = wheel.poll_and_rebalance_with_limit(now, MAX_TIMERS_PER_TICK, buf);
    if fired == MAX_TIMERS_PER_TICK {
        // Hit the budget — remaining timers will fire on the next iteration
        // with the *same* `now`, preserving the fair-share property.
    }
}
```

The next call with the same `now` resumes where the previous stopped, so you
don't starve any slot. (`limit` bounds the *collect*; rebalancing is bounded
separately by `max_rebalances_per_poll`.)

## Cancellable retries

Combine `reschedule` with a retry counter for exponential-backoff
reconnects:

```rust
use std::time::{Duration, Instant};
use nexus_timer::{Wheel, TimerHandle};

pub struct ReconnectState {
    pub handle: TimerHandle<ConnectionId>,
    pub attempts: u32,
}
# #[derive(Clone, Copy)] pub struct ConnectionId(u64);

pub fn bump_retry(
    wheel: &mut Wheel<ConnectionId>,
    state: ReconnectState,
    now: Instant,
) -> ReconnectState {
    let delay_ms = 100u64 << state.attempts.min(10);  // cap at 100s
    let handle = wheel.reschedule(
        state.handle,
        now + Duration::from_millis(delay_ms),
    );
    ReconnectState { handle, attempts: state.attempts + 1 }
}
```

`reschedule` is cheaper than `cancel` + `schedule` because it doesn't
construct a new entry or touch the allocator.
