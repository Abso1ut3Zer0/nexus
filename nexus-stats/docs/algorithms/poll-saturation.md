# PollSaturation — Consumer-Side Saturation from Poll Outcomes

**Bounds how long messages waited for this thread, from what each poll
returned.** No message timestamps, no queue depth, no producer cooperation,
no clock read on an idle spin.

| Property | Value |
|----------|-------|
| Update cost | `on_idle`: one byte store. `on_work`: 22 instructions on the steady path, four predictable branches, no division, no call |
| Memory | 80 bytes |
| Types | `PollSaturation`, `PollSummary` |
| Output | `on_work` returns `behind` (ticks); `take` returns a `PollSummary` |

## What It Does

Saturation of a consumer thread is work that has arrived for it and is
waiting because the thread is busy. It has a **count** (how many are
waiting) and a **duration** (how long each waited). `PollSaturation`
reports both over a window, from one fact the consumer can always
establish itself: a poll that returned nothing proves the input empty.

```
  floor: the latest tick the input was proven empty
  ─────────────────────────────────────────────────────────────▶ time
  empty poll     work         work         work        empty poll
       │          │            │            │              │
       ▼          ▼            ▼            ▼              ▼
     floor      behind=0    behind=3     behind=6       floor pending
                (did not    (arrived     (arrived         again
                 wait)       while #1     while #1/#2
                             ran)         ran)
```

Every message taken arrived after the floor, so `behind = now - floor` at a
working poll is an upper bound on how long any message in it waited. Zero
is exact: the previous poll was empty, nothing waited. A short batch poll
(fewer than its limit) is the other proof. A **full** poll proves nothing:
under a backlog with a poll limit, every poll comes back full, no proof
arrives, and `behind` and `max_backlog_messages` grow until a short poll shows the
consumer caught up. That growth is the signal.

RFC 8289 states the same observation with timestamps: one packet with zero
sojourn means no persistent queue. An empty poll is that observation made
without a timestamp.

Three hot calls and one window read:

| Call | When | Cost |
|------|------|------|
| `on_idle()` | the poll returned nothing | one store, no clock |
| `on_work(now, n)` | `n` messages start processing at `now`; returns `behind` | 22 instructions, ~5 cycles |
| `on_drained(at)` | a batch poll came back short: the input was empty at `at` | a compare and two stores |
| `take()` | whenever you decide to snap: the summary of every poll since the last take | copies 56 bytes |

## Configuration

```rust
use nexus_stats::clock::{Clock, WallClock};
use nexus_stats::monitoring::PollSaturation;

let clock = WallClock::new();                 // nanosecond ticks since construction
let mut sat = PollSaturation::new(50_000);    // budget: 50 µs
```

Ticks are whatever unit your stamps use; the type never reads a clock.
`WallClock` is the std bridge (nanoseconds since construction), so the
budget above is 50 µs. Two knobs, and only two:

- **`budget`**: the wait you consider late. Messages whose `behind` exceeds
  it count toward `messages_over_budget`; nothing else depends on it. Set it from your
  latency budget for this consumer, or from shadow data: `messages_over_budget / messages_seen` near
  zero in a normal hour, clearly above zero in a known busy one.
- **When you snap.** `take()` closes the period and returns its summary.
  The period is your decision: a timer (every millisecond, every second),
  a count (every 1,000 messages), or an event (the end of a burst). Maxima
  survive any period length; the `messages_over_budget / messages_seen` fraction is diluted by a
  long one. Snap at the alert cadence and merge for publishing: sums add,
  maxima take the max, flags AND, exactly.

No span, no decay, no sample count, no clock. Smoothing, if wanted, goes on
the outputs once per summary (`EmaF64` on `messages_over_budget / messages_seen`, `CusumF64` on
`max_behind_ticks`), not inside the type.

## Reading the Summary

| Field | Meaning | Healthy |
|-------|---------|---------|
| `messages_seen` | messages taken in the period | denominator |
| `messages_waited` | of those, how many waited for this thread (not the first after an empty poll) | low |
| `messages_over_budget` | messages with `behind > budget` | `messages_over_budget / messages_seen` near 0 |
| `max_backlog_messages` | most messages processed without once catching up | small |
| `max_behind_ticks` | largest `behind`, in your tick unit: the longest stretch without catching up | under `budget` |
| `max_messages_per_poll` | most messages one poll returned: queue length when polls drain | `<= 1` |
| `is_fully_utilized` | no empty poll in the period: the thread never waited for input, utilization 100% | false |
| `is_backlogged` | never proven empty in the period: the consumer never caught up (CoDel's standing queue) | false |

`max_messages_per_poll` is the count form of saturation: with polls that drain the
input it is the queue-length high-water mark. Under a poll limit it pins
at the limit and means "at least this deep"; `max_backlog_messages` is the depth
measure there. Everything is weighted per message, never per loop
iteration: a detector sampled once per spin reads "fine" through a second
where most messages were late, because almost every spin is empty.

Read it beside utilization (your sum of service time over the period, whose
length you know because you chose it), the USE method's other column for
the same thread:

| Utilization | Saturation | Meaning | Fix |
|-------------|------------|---------|-----|
| low | `messages_over_budget == 0`, `max_messages_per_poll <= 1` | healthy | none |
| low | `messages_over_budget > 0` | bursts, hidden by averaging | absorb them: batch, defer non-critical work |
| `is_fully_utilized` | `messages_over_budget > 0` | capacity | split the consumer, move work off the thread |
| not pegged | `is_backlogged` | service-time spikes keep a queue standing | find the slow path |
| any | `behind == 0` on a late message | the delay was upstream | not this thread's problem |

## Examples

### Spin loop, one message per poll

```rust
use nexus_stats::clock::{Clock, WallClock};
use nexus_stats::monitoring::PollSaturation;

let clock = WallClock::new();                 // nanosecond ticks since construction
let mut sat = PollSaturation::new(50_000);    // budget: 50 µs

loop {
    match rx.try_recv() {
        Ok(msg) => {
            let behind = sat.on_work(clock.stamp(), 1);
            handle(msg, behind);
        }
        Err(TryRecvError::Empty) => sat.on_idle(),
        Err(TryRecvError::Disconnected) => break,
    }
    if timer.fired() {                        // or every N messages: your call
        publish(sat.take());
    }
}
```

### Batch poll with a limit, inline handler

Per-message accounting is the tighter form: each message's `behind` is
measured from its own start. The short-poll proof uses the last handler's
stamp, which is sound when the transport consumes a message, runs the
handler, then checks for the next; a stamp taken before the poll is always
sound and loose by the poll's duration.

```rust
let t0 = clock.stamp();
let mut last = t0;
let n = input.poll(|msg| {
    last = clock.stamp();
    let behind = sat.on_work(last, 1);
    handle(msg, behind);
}, LIMIT);

if n == 0 {
    sat.on_idle();
} else if n < LIMIT {
    sat.on_drained(last);
}
```

More loop shapes, including blocking and async consumers, several inputs
on one thread, and the stamped-message companion, are in the
[Consumer Saturation](../use-cases/consumer-saturation.md) use case.

## Guarantees and Limits

Every error is in the direction of over-reporting. If `on_work` returns 0,
nothing in that poll waited behind an earlier poll's work. If it returns
`b`, nothing waited more than `b` plus one idle iteration. `messages_waited` and
`messages_over_budget` never under-count. Any split of a call sequence into periods merges
back to the single-take result.

What it cannot do: `behind` is a bound, not the wait. With one message per
poll it is the busy period so far, loose under sustained high utilization
(above roughly 75%); batch polls with `on_drained` tighten it, and an
enqueue stamp on the same clock makes it exact. It cannot see delay before
a message became visible to this poll. A false proof under-reports until
the next true one. Ticks must be monotonic: after a backwards step every
bound reads 0 and proofs are ignored until the clock passes the floor.

## Performance

Measured pinned (`taskset -c 0`, best of three, `examples/perf_stats.rs`):
`on_work` 5 cycles p50, `on_idle` 1 cycle, beside `LivenessU64::update` at
6 and `CoDelI64::update` at 5.

Disassembly of the steady `on_work` path (floor not pending): a byte load
and test, a saturating subtraction (`sub` + `cmovae`), one `add` for the
run, one SIMD `paddq` the compiler uses for `messages_seen` and `messages_waited` together,
then four `cmp` + forward `ja` to out-of-line updates for `messages_over_budget` and the
three maxima. 22 instructions, no division, no float, no call. `on_idle`
is `mov byte ptr [self], 7; ret`. `on_drained` is nine instructions.

The struct is `repr(C)` with the fields every working poll touches in the
first cache line. All counters are `u64`: at 333k msg/s a `u32` wraps in
3.6 hours without a `take`.
