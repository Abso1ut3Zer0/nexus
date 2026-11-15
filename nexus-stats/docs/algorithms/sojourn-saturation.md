# SojournSaturation — Consumer Saturation from Queue Sojourn

**Exact per-message wait, summarized per period.** The stamped twin of
[PollSaturation](poll-saturation.md): where that type bounds the wait from
poll outcomes, this one takes the measured sojourn (dequeue tick minus
enqueue tick, same clock) and reports how many waited past your budget, the
floor, the worst, the total, and whether the queue ever drained.

| Property | Value |
|----------|-------|
| Update cost | 27 straight-line instructions, no branches, no division, no call; 6 cycles |
| Memory | 56 bytes on 64-bit targets |
| Types | `SojournSaturation`, `SojournSummary` |
| Input | `i64` sojourn in any tick unit; negative (clock skew) clamps to zero |
| Output | `take()` returns a `SojournSummary` |

## What It Does

Saturation of a consumer thread is work that has arrived for it and is
waiting because the thread is busy. With an enqueue stamp on every message
the wait is known exactly, so there is nothing to bound: the type is a
per-period summary of the sojourn distribution, built so each number has
one meaning.

A sojourn is never zero on a healthy system: there is always transit and
processing. What matters is whether it stays near its floor or grows, and
whether the queue keeps draining to within budget.

## Configuration

```rust
use nexus_stats::monitoring::SojournSaturation;

let mut sat = SojournSaturation::new(50_000);      // budget: 50 µs in ns ticks

// per message, in the handler: same clock on both sides
sat.update((now_wall_ns - msg.enqueued_wall_ns) as i64);

// whenever you decide to snap: a timer, every N messages, an event
let s = sat.take();
```

Two knobs, and only two:

- **`budget`**: the sojourn you consider late. Messages above it count
  toward `messages_over_budget`; a message at or below it proves the queue
  drained for `is_backlogged`.
- **When you snap.** `take()` closes the period and returns its summary.
  The period is your decision; the type keeps no clock. Snap short for
  alerting and merge for publishing.

No interval, no target, no baseline window, no smoothing. `CoDelI64` stays
for callers who want the RFC detector to drive a control decision (shed,
drop, back off); this is the observability summary.

## Reading the Summary

| Field | Meaning | Healthy |
|-------|---------|---------|
| `messages_seen` | messages in the period | denominator |
| `messages_over_budget` | of those, sojourn above `budget` | `/ messages_seen` near 0 |
| `min_sojourn_ticks` | the floor: transit plus processing. `u64::MAX` for an empty period | small and stable. **Zero means the two clocks disagree** |
| `max_sojourn_ticks` | the worst wait | under `budget` |
| `total_sojourn_ticks` | sum of sojourns, saturating | |
| `mean_sojourn_ticks()` | `total / messages_seen`, integer | close to `min` |
| `is_backlogged` | no message within budget all period: CoDel's standing queue with the period as the interval. Vacuously true for an empty period, as in `PollSummary` | false |

`total_sojourn_ticks / period length` is the mean number of messages waiting
(Little's law), so the count form of saturation is one division away;
healthy is well under 1. That is the same quantity `PollSaturation` reports
as `max_messages_per_poll`, reached from the other direction.

Merging summaries is an exact plain fold: counts and totals add, `min`
takes the min, `max` the max, `is_backlogged` ANDs. An empty period is the
identity of every field and carries no information in `min`, `max` or the
flag; read `messages_seen` first.

## Clocks and Stamps

The stamp and the dequeue tick must come from the same clock:

- **Same process or same host**: one clock (monotonic ticks, or wall time
  in nanoseconds since both sides can read `CLOCK_REALTIME`). The sojourn
  is exact. For our own queues and shared memory the slot carries the
  enqueue stamp (#765); the consumer reads it and never mutates the message.
- **Across hosts**: wall clocks carry an offset. Every sojourn shifts by the
  same amount, `min_sojourn_ticks` absorbs it, and `budget` must be read
  against that floor. The exchange timestamp on a market-data message is
  this case; the same type then measures upstream lag.

Subtract in the caller's wide type (`i128` for nanosecond wall clocks) and
pass the difference: a nanosecond difference fits `i64` for 292 years. A
negative difference is clock skew; the type clamps it to zero, which shows
up as a zero minimum.

## Which One

| You have | Use |
|---|---|
| An enqueue tick on the same clock | `SojournSaturation`: exact. Add `PollSaturation` beside it if you also want `max_messages_per_poll` and the utilization flag. |
| No stamp (sockets, buses, channels you don't own, one-per-poll loops) | `PollSaturation`: a sound bound from emptiness proofs. |
| A control decision to drive from queue delay | `CoDelI64` on the sojourn. |

## Performance

Measured pinned (`taskset -c 0`, best of three, `examples/perf_stats.rs`,
one message in four over budget at random so the compare cannot be
predicted): `update` 6 cycles p50, beside `CoDelI64::update` at 5 and
`PollSaturation::on_work` at 5 in the same runs.

`update` is branchless: the clamp is a `cmovg`, the over-budget and
drained flags are `seta`/`setbe` folded into an add and an `or`, the
minimum, maximum and saturating total are `cmov`s. 27 straight-line
instructions, no jump, no division, no float, no call. The struct is the
budget, five `u64` accumulators and a flag: 56 bytes on 64-bit targets.
