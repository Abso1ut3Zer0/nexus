# Use Case: Consumer Saturation

How a consumer thread measures its own saturation: is work waiting behind
my processing, how much, and for how long?

## The Problem

A message reaches your handler late. One of two things happened, and the
fix is different for each:

- **It waited for you.** It arrived while this thread was processing
  earlier messages. Fix the consumer: faster handler, split the thread,
  batch, move work off the hot path.
- **It was already old when it arrived.** The producer, the network, or
  the exchange was slow. Not this thread's problem.

Queue depth answers this only on transports that expose it, and only if
sampled at the right moments. Message timestamps answer it exactly, but
need a shared clock and a stamp on every message. `PollSaturation` needs
neither: it works from what each poll returned.

## The Model in One Paragraph

A poll that returns nothing proves the input empty. Every message taken
after that proof arrived after it, so `now - (last proof)` bounds how long
any message in a poll waited. That tick is the **floor**, the bound is
**`behind`**. A short batch poll (fewer than its limit) is the other proof.
A full poll proves nothing: under a backlog, `behind` grows until a short
poll shows you caught up. Healthy reads: `behind == 0`, polls returning
`<= 1` message.

## Recipe: Spin Loop, One Message Per Poll

```rust
use nexus_stats::clock::{Clock, MonotonicClock};
use nexus_stats::monitoring::PollSaturation;

let clock = MonotonicClock::new();                 // nanosecond ticks since construction
let mut sat = PollSaturation::new(50_000);    // budget: 50 µs

loop {
    match rx.try_recv() {
        Ok(msg) => {
            let behind = sat.on_work(clock.stamp(), 1);   // 0: did not wait
            handle(msg, behind);
        }
        Err(TryRecvError::Empty) => sat.on_idle(),       // one store, no clock
        Err(TryRecvError::Disconnected) => break,
    }
    if timer.fired() {                                   // or every N messages
        publish(sat.take());
    }
}
```

The type never reads a clock. Ticks are whatever your stamps use;
`MonotonicClock` is the std bridge (nanoseconds since construction). The later
recipes assume `clock` and `sat` from here.

## Recipe: Batch Poll with a Limit

Poll limits are common (they keep one input from starving the others). A
full poll is not a proof; a short one is. Account per message in the
handler so each message's `behind` is measured from its own start:

```rust
let t0 = clock.stamp();                     // always a sound proof stamp
let mut last = t0;
let n = input.poll(|msg| {
    last = clock.stamp();
    let behind = sat.on_work(last, 1);
    handle(msg, behind);
}, LIMIT);

if n == 0 {
    sat.on_idle();
} else if n < LIMIT {
    sat.on_drained(last);                   // input was empty after the last message
}
```

The last handler's stamp is a sound proof when the transport consumes a
message, runs the handler, then checks for the next. A transport that
reads everything first and dispatches afterwards checked emptiness before
the handlers ran; use `t0` there. Some transports also return short for
reasons other than emptiness (the end of a buffer segment, a fragment
limit): treat an empty poll as a proof only when the poll before it was
also empty, and never a short one.

If you drain into a buffer and report once per batch, every message in
the batch gets the same `behind` and the later ones are under-reported by
the batch's processing time. Fine when `limit × service time` is small
against `budget`; otherwise account per message.

## Recipe: Several Inputs on One Thread

One monitor per thread. `on_work` for each poll that returned work.
`on_idle` only after a pass in which **every** input was polled and every
one was empty: an input skipped in a pass is not known empty in it.

```rust
let mut all_empty = true;
for input in &mut inputs {
    let n = input.poll(|msg| { handle(msg, sat.on_work(clock.stamp(), 1)); }, LIMIT);
    if n > 0 { all_empty = false; }
}
if all_empty { sat.on_idle(); }
```

Inputs on different cadences cost one polling cycle of slack on the bound.

## Recipe: Blocking and Async Consumers

The information is the same bit, hidden: a blocking receive that
**blocked** saw an empty input; one that **returned immediately** found
data that arrived while you were busy. Two ways to recover it.

Non-blocking attempt first (exact; one failed attempt per idle transition,
none under load):

```rust
let msg = match rx.try_recv() {
    Ok(m) => m,
    Err(TryRecvError::Empty) => { sat.on_idle(); rx.recv().await? }
    Err(TryRecvError::Disconnected) => return Ok(()),
};
let behind = sat.on_work(clock.stamp(), 1);
```

Timing the call (nothing extra; an ambiguity zone the size of the epsilon):

```rust
let t0 = clock.stamp();
let n = sock.recv(&mut buf)?;
let t1 = clock.stamp();
if t1 - t0 > WAKE_EPSILON { sat.on_idle(); }   // it blocked: input was empty
let behind = sat.on_work(t1, n as u64);
```

A non-blocking socket's `WouldBlock`, a stream's `Poll::Pending`, a
reactor wakeup with zero events: each is the empty poll. A short stream
read is a proof at that instant; a short datagram read is not.

What an async consumer cannot show this type: the executor's delay between
the task's wake and its run. That is a different resource (the worker
thread), measured with the runtime's own scheduling metrics.

## Reading the Summary

| Field | Meaning | Healthy |
|-------|---------|---------|
| `messages_over_budget / messages_seen` | fraction of messages that waited past `budget` | near 0 |
| `messages_waited` | of those, how many waited for this thread | low |
| `max_behind_ticks` | worst wait bound, in ticks: the longest stretch without catching up | under `budget` |
| `max_messages_per_poll` | queue-length high-water mark when polls drain; "at least this deep" under a limit | `<= 1` |
| `max_backlog_messages` | messages processed without once catching up: the depth measure under a limit | small |
| `is_fully_utilized` | no empty poll all period: utilization was 100% | false |
| `is_backlogged` | never proven empty all period: the consumer never caught up | false |

With utilization from your own service-time sum over the period:

| Utilization | Saturation | Meaning |
|-------------|------------|---------|
| low | `messages_over_budget == 0` | healthy |
| low | `messages_over_budget > 0` | bursts, hidden by averaging: absorb them |
| `is_fully_utilized` | `messages_over_budget > 0` | capacity: split or offload |
| not pegged | `is_backlogged` | a slow path keeps a queue standing |
| any | `behind == 0` on a late message | upstream |

## Recipe: When to Snap, Merging and Smoothing

`take()` closes the period and returns its `PollSummary`; the counters start
over. When to snap is your decision, not the type's: a timer (every
millisecond, every second), a count (every 1,000 messages), an event (the
end of a burst). Snap short for alerting and merge for publishing; the merge
is exact:

```rust
fn merge(a: PollSummary, b: PollSummary) -> PollSummary {
    PollSummary {
        messages_seen: a.messages_seen + b.messages_seen,
        messages_waited: a.messages_waited + b.messages_waited,
        messages_over_budget: a.messages_over_budget + b.messages_over_budget,
        max_backlog_messages: a.max_backlog_messages.max(b.max_backlog_messages),
        max_behind_ticks: a.max_behind_ticks.max(b.max_behind_ticks),
        max_messages_per_poll: a.max_messages_per_poll.max(b.max_messages_per_poll),
        is_fully_utilized: a.is_fully_utilized && b.is_fully_utilized,
        is_backlogged: a.is_backlogged && b.is_backlogged,
    }
}
```

Smoothing belongs on the outputs, once per summary, where it is cheap and
keeps its denominator:

```rust
use nexus_stats::detection::Cusum;
use nexus_stats::smoothing::Ema;

let w = sat.take();
let over_frac = w.messages_over_budget as f64 / w.messages_seen.max(1) as f64;
over_ema.update(over_frac)?;                  // Ema, span of a few summaries
drift.update(w.max_behind_ticks as f64)?;           // Cusum: is the worst case trending up
```

Not inside the type: an EMA there would have to decay on idle spins
(either a clock read per spin or the per-iteration weighting that reads
"fine" while most messages are late), and it would throw away the
denominator.

## With Stamped Messages: Sojourn

When each message carries an enqueue tick from the same clock, the wait is
known exactly (`dequeue - enqueue`, the queue sojourn) and nothing needs
bounding. `SojournSaturation` is the twin of `PollSaturation` for that case,
same vocabulary, same snap-when-you-decide summary:

```rust
use nexus_stats::monitoring::SojournSaturation;

let mut sojourn = SojournSaturation::new(50_000);                 // budget: 50 µs in ns

// per message, in the handler, beside the PollSaturation call. Both stamps
// are i128 wall-clock nanoseconds, so the difference is signed and negative
// on skew; with u64 ticks use `now.wrapping_sub(enqueued) as i64` instead.
let wait: i128 = wall_now_ns - msg.enqueued_wall_ns;
sojourn.update(wait as i64);

// on the same snap as `sat.take()`:
let s = sojourn.take();
// s.messages_over_budget / s.messages_seen, s.max_sojourn_ticks,
// s.min_sojourn_ticks (the floor; 0 means the clocks disagree),
// s.mean_sojourn_ticks(), s.is_backlogged
```

A sojourn is never zero (transit plus processing); what matters is that it
stays near its floor and that the queue keeps draining to within budget.
`is_backlogged` is CoDel's standing-queue rule with your period as the
interval. Keep `PollSaturation` beside it when you want
`max_messages_per_poll` and `is_fully_utilized`, which stamps cannot give
you; keep `CoDel<i64>` when a control decision (shed, drop, back off) should
follow from the delay.

The stamp comes from the transport: for our queues and shared memory the
slot carries it (#765); for an external feed the exchange timestamp plays
the same role and the floor absorbs the clock offset.

## Rules Checklist

1. One monitor per consumer thread.
2. Stamp `on_work` when processing begins; per message in inline handlers.
3. Messages before the proof: `on_drained` describes the input after them.
4. `on_drained` only on a real proof, stamped no later than the empty check.
5. Non-message work: `on_work(start, 0)`, or accept the slack.
6. `take` from the owner's timer, same thread.

## Related

- [PollSaturation](../algorithms/poll-saturation.md): the algorithm page
- [CoDel](../algorithms/codel.md): standing-queue detection from sojourn
- [Backpressure](backpressure.md), [SRE Observability](sre-observability.md)
