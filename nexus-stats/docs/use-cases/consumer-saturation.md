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
use nexus_stats::monitoring::PollSaturation;

let mut sat = PollSaturation::new(clock.now(), 50_000);   // bound: 50 µs in ns

loop {
    match rx.try_recv() {
        Ok(msg) => {
            let behind = sat.on_work(clock.now(), 1);     // 0: did not wait
            handle(msg, behind);
        }
        Err(TryRecvError::Empty) => sat.on_idle(),       // one store, no clock
        Err(TryRecvError::Disconnected) => break,
    }
    if timer.fired() {
        publish(sat.take(clock.now()));
    }
}
```

## Recipe: Batch Poll with a Limit

Poll limits are common (they keep one input from starving the others). A
full poll is not a proof; a short one is. Account per message in the
handler so each message's `behind` is measured from its own start:

```rust
let t0 = clock.now();                       // always a sound proof stamp
let mut last = t0;
let n = input.poll(|msg| {
    last = clock.now();
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
against `bound`; otherwise account per message.

## Recipe: Several Inputs on One Thread

One monitor per thread. `on_work` for each poll that returned work.
`on_idle` only after a pass in which **every** input was polled and every
one was empty: an input skipped in a pass is not known empty in it.

```rust
let mut all_empty = true;
for input in &mut inputs {
    let n = input.poll(|msg| { handle(msg, sat.on_work(clock.now(), 1)); }, LIMIT);
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
let behind = sat.on_work(clock.now(), 1);
```

Timing the call (nothing extra; an ambiguity zone the size of the epsilon):

```rust
let t0 = clock.now();
let n = sock.recv(&mut buf)?;
let t1 = clock.now();
if t1 - t0 > WAKE_EPSILON { sat.on_idle(); }   // it blocked: input was empty
let behind = sat.on_work(t1, n as u64);
```

A non-blocking socket's `WouldBlock`, a stream's `Poll::Pending`, a
reactor wakeup with zero events: each is the empty poll. A short stream
read is a proof at that instant; a short datagram read is not.

What an async consumer cannot show this type: the executor's delay between
the task's wake and its run. That is a different resource (the worker
thread), measured with the runtime's own scheduling metrics.

## Reading the Window

| Field | Meaning | Healthy |
|-------|---------|---------|
| `over / msgs` | fraction of messages that waited past `bound` | near 0 |
| `queued` | messages that waited at all | low |
| `max_behind` | worst wait bound, in ticks: the longest stretch without catching up | under `bound` |
| `max_batch` | queue-length high-water mark when polls drain; "at least this deep" under a limit | `<= 1` |
| `max_run` | messages processed without once catching up: the depth measure under a limit | small |
| `never_idle` | utilization was 100% | false |
| `never_empty` | the queue stood the whole window | false |

With utilization from your own service-time sum over `elapsed`:

| Utilization | Saturation | Meaning |
|-------------|------------|---------|
| low | `over == 0` | healthy |
| low | `over > 0` | bursts, hidden by averaging: absorb them |
| `never_idle` | `over > 0` | capacity: split or offload |
| not pegged | `never_empty` | a slow path keeps a queue standing |
| any | `behind == 0` on a late message | upstream |

## Recipe: Windows, Merging and Smoothing

The window is the `take` cadence. Take short for alerting and merge for
publishing; the merge is exact:

```rust
fn merge(a: PollWindow, b: PollWindow) -> PollWindow {
    PollWindow {
        elapsed: a.elapsed + b.elapsed,
        msgs: a.msgs + b.msgs,
        queued: a.queued + b.queued,
        over: a.over + b.over,
        max_run: a.max_run.max(b.max_run),
        max_behind: a.max_behind.max(b.max_behind),
        max_batch: a.max_batch.max(b.max_batch),
        never_idle: a.never_idle && b.never_idle,
        never_empty: a.never_empty && b.never_empty,
    }
}
```

Smoothing belongs on the outputs, once per window, where it is cheap and
keeps its denominator:

```rust
use nexus_stats::detection::CusumF64;
use nexus_stats::smoothing::EmaF64;

let w = sat.take(now);
let over_frac = w.over as f64 / w.msgs.max(1) as f64;
over_ema.update(over_frac)?;                  // EmaF64, span of a few windows
drift.update(w.max_behind as f64)?;           // CusumF64: is the worst case trending up
```

Not inside the type: an EMA there would have to decay on idle spins
(either a clock read per spin or the per-iteration weighting that reads
"fine" while most messages are late), and it would throw away the
denominator.

## With Stamped Messages: Sojourn

When each message carries an enqueue tick from the same clock, the wait is
known exactly (`dequeue - enqueue`, the queue sojourn) and the time side
needs no bound. Until the dedicated sojourn summary lands (#770), compose
it from existing types beside `PollSaturation`, which still supplies
`max_batch` and the idle flag:

```rust
use nexus_stats::monitoring::{CoDelI64, MaxGaugeI64};

let mut standing = CoDelI64::builder().target(50_000).window(100_000_000).build()?;
let mut worst = MaxGaugeI64::new();

// per message, in the handler:
let sojourn = (wall.now() - msg.sent_wall) as i64;
if standing.update(now, sojourn) == Some(Condition::Degraded) { /* queue stood 100 ms */ }
worst.update(sojourn);
```

A sojourn is never zero (transit plus processing); what matters is that it
stays near its floor. CoDel's rule is built for that: it fires when the
minimum over an interval stays above target.

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
