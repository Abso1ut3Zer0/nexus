# CoDel — Controlled Delay Queue Monitor

**CoDel standing-queue detection (RFC 8289).** Detects standing queues before
buffers fill by requiring the time items wait to stay above target for a whole
interval, not just once.

| Property | Value |
|----------|-------|
| Update cost | one compare and one timestamp compare |
| Memory | 56 bytes |
| Types | `CoDelI64`, `CoDelF64` |
| Priming | Configurable via `min_samples` |
| Output | `Option<Condition>` — `Normal` or `Degraded` |

## What It Does

```
  Queue sojourn time over time:

  Sojourn (μs)
  500 ┤                    ·  ·
  400 ┤                 · ·  ·  · ·
  300 ┤              ·  ·  ·  ·  ·  ·  ·
  200 ┤── ── ── ── ── ── ── ── ── ── ── ── ── target
  150 ┤           ·
  100 ┤  · ·  ·  ·                          ·  ·
   50 ┤    ·  ·                                ·  · ·  ·
      └───────────────────────────────────────────────────── t
       Normal     │   Elevated (standing queue)  │  Normal
                  │                              │
                  │  even the MIN is above       │
                  │  target for a full window    │

  first_above deadline:
                     armed ────────────► reached
      ─────────────────┬──────────────┬───────────────────────
       no deadline     │ Normal       │ Degraded      │ cleared by a
       (all ≤ target)  │ (waiting out │ (above target │ sample ≤ target
                       │  the window) │  for a window)│
```

The key insight from CoDel: a burst puts a few items above target, but
some item soon gets through quickly, which proves there is no standing
backlog. A standing queue is one where *no* item gets through quickly for
a whole interval. So one slow sample never counts; only "above target,
continuously, for the whole window" does.

## When to Use It

**Use CoDel when:**
- You have a producer-consumer queue and want early warning
- You want to detect congestion before buffers fill and you hit hard backpressure
- You can timestamp items at enqueue time

**Don't use CoDel when:**
- You don't have timestamps on queued items → use [Saturation](saturation.md) with queue depth instead
- You want to detect individual slow items → use [AdaptiveThreshold](adaptive-threshold.md) on sojourn times
- You want to detect mean shifts in processing time → use [CUSUM](cusum.md)

## How It Works

On each dequeue, compute `sojourn = now - enqueue_time` and feed it to
CoDel along with the current timestamp.

Internally, the `first_above_time` rule from RFC 8289 section 5.6:
1. A sojourn at or below target **disarms** the deadline → `Condition::Normal`
2. A sojourn above target with no deadline armed **arms** one at
   `now + window` → `Condition::Normal` (waiting out the window)
3. A sojourn above target at or after the deadline → `Condition::Degraded`,
   and it stays `Degraded` until a sample at or below target disarms it

One timestamp of state. There is no windowed minimum, so the detector is
exact: it fires at precisely one window of continuous excess, never on a
transient.

This is the **measurement layer** of CoDel. CoDel itself is a *policy*
(drop packets when congested). CoDel gives you the signal — you
decide the response (slow producers, shed load, alert, etc.).

## Configuration

```rust
let mut qd = CoDelI64::builder()
    .target(100_000)       // 100μs target sojourn time
    .window(1_000_000_000) // 1 second observation window (in nanoseconds)
    .min_samples(10)
    .build().unwrap();
```

### Parameters

| Parameter | What | Default | Guidance |
|-----------|------|---------|----------|
| `target` | Max acceptable sojourn time | Required | Set to your latency budget |
| `window` | Interval (ticks) | Required | How long sojourn must stay above target |
| `min_samples` | Warmup | 1 | Set to 10+ for noisy startup |

**Choosing target:** Your latency budget for queue wait time. If your
end-to-end budget is 100μs and processing takes 60μs, the queue budget
is 40μs. Set target to 40μs (40,000 ns).

**Choosing window:** How long a standing queue must persist before you
act. Shorter = faster detection, more false alarms from bursts. Longer =
more confident, slower response. 100ms-1s is typical.

## Examples by Domain

### Trading — Aeron Publication Backpressure

```rust
// Detect backpressure before Aeron buffers fill
let mut qd = CoDelI64::builder()
    .target(10_000)         // 10μs max queue wait
    .window(100_000_000)    // 100ms observation window
    .min_samples(20)
    .build().unwrap();

// At dequeue from ring buffer:
let sojourn_ns = now_ns - message.enqueue_timestamp;
match qd.update(now_ns as u64, sojourn_ns) {
    Some(Condition::Degraded) => {
        // Standing queue detected — slow down strategies
        throttle_strategies();
    }
    Some(Condition::Normal) => {
        // Queue is healthy
    }
    None => {} // not primed yet
}
```

### Networking — Request Queue Health

```rust
// Web server request queue monitoring
let mut qd = CoDelI64::builder()
    .target(5_000_000)       // 5ms max queue wait
    .window(10_000_000_000)  // 10s window
    .build().unwrap();

// On each request completion:
let wait_ms = request.started_processing - request.received;
if let Some(Condition::Degraded) = qd.update(now_ns, wait_ms) {
    shed_load();  // start rejecting requests
}
```

### Gaming — Command Queue Monitoring

```rust
// Detect when the render command queue backs up
let mut qd = CoDelI64::builder()
    .target(2_000)           // 2ms max command wait
    .window(100_000_000)     // 100ms window
    .build().unwrap();
```

## Composition Patterns

### CoDel + Saturation

"Comprehensive resource monitoring":

```rust
// CoDel catches standing queues (latency-based)
// Saturation catches high utilization (throughput-based)
let mut qd = CoDelI64::builder().target(t).window(w).build().unwrap();
let mut sat = SaturationF64::builder().alpha(0.1).threshold(0.8).build().unwrap();

// On dequeue:
let sojourn = now - enqueue_time;
let queue_pressure = qd.update(now, sojourn);
let util_pressure = sat.update(utilization);

match (queue_pressure, util_pressure) {
    (Some(Condition::Degraded), _) => { /* queue backing up */ }
    (_, Some(Condition::Degraded))     => { /* resource maxed out */ }
    _                                   => { /* healthy */ }
}
```

### CoDel + CUSUM

"Detect both transient backpressure and permanent degradation":

CoDel catches standing queues. CUSUM on the sojourn time detects
when the mean processing time has shifted (e.g., downstream got slower).

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `CoDelI64::update` | 7 cycles | 10 cycles |

One comparison against the target and one against the armed deadline per
update; no windowed minimum. The integer path avoids float conversion
entirely.

## Background: CoDel

CoDel (Controlled Delay) was developed by Kathleen Nichols and Van
Jacobson in 2012 for active queue management in network routers. The
key insight: **good queues** (transient bursts) have low minimum delay,
while **bad queues** (standing backlog) have high minimum delay.

CoDel's policy is to drop packets when the queue is "bad." CoDel
provides the measurement without imposing a policy — your system decides
what to do when pressure is elevated.

Reference: Nichols, K. and Jacobson, V. "Controlling Queue Delay."
*ACM Queue* 10.5 (2012): 20-34.

Linux kernel implementation: `include/net/codel_impl.h`
