# Liveness — Source Alive/Dead Detection

**EMA of inter-arrival times with deadline threshold.** Detects when a
data source goes quiet.

| Property | Value |
|----------|-------|
| Update cost | ~6 cycles |
| Memory | ~32 bytes |
| Types | `LivenessI64`, `LivenessU64` |
| Output | `bool` — true = alive, false = dead |

## What It Does

```
  Events arriving with inter-arrival times:

  ──┤──┤──┤──┤──┤──┤──┤──────────────────┤──┤──┤──
  10 10 10 10 10 10 10         80          10 10 10
                              ↑
                     gap exceeds deadline
                     check(now) returns false

  Smoothed interval (EMA):
  10 10 10 10 10 10 10  slowly rises...  drops back
                              ↑
                        deadline_multiple × smoothed > actual gap
```

Two methods:
- **`update(timestamp)`** — call when data arrives. Updates the EMA.
- **`check(now)`** — call periodically (e.g., from a timer). Returns false
  if time since last event exceeds the deadline. This is how you detect
  *silence* — `update()` can't fire if nothing arrives.

## Configuration

```rust
let mut live = LivenessU64::builder()
    .span(20)                  // EMA smoothing of intervals
    .deadline_multiple(5)      // dead if gap > 5× smoothed interval
    .min_samples(5)
    .build().unwrap();

// On each event:
live.update(now);

// On timer tick (must call periodically!):
if !live.check(now) {
    handle_source_dead();
}
```

### Deadline modes

- **`deadline_multiple(n)`** — adaptive: dead when `gap > n × smoothed_interval`
- **`deadline_absolute(t)`** — fixed: dead when `gap > t`

## Examples

### Trading — WebSocket Feed Health
```rust
let mut feed = LivenessI64::builder()
    .span(15)
    .deadline_multiple(5)
    .build().unwrap();

// On each market data message:
feed.update(now_ns);

// On 100ms timer (nexus-rt timer driver):
if !feed.check(now_ns) {
    reconnect_feed();
}
```

### Networking — Heartbeat Monitoring
```rust
let mut heartbeat = LivenessU64::builder()
    .deadline_absolute(30)    // 30 seconds absolute timeout
    .build().unwrap();
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `LivenessU64::update` | 6 cycles | 20 cycles |
| `LivenessU64::check` | ~3 cycles | ~3 cycles |

`update()` includes one EMA update. `check()` is one subtraction +
one comparison.
