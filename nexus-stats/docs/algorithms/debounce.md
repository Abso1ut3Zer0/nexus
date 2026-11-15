# Debounce — N Consecutive Events Before Triggering

**Requires N consecutive positive signals before reporting true.**
A single negative resets the counter. From AUTOSAR diagnostic standards.

| Property | Value |
|----------|-------|
| Update cost | 5 cycles |
| Memory | ~16 bytes |
| Types | `Debounce` |
| Output | `bool` — true once threshold reached |

## What It Does

```
  Input:    T  T  T  F  T  T  T  T  T     (T=active, F=inactive)
  Counter:  1  2  3  0  1  2  3  4  5
  Output:   .  .  .  .  .  .  .  .  ✓     (threshold = 5)

  The single F at position 4 resets everything.
  Must see 5 consecutive T to trigger.
```

## When to Use It

**Use Debounce when:**
- "3 consecutive timeouts = connection dead"
- "5 consecutive sensor faults = real problem, not noise"
- You want confirmation before acting on a state change

**Not the same as:**
- [CUSUM](cusum.md) — detects drift in continuous signals, not discrete events
- [BoolWindow](bool-window.md) — tracks failure *rate* over a window, not consecutive count
- [Liveness](liveness.md) — time-based silence detection, not event counting

## Configuration

```rust
let mut db = Debounce::new(3).unwrap();  // need 3 consecutive actives

db.update(true);   // 1 — false
db.update(true);   // 2 — false
db.update(true);   // 3 — TRUE (triggered!)
db.update(false);  // 0 — reset
db.update(true);   // 1 — false (starts over)
```

## Examples

### Trading — Connection Dead Detection
```rust
let mut timeout_debounce = Debounce::new(3).unwrap();
if timeout_debounce.update(request_timed_out) {
    failover_to_backup();
}
```

### IoT — Sensor Fault Confirmation
```rust
let mut fault = Debounce::new(5).unwrap();
if fault.update(reading_out_of_range) {
    raise_alarm();
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Debounce::update` | 5 cycles | 5 cycles |

One increment + one comparison. Perfectly predicted branch.
