# BoolWindow — Sliding Pass/Fail Rate

**Ring buffer of boolean outcomes with running count.** "4 of the last
10 requests failed." Circuit breaker input signal.

| Property | Value |
|----------|-------|
| Update cost | 6 cycles |
| Memory | ~N/8 bytes + counter |
| Types | `BoolWindow` |
| Requires | `alloc` feature |
| Output | Failure rate (0.0 to 1.0) |

## What It Does

```
  Events:   ✓ ✓ ✓ ✗ ✓ ✓ ✗ ✗ ✓ ✓  (✓=success, ✗=failure)
  Bits:     0 0 0 1 0 0 1 1 0 0
  Failures: 3 out of 10 = 30% failure rate

  Next event (✓): evicts oldest, inserts new
  Bits:     0 0 1 0 0 1 1 0 0 0
  Failures: 2 out of 10 = 20% (oldest failure fell off)
```

Internally uses a `Vec<u64>` bitfield. For 64 events, one u64 word.
For 128 events, two words. Failure count is maintained incrementally —
no popcount needed per query.

## When to Use It

- Circuit breaker input: "trip when failure rate > 50% over last 20 requests"
- Quality scoring: "success rate over a rolling window"
- Different from [ErrorRate](error-rate.md): BoolWindow is count-based
  (last N events), ErrorRate is time-decayed (EMA)

## Configuration

```rust
let mut window = BoolWindow::new(64).unwrap();  // track last 64 events

window.update(true);   // success
window.update(false);  // failure

let rate = window.failure_rate();  // 0.0 to 1.0
let count = window.count();        // events seen so far (up to 64)
```

## Examples

### Circuit Breaker Input
```rust
let mut outcomes = BoolWindow::new(20).unwrap();  // last 20 requests

outcomes.update(request_succeeded);

if outcomes.failure_rate() > 0.5 && outcomes.count() >= 10 {
    trip_circuit_breaker();
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `BoolWindow::update` | 6 cycles | 6 cycles |

Bit shift + OR + mask for the window rotation. Incremental failure
count: subtract evicted bit, add new bit. No popcount on query.
