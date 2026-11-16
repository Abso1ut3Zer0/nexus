# ErrorRate — Failure Rate Tracking

**EMA of success/failure outcomes.** Supports weighted severity.

| Property | Value |
|----------|-------|
| Update cost | 7 cycles |
| Memory | ~32 bytes |
| Types | `ErrorRate` |
| Output | `Option<Condition>` — `Normal` or `Degraded` |

## What It Does

```
  Outcomes over time (✓=success, ✗=failure):

  ✓ ✓ ✓ ✓ ✗ ✓ ✓ ✗ ✗ ✓ ✗ ✗ ✗ ✓ ✓ ✓ ✓ ✓ ✓ ✓

  Smoothed error rate (EMA):
  0.05 ┤──────╱
  0.10 ┤     ╱  ╲
  0.20 ┤    ╱    ╲──╱─╲
  0.30 ┤   ╱          ╲── threshold
  0.40 ┤                  ╲╲
  0.20 ┤                    ╲──────── recovers
       └──────────────────────────── t
       Healthy │ Degraded │ Healthy
```

Each outcome (success/failure) feeds the EMA as 0.0 or 1.0. The smoothed
value is the recent error rate (0.0 to 1.0). When it exceeds the threshold,
status changes to `Degraded`.

**Weighted outcomes:** `record_weighted(false, 3.0)` counts a failure as 3×
severity. Useful when not all errors are equal (timeout vs rejection vs crash).

## Configuration

```rust
let mut er = ErrorRate::builder()
    .span(100)          // smooth over ~100 outcomes
    .threshold(0.05)    // degraded above 5% error rate
    .build().unwrap();

// Simple binary:
er.update(request_succeeded);

// Weighted:
er.update_weighted(false, severity_score).unwrap();

if let Some(Condition::Degraded) = er.update(false) {
    trip_circuit_breaker();
}
```

## When to Use Something Else

- Count-based failure rate (last N events) → [BoolWindow](bool-window.md)
- N consecutive failures → [Debounce](debounce.md)

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `ErrorRate::update` | 7 cycles | 9 cycles |
