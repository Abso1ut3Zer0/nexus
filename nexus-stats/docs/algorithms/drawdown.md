# Drawdown — Peak-to-Trough Decline Tracking

**Tracks peak value and current/maximum drawdown.** Core risk metric
for circuit breakers.

| Property | Value |
|----------|-------|
| Update cost | 6 cycles |
| Memory | ~24 bytes |
| Types | `Drawdown<f64>`, `Drawdown<i64>` |
| Output | Current drawdown value |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

```
  Value
  100 ┤──────────┐
   90 ┤          │  peak = 100
   80 ┤          │╲
   70 ┤          │  ╲────╱╲
   60 ┤          │        ╲──── drawdown = 40 (peak - current)
      │          │
      │  max_drawdown = 40 (worst ever observed)
      └──────────────────────────────────────── t
```

Tracks three values: peak (highest value seen), current drawdown
(peak - last sample), and maximum drawdown (worst drawdown ever).

## When to Use It

- Risk circuit breaker: "halt if PnL drops $X from peak"
- High-water mark tracking for fee calculation
- Maximum adverse excursion analysis

## Configuration

```rust
let mut dd = Drawdown::<f64>::new();

dd.update(100.0).unwrap();  // peak = 100, drawdown = 0
dd.update(90.0).unwrap();   // peak = 100, drawdown = 10
dd.update(95.0).unwrap();   // peak = 100, drawdown = 5
dd.update(60.0).unwrap();   // peak = 100, drawdown = 40

assert_eq!(dd.max_drawdown(), 40.0);

dd.update(110.0).unwrap();  // NEW peak = 110, drawdown = 0
```

Zero config — just create and update. Implements `Default`.

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Drawdown::<f64>::update` | 6 cycles | 6 cycles |

One comparison + one conditional update. Pure arithmetic.
