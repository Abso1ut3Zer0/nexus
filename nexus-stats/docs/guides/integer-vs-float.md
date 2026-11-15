# Integer vs Float Variants

When to use which numeric type.

## Decision Tree

```
Is your data naturally integer (nanoseconds, ticks, counts)?
  ├─ Yes → does the algorithm have an integer variant?
  │   ├─ Yes → use it (EmaI64, CusumI64, etc.)
  │   └─ No → convert to f64 on input
  └─ No → use float (Ema, Welford, etc.)
```

## Integer Advantages

- **No floating-point unit needed** (embedded, kernel)
- **Deterministic** — no rounding differences across platforms
- **Often faster** — EmaI64 uses bit-shifts instead of multiply

## Integer Limitations

- **EMA weight is quantized** to powers of 2 (span rounds to 2^k - 1)
- **No division-based algorithms** (Welford, Kalman, Covariance, Holt)
- **Potential overflow** for large accumulations (i64 is usually fine)

## Float Advantages

- **All algorithms available** — division and transcendentals work
- **Fine-grained alpha** — any value in (0, 1), not just powers of 2
- **Standard for scientific/financial computation**

## Float Limitations

- **Non-deterministic** across platforms (IEEE 754 allows flexibility)
- **Requires FPU** (or software float on embedded)
- **NaN/Inf propagation** if input is corrupted

## Practical Guidance

| Domain | Recommendation |
|--------|---------------|
| Latency (nanoseconds) | `i64` for EMA/CUSUM, `f64` for Welford/Kalman |
| Prices | `f64` (prices are inherently fractional) |
| Counts | `i64` for simple tracking, `f64` if you need variance |
| Utilization (0-100%) | `f64` (ratio, needs float precision) |
| Timestamps | `i64` (nanoseconds since epoch) |
