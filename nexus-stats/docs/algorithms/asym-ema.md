# AsymmetricEMA — Different Alpha for Rising vs Falling

**EMA with different smoothing factors for each direction.** "Increase
fast, decrease slow" — or vice versa.

| Property | Value |
|----------|-------|
| Update cost | 11 cycles |
| Memory | ~16 bytes |
| Types | `AsymEma` |
| Priming | Configurable via `min_samples` |
| Output | `Option<T>` — smoothed value once primed |

## What It Does

```
  Standard EMA (symmetric):        AsymmetricEMA (fast up, slow down):

  Value                            Value
  ──·──·──                         ──·──·──
  100 ┤────────── baseline         100 ┤────────── baseline
   80 ┤  ╲    ╱   symmetric        80 ┤  ╲╲  ╱╱  fast rise,
   60 ┤    ╲╱     response         60 ┤    ╲╱     slow decline
      └──────────── t                  └──────────── t
```

The Linux kernel uses this exact pattern for TCP RTT variance estimation:
variance grows quickly (detecting degradation fast) but shrinks slowly
(maintaining conservative timeout estimates).

## When to Use It

- RTT / latency estimation: react fast to increases, slow to decreases
- Load tracking: detect spikes fast, don't release capacity too quickly
- Capacity planning: ramp up fast, scale down slowly

## Configuration

```rust
let mut ema = AsymEma::builder()
    .alpha_up(0.3)     // fast response to increases
    .alpha_down(0.05)  // slow response to decreases
    .min_samples(5)
    .build().unwrap();
```

Or using spans:
```rust
let mut ema = AsymEma::builder()
    .span_up(5)    // ~5-sample response on increases
    .span_down(40) // ~40-sample response on decreases
    .build().unwrap();
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `AsymEma::update` | 11 cycles | 11 cycles |

One branch (rising vs falling) + one `mul_add`. The branch is
well-predicted for signals with consistent direction.

## Background

Jacobson, V. and Karels, M. "Congestion Avoidance and Control."
*ACM SIGCOMM* (1988). — Introduces asymmetric RTT variance tracking.
Linux kernel implementation: `net/ipv4/tcp_input.c`, `tcp_rtt_estimator()`.
