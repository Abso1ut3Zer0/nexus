# KAMA — Kaufman Adaptive Moving Average

**EMA that adapts its smoothing factor to market conditions.** Fast
response when trending, heavy smoothing when noisy. Used by quant shops.

| Property | Value |
|----------|-------|
| Update cost | 14 cycles (window 10) |
| Memory | ~N×8 bytes (lookback buffer) |
| Types | `Kama` |
| Requires | `alloc` feature (runtime window size) |
| Priming | After N samples |
| Output | `Option<T>` — smoothed value once primed |

## What It Does

```
  Trending signal:                   Noisy signal:
  efficiency ratio ≈ 1.0             efficiency ratio ≈ 0.0

  Value                              Value
  120 ┤              ·               120 ┤  ·     ·     ·
  115 ┤           ·                  115 ┤     ·     ·
  110 ┤        ·                     110 ┤  ·     ·
  105 ┤     ·                        105 ┤     ·     ·     ·
  100 ┤──·───────── KAMA tracks      100 ┤──·──·──·──────── KAMA barely moves
      └────────────── t                   └────────────── t
      α → fast (responsive)              α → slow (smooths heavily)
```

The **efficiency ratio** measures how efficiently the signal is moving:

```
direction  = |price_now - price_N_ago|       (net movement)
volatility = sum(|price_i - price_{i-1}|)    (total path length)
ER = direction / volatility                  (0 to 1)
```

- **ER ≈ 1.0** — signal is trending (straight line). KAMA responds fast.
- **ER ≈ 0.0** — signal is noisy (random walk). KAMA smooths heavily.

## When to Use It

**Use KAMA when:**
- Signal alternates between trending and mean-reverting
- Fixed alpha EMA is either too slow (misses trends) or too noisy (amplifies noise)
- You want one primitive that adapts to regime changes

**Don't use KAMA when:**
- Signal has consistent noise characteristics → [EMA](ema.md) is simpler
- You need direction detection → use [TrendAlert](trend-alert.md) or [Holt](holt.md)
- You need the absolute cheapest smoother → EMA at ~5 cycles vs KAMA at ~16

## Configuration

```rust
let mut kama = Kama::builder()
    .window_size(10)  // ER lookback window
    .fast_span(2)     // alpha when ER=1 (very reactive)
    .slow_span(30)    // alpha when ER=0 (very smooth)
    .min_samples(10)
    .build().unwrap();
```

### Parameters

| Parameter | What | Default | Guidance |
|-----------|------|---------|----------|
| `window_size` | ER lookback window | Required | 10-20 typical |
| `fast_span` | EMA span when trending | 2 | Lower = more reactive at ER=1 |
| `slow_span` | EMA span when noisy | 30 | Higher = smoother at ER=0 |

## Examples

### Trading — Adaptive Price Smoothing
```rust
let mut price_kama = Kama::builder()
    .window_size(10)
    .fast_span(2)
    .slow_span(30)
    .build().unwrap();

if let Some(smoothed) = price_kama.update(mid_price).unwrap() {
    // Tracks trends closely, filters noise
}

// Check current regime:
if let Some(er) = price_kama.efficiency_ratio() {
    if er > 0.7 { /* trending */ }
    else { /* noisy / mean-reverting */ }
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Kama::update` (window=10) | 14 cycles | 14 cycles |

O(N) volatility recompute per update. For N=10, that's 9 subtractions
+ absolute values. Negligible for typical window sizes.

## Academic Reference

Kaufman, P.J. *Trading Systems and Methods.* Chapter on adaptive techniques.
Originally published in *Smarter Trading* (1995).
