# EMA — Exponential Moving Average

**First-order IIR low-pass filter.** Smooths a noisy signal by
exponentially weighting recent samples more heavily than older ones.

| Property | Value |
|----------|-------|
| Update cost | 5 cycles |
| Memory | ~24 bytes |
| Types | `Ema` |
| Priming | Configurable via `min_samples` |
| Output | `Option<f64>` — smoothed value once primed |

## What It Does

```
  Noisy signal vs EMA (alpha = 0.1):

  Value
  120 ┤      ·
  115 ┤  ·       ·              ·
  110 ┤    ·  ·      ·       ·     ·
  105 ┤ ·──────────────·──────────────·─────── EMA (smooth)
  100 ┤──·──·────·──·─────·──·──·──·──────·──
   95 ┤            ·        ·           ·
   90 ┤               ·
      └──────────────────────────────────────── t
            scattered dots = raw signal
            smooth line = EMA output

  Higher alpha (0.5) — more reactive, less smooth:

  Value
  120 ┤      ·
  115 ┤  · ╱─╲  ·              ·
  110 ┤   ╱    ╲    ·       ·╱──╲·
  105 ┤ ·╱      ╲·──────·──╱      ╲──── EMA
  100 ┤──         ╲·──·─────        ╲·──
   95 ┤            ╲    ·            ·
   90 ┤             ·
      └──────────────────────────────────────── t
```

Each update blends the new sample into the running average:

```
EMA = alpha × sample + (1 - alpha) × EMA
```

- **High alpha** (0.5-0.9) — reactive, tracks signal closely, more noise
- **Low alpha** (0.01-0.1) — smooth, lags behind signal, less noise

## When to Use It

**Use EMA when:**
- You need the simplest possible smoother
- The signal has consistent noise characteristics
- ~5 cycles per update is your budget

**Don't use EMA when:**
- Signal alternates between trending and noisy → use [KAMA](kama.md) (adapts alpha)
- You need different smoothing for rising vs falling → use [AsymmetricEMA](asym-ema.md)
- You need to chase a moving target without overshoot → use [Spring](spring.md)
- You need to remove outlier spikes, not smooth them → use [WindowedMedian](windowed-median.md)
- You need level + trend separation → use [Holt](holt.md)

## How It Works

The EMA is a weighted sum of all past samples, where weights decay
exponentially:

```
EMA_n = alpha × x_n + alpha(1-alpha) × x_{n-1} + alpha(1-alpha)² × x_{n-2} + ...
```

The parameter `alpha` controls the decay rate:

| Alpha | Effective window | Character |
|-------|-----------------|-----------|
| 0.01 | ~200 samples | Very smooth, slow to react |
| 0.05 | ~40 samples | Smooth, moderate lag |
| 0.1 | ~20 samples | Balanced |
| 0.2 | ~10 samples | Responsive, some noise |
| 0.5 | ~4 samples | Very reactive, noisy |

**First sample:** The first value initializes the EMA directly (no
smoothing). This avoids the "start from zero" bias.

## Configuration

Three ways to set the smoothing factor:

```rust
// Direct alpha
let ema = Ema::builder().alpha(0.1).build().unwrap();

// From halflife (samples for weight to decay by half)
let ema = Ema::builder().halflife(10.0).build().unwrap();

// From span (pandas/finance convention)
// alpha = 2 / (n + 1)
let ema = Ema::builder().span(20).build().unwrap();
```

### Integer Inputs

`Ema` is `f64` only. A fixed-point EMA of arbitrary data has no realistic
caller (the alpha is fractional, so integer arithmetic truncates every
update); cast integer samples at the call site. The integer tick types that
need a smoother (`Liveness`, `EventRate`, `Jitter<i64>`) carry their own
shift-based EMA internally.

### Parameters

| Parameter | What | Default | Guidance |
|-----------|------|---------|----------|
| `alpha` | Smoothing factor (0,1) | Must set | Start with 0.1, adjust |
| `halflife` | Samples to decay by half | Computes alpha | More intuitive than raw alpha |
| `span` | Span in samples (n >= 2) | Computes alpha | pandas `span`: alpha = 2/(n+1) |
| `min_samples` | Warmup before output | 1 | Set higher for noisy startup |

### Seeding

Skip warmup with a known baseline:

```rust
let ema = Ema::builder()
    .alpha(0.1)
    .seed(100.0)  // start from known value
    .build().unwrap();
assert_eq!(ema.value(), Some(100.0));
assert_eq!(ema.count(), 0);
```

A seed is a value, not samples: the EMA is primed at once (`min_samples` no
longer applies), `count()` still counts only samples fed, the first sample is
smoothed into the seed, and `reset()` returns to the seed.

## Examples by Domain

### Trading — Latency Smoothing

```rust
let mut latency_ema = Ema::builder()
    .span(50)         // ~50 sample smoothing
    .min_samples(20)
    .build().unwrap();

// On each round-trip:
if let Some(smoothed) = latency_ema.update(rtt_us) {
    dashboard.set_latency(smoothed);
}
```

### Networking — Throughput Estimation

```rust
let mut throughput = Ema::builder()
    .span(15)
    .min_samples(3)
    .build().unwrap();

// On each measurement interval:
let bytes_per_sec = bytes_received as f64 / interval_secs;
if let Some(smoothed) = throughput.update(bytes_per_sec) {
    adjust_quality(smoothed);
}
```

### Gaming — Frame Time Display

```rust
let mut frame_ema = Ema::builder()
    .alpha(0.05)  // very smooth for display
    .build().unwrap();

// Each frame:
if let Some(smoothed_dt) = frame_ema.update(frame_time_ms) {
    hud.set_fps(1000.0 / smoothed_dt);
}
```

### IoT — Sensor Smoothing

```rust
// Temperature sensor, 1 reading/second
let mut temp = Ema::builder()
    .halflife(30.0)   // 30-second halflife
    .min_samples(10)
    .build().unwrap();
```

### SRE — Error Rate Smoothing

```rust
let mut error_rate = Ema::builder()
    .span(100)  // smooth over ~100 observations
    .build().unwrap();

// On each request:
let is_error = response.status() >= 500;
error_rate.update(if is_error { 1.0 } else { 0.0 });
```

## Composition Patterns

### EMA + CUSUM

"Smooth the signal, detect when the smoothed value shifts":

```rust
let mut ema = Ema::builder().span(20).build().unwrap();
let mut cusum = Cusum::builder(baseline).slack(k).threshold(h).build().unwrap();

if let Some(smoothed) = ema.update(sample) {
    cusum.update(smoothed).unwrap();  // detect shifts in the smoothed signal
}
```

### EMA + AdaptiveThreshold

"Is this sample anomalous relative to the recent average?":

```rust
// AdaptiveThreshold uses EMA internally — this is built in.
// But if you want separate control:
let mut baseline = Ema::builder().span(100).build().unwrap();
let mut fast = Ema::builder().span(5).build().unwrap();

// Divergence between fast and slow EMA signals regime change
if let (Some(slow), Some(fast_val)) = (baseline.update(x), fast.update(x)) {
    if (fast_val - slow).abs() > threshold {
        // significant divergence
    }
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Ema::update` | 5 cycles | 6 cycles |

`update` is one multiply-add (a fused FMA instruction when the target has
`+fma`, else `a * b + c`) plus the priming count.

## Academic Reference

The exponential moving average is a special case of the infinite impulse
response (IIR) filter. In signal processing terms, it's a first-order
low-pass filter with transfer function `H(z) = alpha / (1 - (1-alpha)z⁻¹)`.

The cutoff frequency (in normalized units) is approximately:
`f_c = alpha / (2π(1-alpha))`.

Roberts, S.W. "Control Chart Tests Based on Geometric Moving Averages."
*Technometrics* 1.3 (1959): 239-250.

The kernel-style fixed-point EMA is documented in the Linux kernel source:
`include/linux/average.h`.
