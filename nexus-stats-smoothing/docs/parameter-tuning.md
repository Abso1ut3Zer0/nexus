# Parameter Tuning

This page covers the practical question "what numbers do I put in the constructor?".

## Alpha vs Half-Life

Most smoothers in this crate take an `alpha` in `(0, 1]`. Alpha is *not* intuitive — half-life is.

Half-life = "how many samples until the weight on an observation has halved".

Conversion:

```
alpha    = 1 - exp(-ln(2) / half_life)
half_life = ln(2) / -ln(1 - alpha)
```

Reference table:

| half_life (samples) | alpha   |
|---------------------|---------|
| 2                   | 0.2929  |
| 5                   | 0.1294  |
| 10                  | 0.0670  |
| 20                  | 0.0341  |
| 50                  | 0.0138  |
| 100                 | 0.00691 |
| 500                 | 0.00139 |
| 1000                | 0.00069 |

A helper:

```rust
#[inline]
fn alpha_from_half_life(half_life: f64) -> f64 {
    1.0 - (-core::f64::consts::LN_2 / half_life).exp()
}
```

Use this at construction — don't reach for it on the hot path.

## Choosing Half-Life by Workload

| Workload | Typical half-life (samples) |
|----------|------------------------------|
| Per-packet latency (10us-100us ticks) | 50-500 |
| Per-order fill rate (market making) | 20-200 |
| Per-second throughput | 10-60 |
| Per-minute error rate | 5-30 |
| Market mid-price (HFT) | 50-1000 |
| P&L baseline | 1000-10000 |
| Slow drift baseline | 10000+ |

Rule of thumb: pick a half-life at the timescale of the phenomenon you care about, not the sample rate. If you care about "10-second bursts" and samples arrive 100x/sec, half-life ~ 500-1000.

## Holt: Alpha and Beta

Holt has two parameters: `alpha` (level) and `beta` (trend). Rules:

- Start `alpha` at the same value you'd use for a plain EMA on this data.
- Start `beta` at `alpha / 5`. Trend estimates need to be slower than level estimates or they oscillate.
- If the forecast overshoots, reduce `beta`.
- If the level lags, increase `alpha`.

Worked example: 1Hz sensor, you want 10-second level responsiveness, 1-minute trend stability:

```
alpha_half_life = 10 samples  -> alpha ~ 0.067
beta_half_life  = 60 samples  -> beta  ~ 0.012
```

## KAMA: Window, Fast, Slow

KAMA takes three parameters:

- `window` — efficiency lookback (samples). 10 is classic; 5 for fast assets, 20 for slow.
- `fast` — half-life when market is efficient (trending). 2 is classic.
- `slow` — half-life when market is inefficient (ranging). 30 is classic.

These come from Kaufman's original paper. `window=10, fast=2, slow=30` is your default. Increase `slow` if the ranging output is still too jittery; decrease `fast` if the trending output lags.

## Kalman1d: Process Noise and Measurement Noise

Three parameters:

- `process_noise` (q) — how fast the true state can drift between samples. Bigger = filter tracks change faster, but responds more to measurement noise.
- `measurement_noise` (r) — noise variance on observations. Calibrate this from a stationary period: run `Welford` on residuals and use `.variance()`.
- `initial_variance` (p0) — initial uncertainty. Big number is safe; the filter converges quickly.

Tuning intuition: the filter doesn't care about q and r individually, only the ratio q/r. Bigger ratio = more responsive. Smaller ratio = more smoothing. If both are wild guesses, fix `r = 1.0` and sweep `q` from 0.001 to 10 until you like the output.

## Spring: Smooth Time

One parameter, `smooth_time`, in the same units as the `dt` you pass to
`update`. It is the time scale of convergence: the spring closes most of the
gap to its target within about `smooth_time`, and larger values are slower
and smoother. Example:

```rust
let mut spring = Spring::new(0.5).unwrap();            // 0.5 s smooth time
let shown = spring.update(target, dt_seconds).unwrap();  // each frame: target and elapsed time
let pos = spring.value();                                // current position, no update
```

Critically damped, so it *never* overshoots regardless of `smooth_time`.

## Huber EMA: Threshold

`HuberEma::new(alpha, threshold, sigma)`:

- `alpha` — same as regular EMA.
- `threshold` — in multiples of `sigma`. Typically 1.5-3.0.
- `sigma` — scale for the quadratic-linear boundary. Use current running stddev (from `EwmVar`) or a calibration constant.

A threshold of 1.5 means "steps larger than 1.5 sigma get capped". Start at 2.0 and adjust.

## Hampel: Window, k (MAD multiplier), Winsorize threshold

`Hampel::new(window, k_winsorize, k_reject)`:

- `window` — sliding window size. 11 is classic (5 on each side + center).
- `k_winsorize` — MAD multiplier for "Winsorize zone". Typically 3.0.
- `k_reject` — MAD multiplier for "reject zone". Typically 6.0.

Under pure Gaussian noise, `k=3` MAD ≈ 2 sigma and `k=6` MAD ≈ 4 sigma.

## Windowed Median: Window

`WindowedMedian::<f64>::new(window)`. Odd `window` values are conventional (5, 11, 21, 51). Bigger window = more robust, more lag. At 50% corruption, up to `window/2 - 1` bad samples in the window don't affect the output.

## Testing Your Parameters

Two things to always check:

1. **Lag.** Feed a step function: `[0, 0, 0, 0, 1, 1, 1, 1, ...]`. Count how many samples until the output is >0.9. If that's more than 2x your chosen half-life, something is miscalibrated.

2. **Noise rejection.** Feed a constant with additive Gaussian noise. Measure output stddev. Compare to input stddev. Ratio tells you the effective smoothing.

If you can't decide between two parameter sets, plot both on real data. Your eyes will tell you.
