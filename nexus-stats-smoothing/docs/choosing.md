# Choosing a Smoother

The #1 question for this crate is "which smoother, with what parameters?". Here's a decision tree.

## Is the raw signal noisy but stationary (mean-reverting around a level)?

Use **`Ema`** from `nexus-stats-core::smoothing`. It's the cheapest primitive and usually the right answer. Pick a half-life: your alpha is then `1 - exp(-ln(2) / half_life_samples)`. Typical half-lives: 5-50 samples for "noisy latency", 100-1000 samples for "market mid-price", 10k+ for "long-run baseline".

Only move off of EMA if one of the following is true.

## Does the signal have a *trend* you want to estimate?

Then mean-reverting assumption is wrong — EMA will lag the trend. Use **`Holt`**. Holt maintains `level` and `slope` estimates separately; `forecast(h)` gives you a look-ahead. Alpha tunes level responsiveness, beta tunes trend responsiveness.

Caveat: tuning two parameters is harder than tuning one. Start with alpha ~ 0.1, beta ~ 0.01, then adjust.

See [holt.md](holt.md).

## Does the signal alternate between "trending" and "ranging" regimes?

KAMA is designed for exactly this. It measures efficiency (|net change| / sum of |step changes|) over a lookback window and smooths more aggressively in choppy regimes, less aggressively in trending regimes.

Use **`Kama`** when you have a fixed window size you're comfortable with and don't want to hand-tune between "responsive" and "smooth".

See [kama.md](kama.md).

## Do you have an *observation noise model* and want optimal estimates?

Use **`Kalman1d`**. It gives you position + velocity with formal optimality under Gaussian noise. You provide process noise (how fast the true state drifts) and measurement noise (how bad your sensor is), and the filter computes the optimal Kalman gain on every step.

This is the right choice when you actually know (or can estimate) the noise magnitudes — e.g. from a calibration run, or from `EwmaVar` over recent residuals. When you don't know them and you're just picking magic numbers, a `Holt` will give you 90% of the benefit with half the conceptual overhead.

See [kalman1d.md](kalman1d.md).

## Do you want to chase a *target* (that changes) smoothly, without overshoot?

Use **`Spring`**. This is the critically-damped spring. You push a target, the spring chases it, and it's guaranteed not to overshoot. Tune by setting a half-life (time for distance-to-target to halve).

This is the right smoother for UI animations, slew-limited setpoints, and "target follower" control loops. It is *not* a statistical smoother — there's no noise model.

See [spring.md](spring.md).

## Do you want an EMA, but some samples are outliers you don't trust?

Three choices, in order of increasing aggressiveness:

1. **`HuberEma`** — EMA with a Huber-bounded step. Outliers still contribute, but their influence is capped at `threshold * sigma`. Best when "mostly clean data with occasional shocks".

2. **`Hampel`** — Three-zone filter: close values pass through, medium outliers are Winsorized to the window boundary, far outliers are rejected entirely. Best when you have a clear notion of "obvious garbage" vs "real signal".

3. **`WindowedMedian<f64>`** — Hard median over a fixed window. Completely ignores up to 50% corrupted inputs. Use this when the data can be arbitrarily bad (sensor flakes, exchange glitches, dirty network).

A common pattern: `WindowedMedian` → `EMA` to get the best of both.

See [huber-ema.md](huber-ema.md), [hampel.md](hampel.md), [windowed-median.md](windowed-median.md).

## Do you only want to update the smoother when some condition holds?

Use **`ConditionalEma`** — e.g. "update this fill-rate EMA only when an order was placed", "update this latency EMA only when the queue wasn't empty". Avoids poisoning the average with idle-time zero samples.

See [conditional-ema.md](conditional-ema.md).

## Still not sure?

Start with `Ema` from `nexus-stats-core`. If the output lags badly on trends, move to `Holt`. If the output is wrecked by outliers, move to `HuberEma`. If you *need* velocity, move to `Kalman1d`. Don't pick something clever if a cheap EMA solves the problem.

## Side-by-side Example

Here's the same noisy-with-trend input fed through several smoothers:

```rust
use nexus_stats_core::smoothing::Ema;
use nexus_stats_smoothing::{Holt, Kama, Kalman1d};

let samples: [f64; 8] = [100.0, 100.5, 101.2, 102.0, 102.8, 103.9, 105.1, 106.5];

let mut ema    = Ema::new(0.2);
let mut holt   = Holt::builder().alpha(0.4).beta(0.2).build().unwrap();
let mut kama   = Kama::builder()
    .window_size(10).fast_span(2).slow_span(30)
    .build().unwrap();
let mut k1d    = Kalman1d::builder()
    .process_noise(0.01).measurement_noise(1.0)
    .build().unwrap();

for &s in &samples {
    ema.update(s).unwrap();
    holt.update(s).unwrap();
    kama.update(s).unwrap();
    k1d.update(s).unwrap();
    println!(
        "raw={:.2} ema={:.2} holt={:.2} kama={:.2} k1d={:.2}",
        s,
        ema.value().unwrap_or(s),
        holt.value().unwrap_or(s),
        kama.value().unwrap_or(s),
        k1d.position(),
    );
}
```

Expect: `EMA` lags, `Holt` catches up faster due to trend, `KAMA` adapts to efficiency, `Kalman1d` tracks position+velocity. Run it yourself — intuition for parameter tuning comes from seeing the lines plotted.
