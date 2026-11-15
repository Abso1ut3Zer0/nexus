# nexus-stats-smoothing Documentation

Advanced smoothing and filtering primitives that complement the base EMA / AsymEma / Slew types in [`nexus-stats-core`](../../nexus-stats-core/docs/INDEX.md).

All types follow the ecosystem conventions: O(1) per update, fixed memory, no allocation on the hot path (after construction), `update(sample) -> Result<(), DataError>` for scalar inputs, `is_primed()` / `count()` / `reset()` for state queries.

## Start Here

- [Overview](overview.md) — What this crate provides, when to pick it, feature flags.
- [Choosing a Smoother](choosing.md) — EMA vs Holt vs KAMA vs Kalman1d vs Spring vs Hampel.
- [Parameter Tuning](parameter-tuning.md) — Alpha, half-life, window size, how to pick them.

## Algorithms

| Page | Types | Use When |
|------|-------|----------|
| [Holt](holt.md) | `Holt` | Signal has a trend (drift) you want separated from the level. |
| [KAMA](kama.md) | `Kama` | Trending markets you need to follow aggressively, ranging markets you need to smooth heavily. |
| [Kalman1d](kalman1d.md) | `Kalman1d` | You have an observation-noise model and want optimal position + velocity estimates. |
| [Spring](spring.md) | `Spring` | UI / animation / chase targets without overshoot. |
| [HuberEMA](huber-ema.md) | `HuberEma` | EMA but with per-step bounded influence — robust to outliers without throwing data away. |
| [Hampel](hampel.md) | `Hampel` | Three-zone outlier filter — pass, Winsorize, or reject based on MAD distance. |
| [ConditionalEMA](conditional-ema.md) | `ConditionalEma` | EMA that only updates when a side-condition (e.g. "queue non-empty") is true. |
| [WindowedMedian](windowed-median.md) | `WindowedMedian<f64>` / `WindowedMedianF32` | Robust median over a fixed-size sliding window. |

## Cross-References

- For the base EMA, AsymEMA, and SlewLimiter — see [`nexus-stats-core::smoothing`](../../nexus-stats-core/docs/smoothing.md).
- For deeper algorithmic background, the umbrella docs at [`nexus-stats/docs`](../../nexus-stats/docs/INDEX.md) contain long-form explanations per algorithm.
- For change detection on the smoothed signal — see [`nexus-stats-detection`](../../nexus-stats-detection/docs/INDEX.md).
