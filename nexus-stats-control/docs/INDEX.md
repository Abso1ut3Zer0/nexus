# nexus-stats-control Documentation

Advanced control and frequency primitives that build on top of the base control primitives in [`nexus-stats-core::control`](../../nexus-stats-core/docs/control.md).

This crate has two submodules:

- `control` — `PeakDetector`, `BoolWindow`.
- `frequency` — `TopK`, `FlexProportion`, `DecayAccum`.

The base control primitives (`DeadBand`, `Hysteresis`, `Debounce`, `LevelCrossing`, `FirstDiff`, `SecondDiff`) live in `nexus-stats-core::control`, not here. See [that doc](../../nexus-stats-core/docs/control.md) for those.

## Start Here

- [Overview](overview.md) — What this crate provides, feature flags, relationship to `nexus-stats-core::control`.
- [PeakDetector](peak-detector.md) — Local maxima / minima with prominence filtering.
- [BoolWindow](bool-window.md) — Rolling pass/fail rate over a fixed-count window.
- [TopK](topk.md) — Space-Saving top-K frequent-items tracker.
- [FlexProportion](flex-proportion.md) — Per-entity fraction tracking.
- [DecayAccum](decay-accum.md) — Event-driven score with time decay.

## Algorithms

| Type | Module | Feature | Detects / Tracks |
|------|--------|---------|-------------------|
| `PeakDetector<f64>` / `PeakDetector<i64>` | `control` | — | Local maxima above a prominence threshold |
| `BoolWindow` | `control` | `alloc` | Rolling pass/fail fraction |
| `TopK<K>` | `frequency` | `alloc` | Top-K frequent items (Space-Saving) |
| `FlexProportionGlobal` + `FlexProportionEntity` | `frequency` | — | Per-entity share of a streaming count |
| `DecayAccum` | `frequency` | — | Score that decays with time between events |

## Cross-references

- Base control / thresholds: [`nexus-stats-core::control`](../../nexus-stats-core/docs/control.md).
- Rolling rates with smoothing: [`nexus-stats-core::monitoring::EventRate`](../../nexus-stats-core/docs/monitoring.md#eventrate).
- Bayesian rate with uncertainty: [`BetaBinomial`](../../nexus-stats-regression/docs/estimation.md#betabinomial--bayesian-rate-estimation-for-successes).
- Umbrella: [`nexus-stats/docs`](../../nexus-stats/docs/INDEX.md).
