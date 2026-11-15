# Overview

`nexus-stats-control` collects the advanced control and frequency-counting primitives of the nexus-stats ecosystem. It is smaller than the other subcrates because the *basic* control primitives (DeadBand, Hysteresis, Debounce, LevelCrossing, FirstDiff, SecondDiff) live in [`nexus-stats-core::control`](../../nexus-stats-core/docs/control.md).

## What's in here

- **PeakDetector** — detects local maxima (or minima) with a prominence threshold.
- **BoolWindow** — rolling pass/fail rate over a fixed-count sliding window.
- **TopK** — Space-Saving top-K frequent items tracker (approximate, O(K) memory).
- **FlexProportion** — per-entity fraction-of-total tracker (for leaderboards, load shares).
- **DecayAccum** — event-driven score that exponentially decays with real time between events.

These all share the ecosystem conventions: O(1) update, fixed memory after construction, no allocation on the hot path.

## Feature Flags

| Feature | Effect | Default |
|---------|--------|---------|
| `std` | Enables standard library integration. | Yes |
| `libm` | `no_std` math fallback. | No |
| `alloc` | Enables `TopK`, `BoolWindow`. | Yes via std |

`PeakDetector`, `FlexProportion`, and `DecayAccum` work in strict `no_std` without `alloc`.

## no_std

PeakDetector, FlexProportion, and DecayAccum can be used in a bare-metal `no_std` build. BoolWindow needs an allocated window buffer (hence `alloc`). TopK's counter map requires `alloc`.

## Performance

- **PeakDetector**: O(1) per sample, tens of cycles.
- **BoolWindow**: O(1) per update (bitmask over a fixed window).
- **TopK**: Space-Saving algorithm — O(K) memory, O(log K) per update.
- **FlexProportion**: O(1) per update, integer arithmetic.
- **DecayAccum**: O(1) per update including the exp decay.

## Relationship to `nexus-stats-core::control`

Think of `nexus-stats-core::control` as "pointwise decisions" and this crate as "aggregate / higher-level detection":

| Crate | Type | Answers |
|-------|------|---------|
| core | `DeadBand<f64>` | "Is this change big enough to act on?" |
| core | `Hysteresis<f64>` | "Am I in the hot zone, with flap protection?" |
| core | `DebounceU32` | "Have I had N consecutive triggers?" |
| core | `LevelCrossing<f64>` | "Did I cross this threshold?" |
| core | `FirstDiff<f64>` | "What's the velocity?" |
| control | `PeakDetector<f64>` | "Where are the local maxima?" |
| control | `BoolWindowF64` | "What fraction of the last N were true?" |
| control | `TopK<K>` | "Who are the heavy hitters?" |
| control | `FlexProportion` | "What's entity X's share?" |
| control | `DecayAccum` | "What's this entity's decaying score?" |

## Cross-references

- [`nexus-stats-core::control`](../../nexus-stats-core/docs/control.md) — base control primitives.
- [`nexus-stats-core::monitoring`](../../nexus-stats-core/docs/monitoring.md) — rate and health tracking.
- [`nexus-stats-detection`](../../nexus-stats-detection/docs/INDEX.md) — anomaly and change detection.
