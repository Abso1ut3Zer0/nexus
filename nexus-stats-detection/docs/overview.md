# Overview

`nexus-stats-detection` collects the advanced change-detection and signal-analysis types from the nexus-stats ecosystem. Each algorithm here implements a specific statistical test — knowing which *hypothesis* you're testing is how you pick the right one.

## Why this crate is separate

The umbrella `nexus-stats` crate has a lot of algorithms, and change-detection specifically pulls in some heavier machinery (windowed MOSUM accumulators, log-likelihood ratios for Shiryaev-Roberts, MAD estimators for robust Z). Splitting it out means you don't pay for what you don't use, and the dependency graph stays clean.

If you're already using `nexus-stats`, enable its `detection` feature and import from there. Depend on this crate directly only when you want a narrower dep tree.

## Design Conventions

Same as the rest of the ecosystem:

- `update(sample) -> Result<..., DataError>` (or `Option<Direction>`, `Option<bool>`, `Decision` — the return type encodes what the detector signals).
- `is_primed()` / `count()` / `reset()` on every type.
- Builder-style construction for anything with more than two parameters.
- O(1) per update, fixed memory. Windowed types allocate once at construction.

## The Return Types

Detection types don't all return the same shape. Know what you're getting:

- **`Option<Direction>`** — None if nothing fired; `Some(Direction::Up)` or `Some(Direction::Down)` on signal. Used by CUSUM and MOSUM.
- **`Option<bool>`** — None before primed, `Some(true)` on trigger. Used by Shiryaev-Roberts.
- **`Option<Condition>`** — None if steady, `Some(Condition::Warning | Critical)` on state transition. Used by MultiGate, ErrorRate.
- **Score** — just `update()` and then query `.z_score()` / `.score()` / `.value()`. Used by AdaptiveThreshold and RobustZScore when you want the raw score rather than a threshold decision.
- **`Decision`** — `Accept`, `Reject`, `Continue`. Used by SPRT.

## Feature Flags

| Feature | Effect |
|---------|--------|
| `std` | Native math via standard library; default. |
| `libm` | `no_std` fallback. |
| `alloc` | Enables `Mosum`, entropy types, transfer entropy. |

Shiryaev-Roberts, AdaptiveThreshold, and SPRT variants require `std` or `libm`. MOSUM, Entropy, CrossCorrelation, and TransferEntropy require `alloc`.

## no_std

Everything non-windowed and non-log works under `no_std` + `libm`. Add `alloc` for the windowed and histogram-based types. No wall-clock time dependency — these operate on sample streams, not timestamps.

## Composing with the ecosystem

A typical detection pipeline:

```
raw input
   │
   ▼
 [Hampel or Ema]         pre-filter / smooth
   │
   ▼
 [AdaptiveThreshold]        score the residual
   │
   ▼
 [DebounceU32]                 suppress single-sample noise
   │
   ▼
 alert
```

Every stage is O(1) and composable. None of them allocate on the hot path.

## Cross-references

- Basic CUSUM: [`nexus-stats-core::detection::Cusum`](../../nexus-stats-core/docs/detection.md#cusum--cumulative-sum).
- Smoothing before detecting: [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).
- Composing many detectors: see `choosing.md`.
