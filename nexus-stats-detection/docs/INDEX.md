# nexus-stats-detection Documentation

Change detection, anomaly detection, signal analysis, and hypothesis testing. Each algorithm in this crate tests a different *hypothesis* — knowing which hypothesis matches your question is the key to picking the right one.

## Start Here

- [Overview](overview.md) — What this crate provides, feature flags, no_std story.
- [Choosing a Detector](choosing.md) — Decision tree: persistent shift vs spike vs drift vs distribution change.
- [Detection](detection.md) — MOSUM, Shiryaev-Roberts, AdaptiveThreshold, RobustZScore, TrendAlert, MultiGate.
- [Signal Analysis](signal.md) — Autocorrelation, CrossCorrelation, Entropy, TransferEntropy.
- [SPRT (hypothesis testing)](sprt.md) — Sequential Probability Ratio Test, Bernoulli and Gaussian variants.

## Submodule layout

```
nexus_stats_detection::
├── detection     // change and anomaly detection
├── signal        // signal analysis and information theory
└── estimation    // hypothesis testing (SPRT)
```

## Algorithms

### detection

| Type | Hypothesis | When |
|------|------------|------|
| `Mosum` | "Has a recent *window* mean deviated from baseline?" | Transient spikes, local anomalies |
| `ShiryaevRoberts` | Optimal detection under a known alternative | Change-point with known magnitude |
| `AdaptiveThreshold` | "Is |x - EMA| > k * EW_stddev?" | Generic z-score-based outlier |
| `RobustZScore<f64>` | MAD-based outlier score | Heavy-tailed data |
| `TrendAlert` | "Has the slope (Holt trend) crossed a limit?" | Degradation forecasting |
| `MultiGate` | Layered gates with graded severity | Composite alerting |

### signal

| Type | What it computes |
|------|------------------|
| `Autocorrelation` / `I64` | ρ(lag) — is the signal trending or mean-reverting? |
| `CrossCorrelation` | ρ(x_t, y_{t-lag}) — which stream leads? |
| `Entropy` | Shannon entropy over categorical distributions |
| `TransferEntropy` | Directed information flow — Granger-style causality |

### estimation

| Type | Test |
|------|------|
| `SprtBernoulli` | Sequential test for a Bernoulli success rate |
| `SprtGaussian` | Sequential test for a Gaussian mean |

## Cross-references

- Basic CUSUM and DistributionShift: [`nexus-stats-core::detection`](../../nexus-stats-core/docs/detection.md).
- Feed the smoothed input from [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md) into these detectors.
- Umbrella long-form: [`nexus-stats/docs`](../../nexus-stats/docs/INDEX.md).
