# nexus-stats-core Documentation

`nexus-stats-core` is the foundation crate of the nexus-stats ecosystem. Everything else in the family (`nexus-stats-smoothing`, `nexus-stats-detection`, `nexus-stats-regression`, `nexus-stats-control`) depends on this crate for shared error types, math utilities, and the most-used streaming statistics primitives.

## Who this crate is for

Most users should depend on the umbrella `nexus-stats` crate, which re-exports everything with a single feature-flag story. Depend on `nexus-stats-core` directly when:

- You want only the core primitives and nothing else (smaller dep tree).
- You're building another `nexus-stats-*` subcrate and need the shared error types.

## Start Here

- [Overview](overview.md) — Design conventions, error handling, no_std, features.
- [Statistics](statistics.md) — Welford, Moments, EwmVar, Covariance, Percentile, HarmonicMean, HitRate, HalfLife, Hurst, VarianceRatio, Amihud, BucketAccumulator, LPM, CVaR.
- [Normalization](normalization.md) — ZScoreNorm, MinMaxNorm, QuantileNorm.
- [Smoothing](smoothing.md) — Ema, AsymEma, Slew.
- [Monitoring](monitoring.md) — Drawdown, RunningMax/Min, WindowedMax/Min, PeakHold, MaxGauge, Liveness, EventRate, CoDel, ErrorRate, Jitter.
- [Detection](detection.md) — CUSUM, DistributionShift.
- [Control](control.md) — DeadBand, Hysteresis, Debounce, LevelCrossing, FirstDiff, SecondDiff.

## Module Layout

```
nexus_stats_core::
├── statistics      // core streaming stats
├── smoothing       // EMA family
├── monitoring      // health, gauges, rate tracking
├── detection       // CUSUM and distribution shift
├── control         // thresholds, hysteresis, differencing
└── normalization   // streaming normalizers (z-score, min-max, quantile)
```

Each submodule is namespaced. You import like `use nexus_stats_core::statistics::Welford;`.

## Cross-References

- Advanced smoothers: [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md)
- Advanced detection + signal analysis: [`nexus-stats-detection`](../../nexus-stats-detection/docs/INDEX.md)
- Regression, Kalman, learning: [`nexus-stats-regression`](../../nexus-stats-regression/docs/INDEX.md)
- Frequency, peak detection, bool window: [`nexus-stats-control`](../../nexus-stats-control/docs/INDEX.md)
- Long-form algorithm reference: [`nexus-stats/docs`](../../nexus-stats/docs/INDEX.md)
