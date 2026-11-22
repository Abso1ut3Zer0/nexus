# nexus-stats Documentation

## Getting Started

- [Which algorithm do I need?](guides/choosing.md) — Decision tree for common problems
- [Quick examples](guides/quickstart.md) — Copy-paste recipes for common patterns

## API reference

Each type is documented in the crate docs: what it computes, how to read it, and an example. Each module's docs say which of its types to use for what.

## Use Cases

Domain-specific recipes showing how to compose primitives for real problems.

- [Latency Monitoring](use-cases/latency-monitoring.md) — Tracking, alerting, and diagnosing latency
- [Backpressure Detection](use-cases/backpressure.md) — Early warning before buffers fill
- [Anomaly Detection](use-cases/anomaly-detection.md) — Bad data, outliers, impossible events
- [Feed Health](use-cases/feed-health.md) — Monitoring data sources for degradation
- [Consumer Saturation](use-cases/consumer-saturation.md) — A consumer thread measuring its own saturation from poll outcomes
- [Rate Management](use-cases/rate-management.md) — Tracking and adapting to rate limits
- [Capacity Planning](use-cases/capacity-planning.md) — Load distribution and trend analysis
- [Game Performance](use-cases/game-performance.md) — Frame timing, stutter, adaptive quality
- [Network Quality](use-cases/network-quality.md) — RTT, jitter, packet loss, bandwidth
- [Industrial Monitoring](use-cases/industrial-monitoring.md) — Sensor validation, process control
- [SRE Observability](use-cases/sre-observability.md) — SLOs, error budgets, resource tracking
- [Trading Systems](use-cases/trading.md) — Market impact, signal analysis, regime detection, execution quality

## Guides

- [Choosing an Algorithm](guides/choosing.md) — Decision tree
- [Quick Start](guides/quickstart.md) — Copy-paste recipes
- [Composing Primitives](guides/composition.md) — Building complex monitors from simple parts
- [Parameter Tuning](guides/parameter-tuning.md) — How to set alpha, threshold, slack, etc.
- [Integer vs Float](guides/integer-vs-float.md) — Which types have an `i64` form, and the caller rules for the generics
- [Migrating to 7.0](guides/migrating-to-7.md) — 6.x → 7.0: rename map, generics, removed types, behavior changes
- [no_std Usage](guides/no-std.md) — Embedded and kernel use cases

## Reference

- [Type Matrix](reference/type-matrix.md) — Full type availability table
- [Performance](reference/performance.md) — Cycle counts, memory usage, benchmarks
- [Glossary](reference/glossary.md) — ARL, z-score, MAD, EMA, etc.
