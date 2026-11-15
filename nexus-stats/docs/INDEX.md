# nexus-stats Documentation

## Getting Started

- [Which algorithm do I need?](guides/choosing.md) — Decision tree for common problems
- [Quick examples](guides/quickstart.md) — Copy-paste recipes for common patterns

## Algorithm Reference

Each algorithm has a deep-dive doc covering what it does, how it works,
when to use it (and when not to), configuration guidance, and cross-domain
examples.

### Change Detection
- [CUSUM](algorithms/cusum.md) — Persistent mean shift detection
- [MOSUM](algorithms/mosum.md) — Transient spike detection
- [Shiryaev-Roberts](algorithms/shiryaev-roberts.md) — Optimal change detection
- [MultiGate](algorithms/multi-gate.md) — Layered anomaly filter with graded severity
- [RobustZScore](algorithms/robust-z-score.md) — MAD-based anomaly scoring
- [AdaptiveThreshold](algorithms/adaptive-threshold.md) — Z-score anomaly detection

### Smoothing & Filtering
- [EMA](algorithms/ema.md) — Exponential moving average (float and integer)
- [AsymmetricEMA](algorithms/asym-ema.md) — Different smoothing for rising vs falling
- [KAMA](algorithms/kama.md) — Kaufman adaptive moving average
- [Kalman1D](algorithms/kalman1d.md) — 1D Kalman filter with velocity
- [Holt](algorithms/holt.md) — Double exponential smoothing with trend
- [CriticallyDampedSpring](algorithms/spring.md) — Smooth target chasing
- [SlewLimiter](algorithms/slew.md) — Hard rate-of-change clamp
- [WindowedMedian](algorithms/windowed-median.md) — Robust median filter

### Statistics
- [Welford](algorithms/welford.md) — Online mean, variance, standard deviation
- [Moments](algorithms/moments.md) — Online skewness & kurtosis (Pebay, 2008)
- [EwmaVariance](algorithms/ewma-var.md) — Exponentially weighted variance
- [Covariance](algorithms/covariance.md) — Online covariance and Pearson correlation
- [HarmonicMean](algorithms/harmonic-mean.md) — Correct average for rates

### Signal Analysis
- [Autocorrelation](algorithms/autocorrelation.md) — Self-correlation at fixed lag (trending vs reverting)
- [CrossCorrelation](algorithms/cross-correlation.md) — Two-stream lead/lag detection

### Regression
- [LinearRegression](algorithms/linear-regression.md) — Online linear fit with closed-form solve
- [PolynomialRegression](algorithms/polynomial-regression.md) — Online curve fitting (degree 1-8)
- Transformed fits: [Exponential](algorithms/polynomial-regression.md#exponential-y--aebx), [Logarithmic](algorithms/polynomial-regression.md#logarithmic-y--alnx--b), [Power](algorithms/polynomial-regression.md#power-y--axb)

### Bayesian Inference
- [BetaBinomial / GammaPoisson](algorithms/bayesian.md) — Conjugate prior rate estimation with credible intervals

### Hypothesis Testing
- [SPRT](algorithms/sprt.md) — Sequential Probability Ratio Test (Bernoulli + Gaussian)

### Adaptive Filters & Online Learning
- [LMS / NLMS / RLS](algorithms/adaptive-filters.md) — Adaptive weight learning (gradient + recursive least squares)
- [LogisticRegression](algorithms/adaptive-filters.md#logistic-regression--binary-classification) — Online binary classifier
- [OnlineKMeans](algorithms/adaptive-filters.md#online-k-means--streaming-clustering) — Streaming cluster assignment

### State Estimation
- [Kalman2D / Kalman3D](algorithms/kalman.md) — Multivariate Kalman filters with time-varying observation
- [Kalman1D](algorithms/kalman1d.md) — Scalar Kalman filter

### Optimization
- [Optimizers](algorithms/optimizers.md) — OnlineGD, AdaGrad, Adam/AdamW (background thread, not hot path)

### Information Theory
- [Entropy](algorithms/entropy.md) — Shannon entropy over categorical distributions
- [TransferEntropy](algorithms/transfer-entropy.md) — Directed information flow (Granger causality)

### Monitoring
- [Drawdown](algorithms/drawdown.md) — Peak-to-trough decline tracking
- [RunningMin/Max](algorithms/running-min-max.md) — All-time extrema
- [WindowedMin/Max](algorithms/windowed-min-max.md) — Sliding window extrema
- [PeakHoldDecay](algorithms/peak-hold.md) — Peak envelope with decay
- [MaxGauge](algorithms/max-gauge.md) — Reset-on-read maximum
- [Liveness](algorithms/liveness.md) — Source alive/dead detection
- [EventRate](algorithms/event-rate.md) — Smoothed events per unit time
- [CoDel](algorithms/codel.md) — Controlled Delay queue monitor
- [PollSaturation](algorithms/poll-saturation.md) — Consumer-side saturation from poll outcomes
- [SojournSaturation](algorithms/sojourn-saturation.md) — Consumer saturation from stamped queue sojourn
- [ErrorRate](algorithms/error-rate.md) — Failure rate tracking
- [TrendAlert](algorithms/trend-alert.md) — Trend direction detection
- [Jitter](algorithms/jitter.md) — Signal variability measurement

### Frequency & Counting
- [TopK](algorithms/topk.md) — Space-Saving top-K frequent items
- [FlexibleProportions](algorithms/flex-proportion.md) — Per-entity fraction tracking
- [DecayingAccumulator](algorithms/decay-accum.md) — Event-driven score with time decay

### Utilities
- [Debounce](algorithms/debounce.md) — N consecutive events before triggering
- [DeadBand](algorithms/dead-band.md) — Change suppression below threshold
- [Hysteresis](algorithms/hysteresis.md) — Binary decision with different thresholds
- [BoolWindow](algorithms/bool-window.md) — Sliding pass/fail rate
- [PeakDetector](algorithms/peak-detector.md) — Local maxima/minima detection
- [LevelCrossing](algorithms/level-crossing.md) — Threshold crossing counter
- [FirstDiff / SecondDiff](algorithms/diff.md) — Discrete derivative and acceleration

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
- [Integer vs Float](guides/integer-vs-float.md) — When to use which variant
- [no_std Usage](guides/no-std.md) — Embedded and kernel use cases
- [Runtime vs Const Generic](guides/runtime-vs-const.md) — alloc feature flag explained

## Reference

- [Type Matrix](reference/type-matrix.md) — Full type availability table
- [Performance](reference/performance.md) — Cycle counts, memory usage, benchmarks
- [Glossary](reference/glossary.md) — ARL, z-score, MAD, EMA, etc.
