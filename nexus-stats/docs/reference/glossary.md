# Glossary

**Alpha (α)** — Smoothing factor for EMA, range (0, 1). Higher alpha =
more reactive, lower = smoother. Related to span: `α = 2/(span + 1)`.

**ARL (Average Run Length)** — Expected number of samples before an event.
ARL₀ = samples before false alarm (want high). ARL₁ = samples to detect
a real change (want low). Used to tune CUSUM and control chart parameters.

**CoDel (Controlled Delay)** — Network algorithm that detects standing queues
by monitoring the minimum sojourn time. CoDel implements the measurement
layer.

**CUSUM** — Cumulative Sum. Sequential test that accumulates deviations from
a target. Detects persistent mean shifts.

**Drawdown** — Drop from peak value. `drawdown = peak - current`.
Max drawdown is the worst drawdown ever observed.

**Efficiency Ratio** — In KAMA: `|net movement| / total path length`.
Ranges from 0 (pure noise) to 1 (straight trend).

**EMA (EWMA)** — Exponential (Weighted) Moving Average. First-order IIR
low-pass filter. `EMA = α × x + (1-α) × EMA`.

**FMA** — Fused Multiply-Add. Hardware instruction that computes `a × b + c`
in one operation with one rounding. nexus-stats emits it only when the target
has the `fma` feature (`-C target-cpu=native` or `-C target-feature=+fma`);
elsewhere multiply-adds are computed as `a * b + c`, because on such targets
Rust's `f64::mul_add` is a library call.

**Halflife** — Number of samples for the EMA weight to decay by 50%.
`α = 1 - exp(-ln2 / halflife)`.

**Harmonic Mean** — `n / Σ(1/xᵢ)`. Correct way to average rates. Always
≤ arithmetic mean.

**IQR (Interquartile Range)** — Q3 - Q1. Robust measure of spread.

**MAD (Median Absolute Deviation)** — Median of `|xᵢ - median|`. Robust
measure of spread with 50% breakdown point.

**Modified Z-Score** — `0.6745 × (x - median) / MAD`. The 0.6745 constant
makes it comparable to standard z-scores for normal data.

**MOSUM** — Moving Sum. Windowed variant of CUSUM. Spikes clear when they
leave the window.

**Nichols' Algorithm** — 3-sample sliding window min/max from the Linux
kernel. Used by TCP BBR for bandwidth and RTT estimation.

**Rational approximation of `exp(-x)`**: `1 / (1 + x + 0.48x² + 0.235x³)`,
used by `Spring` (from *Game Programming Gems 4*) so an uneven time step
needs no transcendental function.

**PELT** — Per-Entity Load Tracking. Linux kernel scheduler's geometric
decay model for CPU utilization estimation.

**P-square** — Jain & Chlamtac's algorithm for streaming quantile
estimation using 5 markers. O(1) per update, 80 bytes.

**RiskMetrics** — JP Morgan's exponentially weighted variance model (1996).
EWMA Variance implements this pattern.

**Slack (k)** — CUSUM parameter. Allowable deviation before accumulation.
Typically set to half the minimum shift to detect.

**Sojourn Time** — Time an item spends in a queue (from enqueue to dequeue).
CoDel operates on this metric.

**Span** — EMA parameter equivalent to window size. `α = 2/(span + 1)`,
the pandas `span` convention. Must be at least 2.

**Threshold (h)** — CUSUM parameter. Accumulated evidence required before
declaring a shift. Higher = fewer false alarms, slower detection.

**USE Method** — Brendan Gregg's resource analysis framework. For every
resource, check Utilization, Saturation, and Errors.

**Z-Score** — `(x - mean) / std_dev`. Number of standard deviations from
the mean. |z| > 3 is traditionally "outlier" territory.
