# Choosing a Detector

Every detector tests a different hypothesis. Match the question to the type.

## "Has the mean persistently shifted?"

Use **`Cusum`** (from `nexus-stats-core::detection`). CUSUM accumulates deviations from a target, fires when the cumulative budget is exhausted. It does *not* fire on a single spike — the shift must be sustained.

For optimal detection when you know the shift magnitude in advance, use **`ShiryaevRoberts`** (this crate). Shiryaev-Roberts is the asymptotically optimal detector in the minimax sense under a known alternative hypothesis.

## "Was there a recent *transient* spike?"

Use **`Mosum`** — Moving Sum, the windowed cousin of CUSUM. It sums over a sliding window rather than an unbounded accumulator, so single spikes show up and then fade. Fires on recent anomalies, not on persistent shifts.

CUSUM vs MOSUM: CUSUM detects "is the mean different now and staying different?". MOSUM detects "did something weird happen in the last N samples?".

## "Is this specific sample an outlier?"

Two choices:

- **`AdaptiveThreshold`** — Maintains EMA and EW variance, returns a z-score against the streaming baseline. Classic `|x - EMA| / stddev > k` test. Fast and simple. Assumes Gaussian noise.

- **`RobustZScore<f64>`** — Same idea, but uses median and MAD instead of mean and variance. Robust to heavy tails and outliers (your baseline isn't polluted by the things you're trying to detect). Slower but correct under non-Gaussian noise.

Pick RobustZ when your data has fat tails (financial returns, sensor flakes). Pick AdaptiveThreshold when it's Gaussian-ish (latency with GC, throughput with buffering).

## "Is the trend heading toward a limit?"

Use **`TrendAlert`**. Internally uses Holt-style level+trend estimation; alerts when the extrapolated forecast crosses a threshold. This is the "latency is increasing, will cross SLO in 3 minutes" detector.

## "Has the distribution *shape* changed?"

Use **`DistributionShift`** (from `nexus-stats-core::detection`). Compares fast-window skewness/kurtosis against a slow baseline. Catches "mean is still 0 but tails got fatter" regime changes.

## "I need *graded severity* — normal / warning / critical"

Use **`MultiGate`**. Layered threshold gates — configure multiple thresholds with separate halflives. Emits `Condition::Normal | Warning | Critical` state transitions.

## "Is this stream trending or reverting?"

Use **`Autocorrelation`** at lag 1 (or more). Positive autocorrelation at lag 1 = trending (if a step moved up, the next step is likely up too). Negative = mean-reverting. Near zero = random walk.

For a full trend-vs-reversion suite, pair with [`HalfLife`](../../nexus-stats-core/docs/statistics.md#halflife--mean-reversion-half-life) and [`Hurst`](../../nexus-stats-core/docs/statistics.md#hurst--hurst-exponent).

## "Which of these two streams leads?"

Use **`CrossCorrelation`**. Given streams X and Y and a lag range, it computes ρ(x_t, y_{t-lag}) for each lag and tells you which direction leads.

Classic use: "does the bid side of exchange A lead the bid side of exchange B?". Or: "does our CPU spike lead or follow the latency spike?".

## "Does stream X causally drive stream Y?"

Use **`TransferEntropy`**. Granger-style information-theoretic causality. Expensive to compute (histogram-based) but much stronger than correlation — it detects nonlinear dependencies correlation misses.

Use for: causal signal research, factor discovery. Not for hot paths.

## "I want a sequential A/B test / statistical decision"

Use **`SprtBernoulli`** (for success/failure rates) or **`SprtGaussian`** (for continuous means). Wald's Sequential Probability Ratio Test: accumulate evidence and decide `Accept H0` / `Reject H0` / `Continue` as soon as the evidence crosses a pre-specified error bound. Minimizes samples for a given error rate.

Use for: online A/B tests, sequential quality control, early-stop experiments.

## Decision tree

```
What are you asking?
├─ "Did the mean shift (persistently)?"
│    ├─ Known shift size → ShiryaevRoberts
│    └─ Unknown → CUSUM (from nexus-stats-core)
├─ "Was there a recent spike?" → MOSUM
├─ "Is THIS sample weird?"
│    ├─ Gaussian data → AdaptiveThreshold
│    └─ Heavy tails → RobustZScore
├─ "Will we hit a limit soon?" → TrendAlert
├─ "Did the shape change?" → DistributionShift (from nexus-stats-core)
├─ "Multi-level alerting?" → MultiGate
├─ "Is it trending or reverting?" → Autocorrelation(lag=1)
├─ "Which stream leads?" → CrossCorrelation
├─ "Does X cause Y?" → TransferEntropy
└─ "Sequential decision test" → SPRT
```
