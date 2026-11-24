# Which Algorithm Do I Need?

Start with your problem. Follow the tree to find the right primitive.

## "I want to smooth a noisy signal"

**How noisy? What matters more — responsiveness or stability?**

- Simple smoothing, good defaults → **EMA**
  - `Ema` is `f64`; cast integer samples at the call site (see [Integer vs Float](integer-vs-float.md))
- Need to react fast when trending, slow when noisy → **KAMA**
  - Adapts its smoothing factor based on signal efficiency ratio
- Need to increase fast but decrease slow (or vice versa) → **AsymmetricEMA**
  - Different alpha for each direction. TCP RTT uses this pattern.
- Need to track a moving target without overshoot → **Spring**
  - Better than EMA when chasing a target — has velocity, anticipates
- Need to remove impulse noise / outlier spikes → **WindowedMedian**
  - Median ignores outliers entirely; EMA smears them
- Need level + trend (is it getting worse?) → **Holt**
  - Double exponential smoothing. Separates level from trend.
- Need adaptive smoothing that gets smarter over time → **Kalman1D**
  - Like Holt but with principled adaptive gain. Better after restarts.
- Need to chase a moving target without overshoot → **Spring**
  - Has velocity tracking, anticipates rather than lags. Unity's `SmoothDamp`.
- Need to hard-limit how fast the output can change → **Slew**
  - Not smoothing — hard clamp on rate of change

## "I want to detect a change in behavior"

**What kind of change?**

- Mean shifted up or down permanently → **CUSUM**
  - "Exchange latency increased 20μs and stayed there"
  - Reports direction: `Direction::Rising` or `Direction::Falling`
- Temporary spike, then back to normal → **MOSUM**
  - "Latency spiked for 10 seconds, then recovered"
  - Windowed — forgets the spike after the window passes
- Need best possible detection speed → **ShiryaevRoberts**
  - Theoretically optimal detection delay. Costs one `exp()` per update.
- Is this value trending upward/downward? → **TrendAlert**
  - "Not just high — getting worse over time"
- Is this single sample anomalous? → **AdaptiveThreshold**
  - Z-score against recent baseline. Tells you High/Low direction.

## "I want to detect bad data / outliers"

**How much do you need?**

- Quick, cheap, O(1) → **RobustZScore**
  - MAD-based z-score, freezes baseline on reject
- Multi-level graded response → **MultiGate**
  - Accept / Unusual / Suspect / Reject. Doesn't corrupt baseline.
- Robust statistics (median, MAD, IQR, Tukey fences) → **WindowedMedian**
  - O(N) per update but gives you everything: median, quartiles, MAD
- Just clamp impossible rate of change → **Slew**
  - "Output can't change by more than X per sample"

## "I want to monitor system health"

Every monitoring type states its **weighting clock** in its rustdoc: what one
`update` is worth (per call, per event with its own timestamp, the caller's
timestamps, or none). The rule: never update a per-call type from a loop
whose iteration time depends on the quantity you are measuring. Sampling
queue fill once per spin iteration into an EMA reads healthy under load,
because the loop spins less exactly when the queue is deep. Use a per-event
type with timestamps, or `PollSaturation`, which is weighted per message.

**What are you monitoring?**

- Is a data source alive? → **Liveness**
  - EMA of inter-arrival times + deadline. Call `check(now)` periodically.
- Is a queue building up? → **CoDel**
  - CoDel-inspired. Detects standing queues before buffers fill.
- Is my consumer thread saturated? → **PollSaturation**
  - From poll outcomes alone, no timestamps: how many messages waited behind this thread, for how long at most.
- Messages carry an enqueue stamp? → **SojournSaturation**
  - Exact per-message wait summarized per period: over-budget count, floor, worst, mean, standing queue.
- Is a resource running hot? → smooth the busy fraction with **EMA** and compare it to your threshold. For a consumer thread's own saturation, PollSaturation / SojournSaturation above.
- How many errors, and what share of events? → **ErrorRate**
  - EMA of success/failure outcomes. Supports weighted severity.
- What's the worst since I last checked? → an `Option<T>` you fold with `max` and read with `take()`
- Has N consecutive failures occurred? → **Debounce**
  - "3 timeouts in a row = dead." Simpler than CUSUM for discrete events.
- How many events per second? → **EventRate**
  - Smoothed rate from timestamps.

## "I want to track statistics"

- Running mean + variance + std dev → **`Welford`**
  - Numerically stable. Supports parallel merge (Chan's algorithm).
- Skewness + kurtosis (distribution shape) → **Moments**
  - Extends Welford to 3rd/4th moments. Fat tail and asymmetry detection.
- Exponentially weighted variance (recent volatility) → **EwmVar**
  - More responsive than Welford. RiskMetrics pattern.
- Are two signals correlated? → **Covariance**
  - Online Pearson correlation. Supports merge.
- Average of rates/throughputs → **HarmonicMean**
  - Arithmetic mean of rates is wrong. Harmonic mean is correct.
- Interarrival jitter → **Jitter**
  - The RFC 3550 estimator. Feed each packet's transit time.

## "I want to fit a trend or model"

**What kind of relationship?**

- Simple linear trend (slope + intercept) → **LinearRegression**
  - Closed-form solve, 72 bytes, ~8 cycles. The default for trend estimation.
- Linear trend that adapts to regime changes → **EwLinearRegression**
  - Same but with exponential decay. "What's the *current* slope?"
- Proportional relationship through origin → `LinearRegression::through_origin()`
  - `y = ax`, no intercept. Rate estimation, calibration.
- Quadratic / cubic / higher-degree curve → **PolynomialRegression**
  - Builder: `.degree(3)`. Acceleration detection, complex curvature.
- Exponential growth or decay → **ExponentialRegression**
  - `y = ae^(bx)`. Growth rate estimation, half-life.
- Logarithmic / diminishing returns → **LogarithmicRegression**
  - `y = a·ln(x) + b`. Saturation curves.
- Power law / scaling → **PowerRegression**
  - `y = ax^b`. Scaling exponent estimation.

## "I want to analyze signal relationships"

- Is this signal trending or mean-reverting? → **Autocorrelation**
  - Positive lag-1 = trending, negative = reverting, zero = random walk.
- Does signal A predict signal B? → **CrossCorrelation**
  - Finds the lag with peak correlation. `peak_lag()` = the delay.
- WHICH signal drives the other? → **TransferEntropy**
  - Directed information flow. Cross-correlation is symmetric; transfer entropy is not.
- How predictable is this signal? → **Entropy**
  - Shannon entropy over categorized observations. Low = predictable, high = random.

## "I want to track extrema"

- All-time min or max → `f64::max` / `Ord::max` on a variable; no type needed
- Min/max over a time window → **WindowedMin / WindowedMax**
  - Nichols' algorithm (Linux `win_minmax`, from TCP BBR), 72 bytes. Approximate by
    design: the reported max is never above the truth and the min never below, but
    about 1 to 2% of updates on stationary input disagree with an exact window.
    For a per-reporting-interval maximum, fold with `max` and reset on read: exact and simpler.
- Magnitude of a signal with hold + decay → **PeakHold**
  - "Worst recent spike, fading over time." Smooth envelope.
- Peak-to-trough decline, drawdown → **PeakToTrough**
  - Tracks max drawdown from peak. Risk circuit breaker.

## "I want to count / classify"

- Top K most frequent items → **TopK**
  - Space-Saving algorithm. Fixed memory.
- What share of recent events went to each key? → **FlexProportion**
  - Per-entity fraction with lazy decay. Shard balancing.
- How active is this entity recently? → **DecayingAccumulator**
  - Event-driven score with time decay. Activity/heat scoring.
- Pass/fail rate over last N events → **BoolWindow**
  - Ring of boolean outcomes. Circuit breaker input.

## "I want signal processing utilities"

- Rate of change (first derivative) → **FirstDiff**
- Acceleration (second derivative) → **SecondDiff**
- Detect peaks/troughs in a signal → **PeakDetector**
- Count threshold crossings → **LevelCrossing**
- Binary decision from noisy signal → **Hysteresis**
  - Schmitt trigger. Different thresholds for rising vs falling.
- Suppress changes below threshold → **DeadBand**
  - "Don't tell me unless it changed by at least 5%."

## "I want to make a decision from streaming data"

**What kind of decision?**

- Is A better than B (binary outcome)? → **SprtBernoulli**
  - Controlled false positive/negative rates. Minimal samples.
- Is the mean shifted (continuous)? → **SprtGaussian**
  - Same as Bernoulli but for continuous observations.
- What's the success rate with uncertainty? → **BetaBinomial**
  - Not just "73%" but "73% ± 4% (95% CI)."
- What's the event rate with uncertainty? → **GammaPoisson**
  - Bayesian rate estimation with credible intervals.

## "I want to predict from features"

**What type of prediction?**

- Predict a continuous value from features → **NlmsFilter** (simple) or **RlsFilter** (fast convergence)
- Predict a probability (yes/no) from features → **LogisticRegression**
- Classify into regimes/clusters → **OnlineKMeans**
- Track correlated states with uncertainty → **Kalman2D/3D**

## "I want to optimize parameters from gradients"

- Simple, no tuning needed → **OnlineGD**
- Sparse features, different scales → **AdaGrad**
- Best default, works everywhere → **Adam**
- Need regularization → **Adam with weight_decay**

Note: these are background-thread types, not hot-path. If your loss
is squared error, use LinearRegression
or RLS instead.

## Still not sure?

Common combinations:

| Problem | Primitives |
|---------|-----------|
| "Is latency degrading?" | CUSUM on latency samples |
| "Is latency degrading AND getting worse?" | CUSUM + TrendAlert |
| "Filter bad ticks, track stats on good ones" | MultiGate → Welford (only on Accept) |
| "Monitor queue health with early warning" | PollSaturation (consumer side, no stamps) + CoDel (stamped sojourn) |
| "Smooth a signal, detect when it goes anomalous" | EMA for smoothing, AdaptiveThreshold for detection |
| "Track failure rate, trip a circuit breaker" | ErrorRate (compare its ratio to your limit) or BoolWindow → Debounce |
| "Load-balance across shards" | FlexibleProportions per shard |
| "Display smoothed latency with worst-case envelope" | EMA (display) + PeakHold (envelope) |
| "Is latency distribution getting fat-tailed?" | Moments (kurtosis) |
| "Which signal leads the other?" | CrossCorrelation to find lag, TransferEntropy to confirm direction |
| "Is this signal becoming more/less predictable?" | Entropy over categorized values |
| "Is this signal trending or reverting?" | Autocorrelation lag-1 |
| "What's the current trend slope?" | LinearRegression or EwLinearRegression |
| "Is this accelerating or decelerating?" | PolynomialRegression(degree=2), check quadratic coefficient |
| "Fit an exponential growth curve" | ExponentialRegression |
