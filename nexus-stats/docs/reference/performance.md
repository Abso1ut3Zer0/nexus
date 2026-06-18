# Performance Reference

All measurements in CPU cycles (`rdtsc`), batch of 64 updates per sample,
pinned to a single core.

## Per-Algorithm Cycle Counts

| Algorithm | p50 | p99 | Notes |
|-----------|-----|-----|-------|
| **Change Detection** | | | |
| CusumF64 | 5 | 7 | add/sub/max |
| CusumI64 | 4 | 4 | integer only |
| MosumF64<64> | 6 | 7 | ring buffer |
| ShiryaevRoberts | 17 | 41 | one `exp()` |
| MultiGateF64 | 12 | 17 | 3-gate + conditional EMA |
| RobustZScoreF64 | 12 | 27 | EMA + MAD + freeze |
| AdaptiveThresholdF64 | ~15 | ~20 | EMA + Welford + z-score |
| **Smoothing** | | | |
| EmaF64 | 5 | 6 | mul_add (FMA) |
| EmaI64 | 5 | 5 | bit-shift |
| AsymEmaF64 | 11 | 12 | branch + mul_add |
| KamaF64<10> | 16 | 25 | O(N) volatility recompute |
| Kalman1dF64 | 25 | 30 | 2x2 predict + update |
| HoltF64 | 11 | 12 | two smoothing steps |
| SpringF64 | 12 | 12 | Padé approximant |
| WindowedMedianF64<32> | 136 | 195 | O(N) sorted array |
| SlewF64 | ~3 | ~3 | clamp (maxsd/minsd) |
| **Statistics** | | | |
| WelfordF64 | 10 | 12 | one division |
| WelfordF64 query | 9 | 10 | includes vsqrtsd |
| EwmaVarF64 | 12 | 30 | two mul_add |
| CovarianceF64 | 12 | 40 | three accumulators |
| HarmonicMeanF64 | ~5 | ~6 | one reciprocal |
| **Monitoring** | | | |
| DrawdownF64 | 5 | 5 | compare + max |
| RunningMin/MaxF64 | 5 | 5 | single comparison |
| WindowedMax/MinF64 | 9-10 | 12-34 | 3-sample promotion |
| PeakHoldF64 | 7 | 9 | compare + decay |
| MaxGaugeF64 | ~5 | ~5 | compare-and-swap |
| LivenessI64 / LivenessU64 | 6 | 20 | EMA + deadline |
| EventRateU64 | 6 | 9 | bit-shift EMA + inversion |
| CoDelI64 | 7 | 10 | WindowedMin + threshold |
| SaturationF64 | ~6 | ~8 | EMA + threshold |
| ErrorRateF64 | ~6 | ~8 | EMA of outcomes |
| TrendAlertF64 | ~12 | ~18 | Holt + threshold |
| JitterF64 | 6 | ~9 | EMA of deltas |
| **Frequency** | | | |
| TopK<u64, 16> | 42 | 97 | linear scan |
| **Utilities** | | | |
| BoolWindow<1> | 6 | 11 | bit manipulation |
| HysteresisF64 | ~3 | ~3 | two comparisons |
| DeadBandF64 | ~2 | ~3 | one comparison |
| DebounceU32 | ~2 | ~2 | increment + compare |
| FirstDiff/SecondDiff | ~2 | ~2 | subtraction |
| LevelCrossingF64 | ~2 | ~2 | one comparison |
| PeakDetectorF64 | ~3 | ~3 | two comparisons |

## Memory Per Instance

| Category | Typical size |
|----------|-------------|
| Simple (EMA, CUSUM, Drawdown, etc.) | 16-56 bytes |
| Welford, Covariance | 24-48 bytes |
| Windowed types (3-sample Nichols') | 48 bytes |
| Ring buffer types (MOSUM<N>) | N × 8 bytes |
| WindowedMedian<N> | 2 × N × 8 bytes |
| TopK<K, CAP> | CAP × (sizeof(K) + 8) bytes |

## Running Benchmarks

```bash
cargo build --release --example perf_stats -p nexus-stats
taskset -c 0 ./target/release/examples/perf_stats
```

For accurate results:
- Pin to a single physical core (`taskset -c 0`)
- Disable turbo boost if comparing across runs
- Run in isolation (no other CPU-intensive processes)
