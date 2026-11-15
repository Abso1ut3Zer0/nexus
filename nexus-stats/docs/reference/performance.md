# Performance Reference

All measurements in CPU cycles (`rdtsc`), batch of 64 updates per sample,
pinned to a single core.

## Per-Algorithm Cycle Counts

| Algorithm | p50 | p99 | Notes |
|-----------|-----|-----|-------|
| **Change Detection** | | | |
| Cusum | 5 | 7 | add/sub/max |
| CusumI64 | 4 | 4 | integer only |
| Mosum<64> | 6 | 7 | ring buffer |
| ShiryaevRoberts | 17 | 41 | one `exp()` |
| MultiGate | 12 | 17 | 3-gate + conditional EMA |
| RobustZScore<f64> | 12 | 27 | EMA + MAD + freeze |
| AdaptiveThreshold | ~15 | ~20 | EMA + Welford + z-score |
| **Smoothing** | | | |
| Ema | 5 | 6 | mul_add (FMA) |
| EmaI64 | 5 | 5 | bit-shift |
| AsymEma | 11 | 12 | branch + mul_add |
| Kama<10> | 16 | 25 | O(N) volatility recompute |
| Kalman1d | 25 | 30 | 2x2 predict + update |
| Holt | 11 | 12 | two smoothing steps |
| Spring | 12 | 12 | Padé approximant |
| WindowedMedian<f64><32> | 136 | 195 | O(N) sorted array |
| Slew<f64> | ~3 | ~3 | clamp (maxsd/minsd) |
| **Statistics** | | | |
| Welford | 10 | 12 | one division |
| Welford query | 9 | 10 | includes vsqrtsd |
| EwmaVar | 12 | 30 | two mul_add |
| Covariance | 12 | 40 | three accumulators |
| HarmonicMean | ~5 | ~6 | one reciprocal |
| **Monitoring** | | | |
| Drawdown<f64> | 5 | 5 | compare + max |
| RunningMin/MaxF64 | 5 | 5 | single comparison |
| WindowedMax/MinF64 | 9-10 | 12-34 | 3-sample promotion |
| PeakHold<f64> | 7 | 9 | compare + decay |
| MaxGauge<f64> | ~5 | ~5 | compare-and-swap |
| Liveness | 6 | 20 | EMA + deadline |
| EventRate | 6 | 9 | bit-shift EMA + inversion |
| CoDel<i64> | 7 | 10 | first_above deadline (RFC 8289) |
| PollSaturation::on_work | 5 | 6 | branchless (cmov selects, no jumps); 5 under mixed load too |
| PollSaturation::on_idle | 1 | 1 | one byte store, no clock |
| SojournSaturation::update | 6 | 7 | branchless: clamp, count, min, max, saturating total |
| ErrorRate | ~6 | ~8 | EMA of outcomes |
| TrendAlert | ~12 | ~18 | Holt + threshold |
| Jitter<f64> | 6 | ~9 | EMA of deltas |
| **Frequency** | | | |
| TopK<u64, 16> | 42 | 97 | linear scan |
| **Utilities** | | | |
| BoolWindow<1> | 6 | 11 | bit manipulation |
| Hysteresis<f64> | ~3 | ~3 | two comparisons |
| DeadBand<f64> | ~2 | ~3 | one comparison |
| DebounceU32 | ~2 | ~2 | increment + compare |
| FirstDiff/SecondDiff | ~2 | ~2 | subtraction |
| LevelCrossing<f64> | ~2 | ~2 | one comparison |
| PeakDetector<f64> | ~3 | ~3 | two comparisons |

## Memory Per Instance

| Category | Typical size |
|----------|-------------|
| Simple (EMA, CUSUM, Drawdown, etc.) | 16-56 bytes |
| Welford, Covariance | 24-48 bytes |
| Windowed types (3-sample Nichols') | 48 bytes |
| PollSaturation (`repr(C)`: flag byte + nine `u64`) | 80 bytes (64-bit) |
| SojournSaturation (budget + five `u64` + flag) | 56 bytes (64-bit) |
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
