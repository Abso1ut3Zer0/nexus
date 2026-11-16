# Performance Reference

All measurements are `rdtsc` ticks per update, batch of 64 updates per
sample, 100k samples after 10k warmup, from `examples/perf_stats.rs` on an
Intel Core Ultra 7 165U, pinned to a P-core (`taskset -c 0`) with turbo on,
best of three runs (minimum per row). This is a developer laptop, not a perf
lab, and `rdtsc` counts the constant 2.7 GHz TSC rather than core clocks, so
read the numbers as estimates of relative cost, taken the same way as every
earlier number in these docs. The build uses the default x86_64 target
features, so multiply-adds are `a * b + c`; the crate fuses them into FMA
instructions only when the target has the feature (`-C target-cpu=native` or
`-C target-feature=+fma`), because without it Rust's `f64::mul_add` is a call
into compiler-builtins' software `fma`, which used to cost the FMA-heavy rows
3 to 5 times their arithmetic. Fused and unfused results differ in the last
bit. Inputs are pseudo-random in a narrow band,
except the threshold types (`DeadBand`, `Hysteresis`, `LevelCrossing`,
`PeakDetector`), which see a slowly varying sawtooth so the branch is
predictable, as a monitored signal is in practice; on white noise each flip
costs a branch mispredict, about 20 cycles.

## Per-Algorithm Cycle Counts

| Algorithm | p50 | p99 | Notes |
|-----------|-----|-----|-------|
| **Change Detection** | | | |
| Cusum | 5 | 5 | add/sub/max |
| Mosum (window 64) | 5 | 5 | ring buffer |
| ShiryaevRoberts | 18 | 21 | one `exp()` |
| MultiGate | 8 | 9 | 3-gate + conditional EMA |
| RobustZScore<f64> | 7 | 8 | EMA + MAD + freeze |
| AdaptiveThreshold | 6 | 7 | EMA + Welford + z-score |
| **Smoothing** | | | |
| Ema | 5 | 5 | mul_add (FMA) |
| AsymEma | 10 | 11 | branch + mul_add |
| Kama (window 10) | 21 | 22 | O(N) volatility recompute |
| Kalman1d | 22 | 27 | 2x2 predict + update |
| Holt | 9 | 10 | two smoothing steps |
| Spring | 12 | 12 | Padé approximant |
| WindowedMedian<f64> (window 32) | 131 | 147 | O(N) sorted array |
| Slew<f64> | 7 | 8 | clamp (maxsd/minsd) |
| **Statistics** | | | |
| Welford | 11 | 13 | one division |
| Welford query | 9 | 10 | includes vsqrtsd |
| EwmaVar | 6 | 6 | two mul_add |
| Covariance | 10 | 12 | three accumulators |
| HarmonicMean | 7 | 7 | one reciprocal |
| **Monitoring** | | | |
| Drawdown<f64> | 5 | 5 | compare + max |
| RunningMin/Max<f64> | 5 | 5 | single comparison |
| WindowedMax/Min<f64> | 9 | 11 | 3-sample promotion |
| PeakHold<f64> | 8 | 10 | compare + decay |
| MaxGauge<f64> | 6 | 6 | compare-and-swap |
| Liveness | 7 | 8 | EMA + deadline |
| EventRate | 6 | 6 | bit-shift EMA + inversion |
| CoDel<i64> | 5 | 5 | first_above deadline (RFC 8289) |
| PollSaturation::on_work | 5 | 6 | branchless (cmov selects, no jumps); 5 under mixed load too |
| PollSaturation::on_idle | 1 | 1 | one byte store, no clock |
| SojournSaturation::update | 6 | 7 | branchless: clamp, count, min, max, saturating total |
| ErrorRate | 7 | 9 | EMA of outcomes |
| TrendAlert | 10 | 10 | Holt + threshold |
| Jitter<f64> | 6 | 7 | EMA of deltas |
| **Frequency** | | | |
| TopK<u64, 16> | 46 | 49 | linear scan |
| **Utilities** | | | |
| BoolWindow (64) | 10 | 10 | bit manipulation |
| Hysteresis<f64> | 2 | 2 | two comparisons |
| DeadBand<f64> | 4 | 4 | one comparison |
| Debounce | 5 | 5 | increment + compare |
| FirstDiff/SecondDiff | 6 | 6 | subtraction |
| LevelCrossing<f64> | 3 | 4 | one comparison |
| PeakDetector<f64> | 3 | 4 | two comparisons |

## Memory Per Instance

| Category | Typical size |
|----------|-------------|
| Simple (EMA, CUSUM, Drawdown, etc.) | 16-56 bytes |
| Welford, Covariance | 24-48 bytes |
| Windowed types (3-sample Nichols') | 48 bytes |
| PollSaturation (`repr(C)`: flag byte + nine `u64`) | 80 bytes (64-bit) |
| SojournSaturation (budget + five `u64` + flag) | 56 bytes (64-bit) |
| Ring buffer types (MOSUM, window N) | N × 8 bytes |
| WindowedMedian (window N) | 2 × N × 8 bytes |
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
