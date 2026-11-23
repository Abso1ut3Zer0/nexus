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
| Cusum | 6 | 6 | add/sub/max |
| Mosum (window 64) | 5 | 5 | ring buffer |
| ShiryaevRoberts | 18 | 22 | one `exp()` |
| MultiGate | 8 | 8 | 3-gate + conditional EMA |
| RobustZScore<f64> | 8 | 8 | EMA + MAD + freeze |
| AdaptiveThreshold | 7 | 7 | EMA + Welford + z-score |
| Bocpd (max run 64) | 3637 | 4405 | three passes over the run-length posterior, SIMD `ln`/`exp` when built with `+avx2,+fma` |
| DistributionShift (window 50) | 15 | 16 | one moments update; a merge per window |
| **Normalization** | | | |
| ZScoreNorm<f64> | 6 | 7 | score, then EW mean and variance |
| MinMaxNorm<f64> | 15 | 19 | two 3-sample window trackers |
| QuantileNorm<f64> (resolution 9) | 186 | 234 | P² histogram, 11 markers |
| QuantileNorm<f64> (resolution 19) | 292 | 344 | 21 markers |
| QuantileNorm<f64> (resolution 99) | 886 | 1089 | 101 markers |
| **Smoothing** | | | |
| Ema | 5 | 6 | one multiply-add |
| AsymEma | 12 | 12 | branch + multiply-add |
| Kama (window 10) | 15 | 25 | O(N) volatility recompute |
| Kalman1d | 26 | 27 | 2x2 predict + update |
| Holt | 11 | 11 | two smoothing steps |
| Spring | 13 | 14 | Padé approximant |
| WindowedMedian<f64> (window 32) | 80 | 99 | O(N) sorted array |
| Slew<f64> | 8 | 8 | clamp (maxsd/minsd) |
| **Statistics** | | | |
| Welford | 7 | 7 | one reciprocal of the count, off the running mean's dependency chain |
| Welford query | 9 | 10 | includes vsqrtsd |
| EwmVar | 7 | 7 | decayed Welford |
| Covariance | 11 | 11 | three accumulators |
| HarmonicMean | 6 | 7 | one reciprocal |
| **Monitoring** | | | |
| Drawdown<f64> | 5 | 6 | compare + max |
| WindowedMax/Min<f64> | 9 | 11 | 3-sample promotion |
| PeakHold<f64> | 8 | 10 | compare + decay |
| Liveness | 7 | 16 | EMA + deadline |
| EventRate | 7 | 7 | bit-shift EMA + inversion |
| CoDel<i64> | 5 | 6 | first_above deadline (RFC 8289) |
| PollSaturation::on_work | 6 | 6 | branchless (cmov selects, no jumps); 5 under mixed load too |
| PollSaturation::on_idle | 1 | 1 | one byte store, no clock |
| SojournSaturation::update | 7 | 7 | branchless: clamp, count, min, max, saturating total |
| ErrorRate | 7 | 10 | EMA of outcomes |
| TrendAlert | 10 | 11 | Holt + threshold |
| Jitter<f64> | 7 | 7 | EMA of deltas |
| **Frequency** | | | |
| TopK (16 slots) | 36 | 48 | sorted array, scanned (indexed above 32 counters) |
| **Utilities** | | | |
| BoolWindow (64) | 5 | 8 | bit manipulation |
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
| Windowed types (3-sample Nichols') | 72 bytes |
| PollSaturation (`repr(C)`: flag byte + nine `u64`) | 80 bytes (64-bit) |
| SojournSaturation (budget + five `u64` + flag) | 56 bytes (64-bit) |
| Ring buffer types (`storage::Ring`: Mosum, Kama, Hurst, window N) | N × 8 bytes, plus 32 bytes of `Ring` metadata (slice pointer and length, head, full flag) |
| WindowedMedian (window N) | 2 × N × 8 bytes |
| Bocpd (max run N) | 11 × (N + 1) × 8 bytes (posterior, two sufficient statistics, two scratch rows, six precomputed tables) |
| Adwin (max_buckets B) | 64 × (B + 1) × 16 bytes in one allocation, plus 128 bytes of lane occupancies; fixed at build |
| TopK<K> (capacity N) | N × (sizeof(K) + 24, padded) bytes of counters, plus 8 × next_pow2(2N) bytes of hash index when N > 32, allocated once at construction |

## Running Benchmarks

```bash
cargo build --release --example perf_stats -p nexus-stats
taskset -c 0 ./target/release/examples/perf_stats
```

For accurate results:
- Pin to a single physical core (`taskset -c 0`)
- Disable turbo boost if comparing across runs
- Run in isolation (no other CPU-intensive processes)
