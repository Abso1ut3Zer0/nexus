# no_std Usage

Using nexus-stats in embedded and kernel environments.

## Feature Configuration

```toml
[dependencies]
# Default: uses std for hardware sqrt/exp
nexus-stats = "1.0"

# no_std with libm (pure Rust math):
nexus-stats = { version = "1.0", default-features = false, features = ["libm"] }

# no_std, no alloc, no libm (only algorithms that don't need sqrt/exp):
nexus-stats = { version = "1.0", default-features = false }
```

## What Needs Math Functions

Most algorithms are pure arithmetic — no `sqrt` or `exp` needed:

| Algorithm | Needs `std` or `libm`? |
|-----------|----------------------|
| EMA, CUSUM, PeakToTrough | No |
| WindowedMin/Max, Slew, DeadBand | No |
| Debounce, Hysteresis, PeakDetector | No |
| FirstDiff, SecondDiff, LevelCrossing | No |
| BoolWindow | No |
| Jitter<i64>, PollSaturation | No |
| Liveness (`alloc`) | No, except `probability_alive()` (`exp`) |
| EventRate, HawkesModel | Yes (an exponential) |
| Welford (`std_dev()` query) | Yes (`sqrt`) |
| ShiryaevRoberts | Yes (`exp`) |
| `halflife()` on any builder | Yes (`exp`) |
| Kalman1D, Spring | No (rational approximation, no transcendentals) |

If you only use algorithms that don't need math functions, you can
skip both `std` and `libm` features entirely.

## Integer Forms for Embedded

The cheap primitives are generic over `f64` and `i64`:
`DeadBand<i64>`, `Hysteresis<i64>`, `LevelCrossing<i64>`, `FirstDiff<i64>`,
`SecondDiff<i64>`,
`WindowedMax<i64>`, `WindowedMin<i64>`, `PeakHold<i64>`,
`Jitter<i64>`, `WindowedMedian<i64>`, `PeakDetector<i64>`. The
saturation monitors (`PollSaturation`, `SojournSaturation`) count in
integers and `Duration`s, so none of it touches floating point. `Liveness` keeps its
state in integers and uses floating point only to report the ratio. The smoothers that take arbitrary data (`Ema`, `AsymEma`, `Welford`,
`Cusum`, ...) are `f64`; see [Integer vs Float](integer-vs-float.md).

## Memory Budgets

All primitives are stack-allocated with known sizes. No heap allocation.

| Primitive | Memory |
|-----------|--------|
| EMA, CUSUM | 24-56 bytes |
| Welford | 24 bytes |
| WindowedMin/Max | 208 bytes on `i128` time, 144 on `Instant`, 128 on `i64` or a named unit |
| MOSUM<32> | 256 bytes (ring buffer) |
| WindowedMedian<16> | 256 bytes (2 arrays) |
| Everything else | 8-32 bytes |
