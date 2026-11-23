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
| EMA, CUSUM, Drawdown | No |
| WindowedMin/Max, Slew, DeadBand | No |
| Debounce, Hysteresis, PeakDetector | No |
| FirstDiff, SecondDiff, LevelCrossing | No |
| BoolWindow | No |
| Jitter<i64>, Liveness, EventRate, PollSaturation | No |
| Welford (`std_dev()` query) | Yes (`sqrt`) |
| ShiryaevRoberts | Yes (`exp`) |
| `halflife()` on any builder | Yes (`exp`) |
| Kalman1D, Spring | No (rational approximation, no transcendentals) |

If you only use algorithms that don't need math functions, you can
skip both `std` and `libm` features entirely.

## Integer Forms for Embedded

The cheap primitives are generic over `f64` and `i64`:
`DeadBand<i64>`, `Hysteresis<i64>`, `LevelCrossing<i64>`, `FirstDiff<i64>`,
`SecondDiff<i64>`, `Drawdown<i64>`,
`WindowedMax<i64>`, `WindowedMin<i64>`, `PeakHold<i64>`,
`CoDel<i64>`, `Jitter<i64>`, `WindowedMedian<i64>`, `PeakDetector<i64>`. The
tick-based monitors (`Liveness`, `EventRate`, `PollSaturation`,
`SojournSaturation`) are integer throughout. Where these need smoothing they
use the Linux kernel's fixed-point pattern (a bit-shift EMA), so none of it
touches floating point: ideal for Cortex-M and other platforms without an
FPU. The smoothers that take arbitrary data (`Ema`, `AsymEma`, `Welford`,
`Cusum`, ...) are `f64`; see [Integer vs Float](integer-vs-float.md).

## Memory Budgets

All primitives are stack-allocated with known sizes. No heap allocation.

| Primitive | Memory |
|-----------|--------|
| EMA, CUSUM | 24-56 bytes |
| Welford | 24 bytes |
| WindowedMin/Max | 72 bytes |
| MOSUM<32> | 256 bytes (ring buffer) |
| WindowedMedian<16> | 256 bytes (2 arrays) |
| Everything else | 8-32 bytes |
