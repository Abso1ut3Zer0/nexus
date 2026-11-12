# WindowedMin / WindowedMax — Sliding Window Extrema

**Nichols' algorithm.** Tracks min or max over a sliding time window
using only 3 stored samples. From Linux kernel `win_minmax.h` (TCP BBR).

| Property | Value |
|----------|-------|
| Update cost | ~9 cycles (amortized O(1)) |
| Memory | 64 bytes (3 samples, window, count) |
| Types | `WindowedMaxF64`, `WindowedMinF64`, `WindowedMaxI64`, `WindowedMinI64` |
| Accuracy | Approximate by design; see below |
| Output | Current window extremum |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

```
  WindowedMax with 10-tick window:

  Value
  100 ┤        ·
   80 ┤     ·     ·
   60 ┤  ·           ·        ·
   40 ┤                 ·  ·     ·
      └──────────────────────────────────── t
      │←── window ──→│

  WindowedMax output:
  100 ┤        ┌──────┐
   80 ┤     ┌──┘      └──┐
   60 ┤──┌──┘             └──────────
   40 ┤
      └──────────────────────────────────── t
               ↑ peak enters  ↑ peak exits window
               window         → next best promoted
```

The algorithm keeps the best, 2nd best and 3rd best samples in the window,
each at least as recent as the one before it. A new extremum forgets
everything earlier. By age, a choice is only replaced while no distinct
choice has been found yet: the 2nd after a quarter of the window, the 3rd
after half. When the best ages out, the 2nd is promoted. 64 bytes of state
regardless of window size. This is a literal port of the kernel's
`lib/win_minmax.c`.

## Accuracy

Constant space and time buys an approximation. The reported value is always
a real sample from inside the window, so the maximum is never above the true
windowed maximum and the minimum never below it. On stationary input about
1 to 2% of updates disagree with an exact window; on trending input (a random
walk) the rate is higher, which the kernel's own header acknowledges with
"almost always". For a maximum per reporting interval, `MaxGauge` is exact
and simpler.

## When to Use It

- Min RTT tracking (BBR-style baseline estimation)
- Max throughput over a measurement window
- Best/worst latency in the last N seconds

## When to Use Something Else

- All-time extrema → [RunningMin/Max](running-min-max.md)
- Peak with smooth decay → [PeakHoldDecay](peak-hold.md)
- Max since last check → [MaxGauge](max-gauge.md)

## Configuration

```rust
let mut max = WindowedMaxF64::new(1_000_000_000);  // 1-second window in nanoseconds

let current_max = max.update(now_ns, sample).unwrap();
```

Timestamps are `u64`. The user defines what the units mean (nanoseconds,
ticks, milliseconds, etc.).

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `WindowedMaxF64::update` | 9 cycles | 12-34 cycles |

The p99 tail is higher when sub-window promotions occur (shuffling
3 samples). p50 is a simple comparison.

## Background

Ported from Linux kernel `include/linux/win_minmax.h` and `lib/win_minmax.c`.
Used by TCP BBR for `BtlBw` (bottleneck bandwidth) estimation over
10 RTT rounds, and `RTprop` (round-trip propagation time) over 10 seconds.

Kathleen Nichols' algorithm. Also described in:
Cardwell, Cheng, Gunn, Yeganeh, Jacobson. "BBR: Congestion-Based
Congestion Control." *ACM Queue* 14.5 (2016).
