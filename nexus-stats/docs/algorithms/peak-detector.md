# PeakDetector — Local Maxima/Minima Detection

**Detects peaks and troughs in a signal.** Uses 3-point comparison with
configurable prominence threshold to filter noise.

| Property | Value |
|----------|-------|
| Update cost | 3 cycles |
| Memory | ~16 bytes |
| Types | `PeakDetector<f64>`, `PeakDetector<i64>` |
| Output | `Option<Peak>` — detected peak with value and direction |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

```
  Signal with peaks and troughs:

  Value
  100 ┤        ·                    ·
   90 ┤     ·     ·              ·     ·
   80 ┤  ·           ·        ·
   70 ┤                 ·  ·              ·
      └──────────────────────────────────────── t
             ↑              ↑          ↑
          peak(100)     trough(70)  peak(100)
```

A peak is reported when the middle of three consecutive smoothed values
is higher than both neighbors by at least the prominence threshold.
This filters out small oscillations — only significant reversals trigger.

## Configuration

```rust
let mut pd = PeakDetector::<f64>::new(5.0).unwrap();  // prominence = 5.0

// Returns Some(Peak) when a local extremum is found
if let Some(peak) = pd.update(sample).unwrap() {
    if peak.is_maximum {
        println!("peak at {}", peak.value);
    } else {
        println!("trough at {}", peak.value);
    }
}
```

**Note:** Peak detection has a 1-sample delay — the peak is confirmed
when the next sample shows the reversal.

## Examples

- Latency peak/trough detection for capacity analysis
- Volume spikes in market data
- Temperature cycle detection in environmental monitoring
