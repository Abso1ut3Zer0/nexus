# LevelCrossing — Threshold Crossing Counter

**Counts how often a signal crosses a fixed threshold.** One comparison
per sample.

| Property | Value |
|----------|-------|
| Update cost | 3 cycles |
| Memory | ~16 bytes |
| Types | `LevelCrossing<f64>`, `LevelCrossing<i64>` |
| Output | `bool` — true on crossing |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

```
  Signal crossing threshold:

  Value
  110 ┤     ·        ·        ·
  100 ┤──·──×──·──·──×──·──·──×──·── threshold
   90 ┤        ·        ·        ·
      └────────────────────────────── t
             ↑        ↑        ↑
          crossing  crossing  crossing  (count = 3)
```

Detects the moment a signal transitions across the threshold in either
direction. Useful for frequency estimation (crossings/sec ≈ 2 × frequency)
and activity/oscillation counting.

## API

```rust
let mut lc = LevelCrossing::<f64>::new(100.0).unwrap();  // threshold

assert_eq!(lc.update(95.0).unwrap(), None);                      // first sample
assert_eq!(lc.update(105.0).unwrap(), Some(Direction::Rising));  // crossed up
assert_eq!(lc.update(110.0).unwrap(), None);                     // still above
assert_eq!(lc.update(90.0).unwrap(), Some(Direction::Falling));  // crossed back

assert_eq!(lc.crossing_count(), 2);
```

`update` returns the direction on the sample that lands on the other side of
the threshold, and `None` otherwise. A sample exactly on the threshold is on
neither side: it reports nothing and does not change sides. Touching the
threshold and going back is not a crossing; passing through it is one,
reported on arrival at the far side.

## Examples

- Frequency estimation: `crossings / (2 × time) ≈ dominant frequency`
- Oscillation detection: high crossing rate = unstable signal
- Event counting: "how many times did latency exceed 100ms?"

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `LevelCrossing::<f64>::update` | 3 cycles | 4 cycles |

Two comparisons per sample. Branches perfectly predicted for stable signals.
