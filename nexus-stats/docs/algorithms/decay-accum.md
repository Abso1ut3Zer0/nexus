# DecayingAccumulator — Event-Driven Score with Time Decay

**Accumulates on discrete events, decays lazily over time.** Different
from EMA — this is for "how active has this entity been recently?"

| Property | Value |
|----------|-------|
| Update cost | O(1) per event or query |
| Memory | ~16 bytes |
| Types | `DecayAccum` |

## What It Does

```
  Events:  ╿  ╿     ╿     ╿               ╿     (discrete, irregular)
  Score:   ╱╲ ╱╲   ╱╲   ╱╲               ╱╲
          ╱  ╱  ╲ ╱  ╲ ╱  ╲╲            ╱  ╲
         ╱──╱    ╲    ╲    ──╲╲         ╱    ╲──
        ──          ──    ──    ──╲╲──  ╱      ────
                                    ╲╲╱           ──
      └──────────────────────────────────────────── t
        active         quieter        idle    active
```

**Lazy evaluation:** decay is only computed when you call `score()` or
`update()`. If nobody queries for 10 seconds, no work is done —
the decay is applied retroactively on the next access.

## Key Difference from EMA

EMA tracks a continuous signal (one sample per tick). `DecayAccum`
tracks discrete events (arrivals, requests, faults) that happen at
irregular intervals. Between events, the score decays automatically.

## Configuration

```rust
let mut acc = DecayAccum::new(1.0).unwrap();  // half-life of 1.0 time units

acc.update(timestamp, 1.0);   // event with weight 1
acc.update(timestamp, 5.0);   // event with weight 5 (more significant)

let current = acc.score(now);      // decayed score at current time
```

## Examples

- Connection activity scoring: "how active in the last few seconds?"
- Threat/heat scoring in game AI
- Rate limiting with decay (similar to token bucket but additive)

## Performance

O(1) per operation. One `exp()` call (or approximation) on each access
for the lazy decay computation.
