# Use Case: Game Performance Monitoring

Frame timing, stutter detection, and adaptive quality.

## Recipe: Frame Time Dashboard

```rust
use nexus_stats::Direction;
use nexus_stats::smoothing::Ema;
use nexus_stats::detection::AdaptiveThreshold;
use nexus_stats::monitoring::PeakHold;

// Smooth FPS display (don't show every fluctuation)
let mut frame_ema = Ema::builder().alpha(0.05).build().unwrap();

// Detect stutters (frame time spikes)
let mut stutter = AdaptiveThreshold::builder()
    .span(60)           // ~1 second at 60fps
    .z_threshold(2.0)   // 2σ above recent average
    .min_samples(30)
    .build().unwrap();

// Peak frame time with decay
let mut worst_frame = PeakHold::<f64>::builder()
    .hold_samples(60)   // hold for 1 second
    .decay_rate(0.97)
    .build().unwrap();

// Each frame:
let dt_ms = frame_time_ms;

let smooth_dt = frame_ema.update(dt_ms).unwrap_or(dt_ms);
let fps = 1000.0 / smooth_dt;

let is_stutter = matches!(stutter.update(dt_ms), Some(Direction::Rising));
let worst = worst_frame.update(dt_ms);

// Display: fps, worst recent frame, stutter indicator
```

## Recipe: Adaptive Quality

```rust
use nexus_stats::Direction;
use nexus_stats::smoothing::Ema;
use nexus_stats::detection::TrendAlert;

// Track frame budget utilization: smoothed fraction of the 16.67ms budget
let mut budget = Ema::builder().span(30).build().unwrap();

// Track trend (is performance getting worse?)
let mut trend = TrendAlert::builder()
    .alpha(0.2).beta(0.1).trend_threshold(0.1).build().unwrap();

let utilization = frame_time_ms / target_frame_time_ms;
budget.update(utilization).unwrap();
let over_budget = matches!(budget.value(), Some(u) if u > 0.90);  // 90% of budget = 15ms

match (over_budget, trend.update(frame_time_ms).unwrap()) {
    (true, Some(Direction::Rising)) => {
        reduce_quality();  // overloaded and getting worse
    }
    (false, Some(Direction::Falling)) => {
        increase_quality(); // headroom and improving
    }
    _ => {} // hold current quality
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| [EMA](../algorithms/ema.md) | Smooth FPS display |
| [AdaptiveThreshold](../algorithms/adaptive-threshold.md) | Stutter detection |
| [PeakHoldDecay](../algorithms/peak-hold.md) | Worst recent frame |
| [EMA](../algorithms/ema.md) | Budget utilization, smoothed and compared to 0.90 |
| [TrendAlert](../algorithms/trend-alert.md) | Performance trending |
| [Spring](../algorithms/spring.md) | Smooth camera/UI value transitions |
