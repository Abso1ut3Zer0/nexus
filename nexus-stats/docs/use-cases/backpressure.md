# Use Case: Backpressure Detection

How to detect queue congestion before buffers fill, using sojourn time
monitoring and resource tracking.

## The Problem

You have producer-consumer queues (Aeron ring buffers, event loop queues,
request queues). When consumers slow down, the queue builds up. By the
time the buffer is full and you hit hard backpressure, it's too late —
messages are dropped or producers block.

You want **early warning**: detect standing queues while there's still
room to act.

## Recipe: CoDel-Style Queue Health

```rust
use nexus_stats::Condition;
use nexus_stats::monitoring::CoDel;

// Detect standing queues via sojourn time
let mut qd = CoDel::<i64>::builder()
    .target(10_000)          // 10μs acceptable queue wait
    .window(100_000_000)     // 100ms observation window
    .min_samples(20)
    .build().unwrap();

// At dequeue time, measure how long the item waited:
let sojourn_ns = now_ns - item.enqueue_timestamp;

match qd.update(now_ns as u64, sojourn_ns) {
    Some(Condition::Degraded) => {
        // Standing queue detected — even the fastest items are waiting too long
        slow_down_producers();
    }
    Some(Condition::Normal) => {
        // Queue is healthy
    }
    None => {} // not primed
}
```

## Recipe: Multi-Signal Pressure Valve

Combine queue delay with resource saturation for comprehensive monitoring.
For a consumer thread measuring its own saturation from poll outcomes, with
no message timestamps, see [Consumer Saturation](consumer-saturation.md):

```rust
use nexus_stats::{Condition, Direction};
use nexus_stats::monitoring::CoDel;
use nexus_stats::smoothing::Ema;
use nexus_stats::detection::TrendAlert;

let mut queue_health = CoDel::<i64>::builder()
    .target(10_000).window(100_000_000).build().unwrap();

let mut cpu_util = Ema::builder().span(20).build().unwrap();  // smoothed CPU busy fraction

let mut latency_trend = TrendAlert::builder()
    .alpha(0.3).beta(0.1).trend_threshold(1.0).build().unwrap();

// Composite pressure assessment:
let queue_pressure = queue_health.update(now, sojourn);
cpu_util.update(cpu_utilization).unwrap();
let cpu_hot = matches!(cpu_util.value(), Some(u) if u > 0.85);
let trend = latency_trend.update(processing_time);

let should_throttle = matches!(queue_pressure, Some(Condition::Degraded)) // queue backing up
    || cpu_hot                                                             // CPU maxed
    || matches!(trend, Some(Direction::Rising));                           // getting worse

if should_throttle {
    reduce_strategy_aggression();
}
```

## Recipe: Message-Bus Publication Monitoring

```rust
use nexus_stats::smoothing::{AsymEma, Ema};

// Track the publication buffer's fill fraction
let mut buf_fill = Ema::builder().span(50).build().unwrap();

// Track publication latency with asymmetric EMA
// (react fast to increases, slow to decreases)
let mut pub_latency = AsymEma::builder()
    .alpha_up(0.3)    // fast reaction to degradation
    .alpha_down(0.05) // slow to declare recovery
    .build().unwrap();

// On each publication:
let fill = publication.buffer_used() as f64 / publication.buffer_capacity() as f64;
buf_fill.update(fill).unwrap();
if matches!(buf_fill.value(), Some(f) if f > 0.70) {
    // start worrying at 70% full
}

if let Some(smoothed) = pub_latency.update(pub_latency_ns as f64) {
    // smoothed tracks the publication latency with fast-rise/slow-fall
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| [CoDel](../algorithms/codel.md) | Standing queue detection (CoDel) |
| [EMA](../algorithms/ema.md) | Resource utilization, smoothed and compared to a threshold |
| [TrendAlert](../algorithms/trend-alert.md) | "Getting worse" detection |
| [AsymmetricEMA](../algorithms/asym-ema.md) | Fast-rise/slow-fall tracking |
| [CUSUM](../algorithms/cusum.md) | Persistent processing time shifts |

## Tips

- **Measure sojourn time, not queue depth.** A deep queue that drains
  fast is fine. A shallow queue where every item waits 50ms is not.
  CoDel measures what matters.

- **Use asymmetric response.** React fast to degradation (alpha_up=0.3),
  recover slowly (alpha_down=0.05). This prevents oscillation where you
  throttle, recover, un-throttle, overload, repeat.

- **Multiple signals beat one signal.** Queue depth + CPU utilization +
  latency trend together give higher confidence than any one alone.
