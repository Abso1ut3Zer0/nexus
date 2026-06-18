# Use Case: Feed Health Monitoring

How to monitor data sources for degradation, silence, and quality issues.

## The Problem

You consume data from external sources (exchange feeds, sensors, APIs,
upstream services). These sources can fail in multiple ways:
- **Dead** — stopped sending entirely
- **Degraded** — still sending but slower than normal
- **Stale** — sending, but the data isn't changing (stuck sensor)
- **Noisy** — data quality has deteriorated
- **Partial** — some data missing (gaps in sequence)

## Recipe: Comprehensive Feed Monitor

```rust
use nexus_stats::Direction;
use nexus_stats::detection::CusumF64;
use nexus_stats::monitoring::{LivenessI64, EventRateI64, JitterI64};
use nexus_stats::control::DeadBandI64;

struct FeedMonitor {
    liveness: LivenessI64,      // is it alive?
    latency: CusumF64,          // has latency shifted?
    rate: EventRateI64,         // is message rate normal?
    jitter: JitterI64,          // is timing unstable?
    staleness: DeadBandI64,     // is the value actually changing?
}

impl FeedMonitor {
    fn new(baseline_latency: f64, expected_interval_ns: i64) -> Self {
        FeedMonitor {
            liveness: LivenessI64::builder()
                .span(15)
                .deadline_multiple(5)
                .build(),
            latency: CusumF64::builder(baseline_latency)
                .slack(baseline_latency * 0.05)
                .threshold(baseline_latency * 0.5)
                .min_samples(20)
                .build(),
            rate: EventRateI64::builder()
                .span(15)
                .build(),
            jitter: JitterI64::builder()
                .span(20)
                .build(),
            staleness: DeadBandI64::new(1), // flag if value changes by < 1
        }
    }

    fn on_message(&mut self, now_ns: i64, value: i64, latency_us: f64) {
        self.liveness.update(now_ns);
        self.rate.tick(now_ns);
        self.jitter.update(now_ns);

        if let Some(shift) = self.latency.update(latency_us) {
            if matches!(shift, Direction::Rising) {
                log::warn!("feed latency degraded");
            }
        }

        // Staleness: if DeadBand suppresses the update, the value hasn't moved
        if self.staleness.update(value).is_none() {
            // Value didn't change enough — potentially stale
        }
    }

    fn check(&self, now_ns: i64) -> bool {
        self.liveness.check(now_ns)
    }
}
```

## Recipe: WebSocket Feed Health (Trading)

```rust
use nexus_stats::detection::CusumF64;
use nexus_stats::monitoring::{LivenessI64, EventRateI64};

// Per-exchange feed monitor
let mut liveness = LivenessI64::builder()
    .span(15)
    .deadline_absolute(5_000_000_000)  // 5s absolute timeout
    .build().unwrap();

let mut msg_rate = EventRateI64::builder().span(20).build().unwrap();
let mut latency_cusum = CusumF64::builder(baseline_ws_latency)
    .slack(2.0).threshold(20.0).min_samples(50).build().unwrap();

// On each WebSocket message:
liveness.update(now_ns);
msg_rate.tick(now_ns);
latency_cusum.update(msg_latency_ms);

// On timer tick (100ms from nexus-rt timer driver):
if !liveness.check(now_ns) {
    initiate_reconnect();
}
```

## Primitives Used

| Primitive | What it detects |
|-----------|----------------|
| [Liveness](../algorithms/liveness.md) | Source stopped sending |
| [CUSUM](../algorithms/cusum.md) | Latency shifted |
| [EventRate](../algorithms/event-rate.md) | Message rate changed |
| [Jitter](../algorithms/jitter.md) | Timing became unstable |
| [DeadBand](../algorithms/dead-band.md) | Value stopped changing (stale) |
| [Debounce](../algorithms/debounce.md) | Confirm repeated failures |

## Tips

- **Check liveness on a timer, not on data arrival.** You can't detect
  silence from within the data handler — if nothing arrives, the handler
  never runs. Use a timer driver.

- **Use CUSUM, not thresholds, for degradation.** A fixed "latency > 100ms"
  threshold fires on every spike. CUSUM only fires when the *mean* has shifted.

- **Monitor jitter separately from latency.** A feed with stable 50ms latency
  is fine. A feed that alternates between 10ms and 90ms (same mean!) is
  unstable. Jitter catches this.
