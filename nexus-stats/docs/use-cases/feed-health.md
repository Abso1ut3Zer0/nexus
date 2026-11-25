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
use nexus_stats::detection::Cusum;
use nexus_stats::monitoring::{Liveness, EventRate, Jitter};
use nexus_stats::control::DeadBand;

struct FeedMonitor {
    liveness: Liveness<i128>, // how long has it been silent?
    latency: Cusum,          // has latency shifted?
    rate: EventRate<i128>,   // how busy is it?
    jitter: Jitter<i64>,          // is timing unstable?
    staleness: DeadBand<i64>,     // is the value actually changing?
}

impl FeedMonitor {
    fn new(start_ns: i128, baseline_latency: f64, expected_interval_ns: i64) -> Self {
        FeedMonitor {
            liveness: Liveness::builder().build().unwrap(), // mean of the last 1,000 gaps
            latency: Cusum::builder(baseline_latency)
                .slack(baseline_latency * 0.05)
                .threshold(baseline_latency * 0.5)
                .min_samples(20)
                .build()
                .unwrap(),
            rate: EventRate::new(start_ns),
            jitter: Jitter::<i64>::new(),
            staleness: DeadBand::<i64>::new(1).unwrap(), // flag if value changes by < 1
        }
    }

    fn on_message(&mut self, now_ns: i128, value: i64, latency_us: f64) {
        self.liveness.update(now_ns);
        self.rate.update();
        self.jitter.update(gap_ns); // time since the previous message

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
use nexus_stats::detection::Cusum;
use nexus_stats::monitoring::{Liveness, EventRate};

// Per-exchange feed monitor
let mut liveness = Liveness::builder().build().unwrap();
let mut msg_rate = EventRate::new(start_ns);   // any `Timestamp`
let mut latency_cusum = Cusum::builder(baseline_ws_latency)
    .slack(2.0).threshold(20.0).min_samples(50).build().unwrap();

// On each WebSocket message:
liveness.update(now_ns);
msg_rate.update();
latency_cusum.update(msg_latency_ms).unwrap();

// On timer tick (100ms from nexus-rt timer driver):
let rate = msg_rate.take(now_ns)?.rate();     // events per second since the last tick
// Silent for 5 s, or for 20 typical gaps: your policy, not the type's.
let quiet = liveness.check(now_ns);
if quiet.is_some_and(|s| s.silence().as_secs() >= 5 || s.ratio() > 20.0) {
    initiate_reconnect();
}
```

## Primitives Used

| Primitive | What it detects |
|-----------|----------------|
| Liveness | How long the source has been silent, in typical gaps |
| CUSUM | Latency shifted |
| EventRate | Events per second per window, and the 1, 5 and 15 minute load |
| Jitter | Timing became unstable |
| DeadBand | Value stopped changing (stale) |
| Debounce | Confirm repeated failures |

## Tips

- **Check liveness on a timer, not on data arrival.** You can't detect
  silence from within the data handler — if nothing arrives, the handler
  never runs. Use a timer driver.

- **Use CUSUM, not thresholds, for degradation.** A fixed "latency > 100ms"
  threshold fires on every spike. CUSUM only fires when the *mean* has shifted.

- **Monitor jitter separately from latency.** A feed with stable 50ms latency
  is fine. A feed that alternates between 10ms and 90ms (same mean!) is
  unstable. Jitter catches this.
