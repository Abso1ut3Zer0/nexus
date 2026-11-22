# Use Case: Rate Management

Tracking event rates, detecting rate changes, and monitoring against limits.

Note: active rate *limiting* (token bucket, GCRA, sliding window counter)
lives in the `nexus-rate` crate. This covers the *measurement* side.

## Recipe: Monitor Against Exchange Rate Limits

```rust
use nexus_stats::monitoring::EventRate;
use nexus_stats::smoothing::Ema;

// Track our own order rate
let mut order_rate = EventRate::builder().span(15).build().unwrap();

// Smoothed fraction of the exchange limit we are using
let mut limit_util = Ema::builder().span(10).build().unwrap();

// On each order sent:
order_rate.update(now_ns);

if let Some(rate) = order_rate.rate() {
    limit_util.update(rate / exchange_rate_limit).unwrap();
    if matches!(limit_util.value(), Some(u) if u > 0.80) {  // warn at 80% of the limit
        throttle_order_flow();
    }
}
```

## Recipe: Detect Rate Anomalies

```rust
use nexus_stats::Direction;
use nexus_stats::monitoring::EventRate;
use nexus_stats::detection::Cusum;

let mut rate = EventRate::builder().span(31).build().unwrap();
let mut cusum = Cusum::builder(expected_rate)
    .slack(expected_rate * 0.1)
    .threshold(expected_rate * 2.0)
    .build().unwrap();

rate.update(now_ns);
if let Some(r) = rate.rate() {
    if let Some(shift) = cusum.update(r).unwrap() {
        match shift {
            Direction::Rising => log::warn!("rate spike detected"),
            Direction::Falling => log::warn!("rate drop detected"),
            Direction::Neutral => {}
        }
    }
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| [EventRate](../algorithms/event-rate.md) | Smoothed rate measurement |
| [CUSUM](../algorithms/cusum.md) | Rate shift detection |
| [LevelCrossing](../algorithms/level-crossing.md) | Count rate limit breaches |
