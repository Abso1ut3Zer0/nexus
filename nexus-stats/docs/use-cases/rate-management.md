# Use Case: Rate Management

Tracking event rates, detecting rate changes, and monitoring against limits.

Note: active rate *limiting* (token bucket, GCRA, sliding window counter)
lives in the `nexus-rate` crate. This covers the *measurement* side.

## Recipe: Monitor Against Exchange Rate Limits

```rust
use nexus_stats::monitoring::EventRate;
use nexus_stats::smoothing::Ema;

// Track our own order rate
let mut order_rate = EventRate::new(start_ns);

// Smoothed fraction of the exchange limit we are using
let mut limit_util = Ema::builder().span(10).build().unwrap();

// On each order sent:
order_rate.update();

// On a timer, once a second:
let window = order_rate.take(now_ns)?;
limit_util.update(window.rate() / exchange_rate_limit);
if matches!(limit_util.value(), Some(u) if u > 0.80) {  // warn at 80% of the limit
    throttle_order_flow();
}
```

## Recipe: Detect Rate Anomalies

```rust
use nexus_stats::Direction;
use nexus_stats::monitoring::EventRate;
use nexus_stats::detection::Cusum;

let mut rate = EventRate::new(start_ns);
let mut cusum = Cusum::builder(expected_rate)
    .slack(expected_rate * 0.1)
    .threshold(expected_rate * 2.0)
    .build().unwrap();

rate.update();        // per event
// On a timer:
let r = rate.take(now_ns)?.rate();
if let Some(shift) = cusum.update(r).unwrap() {
    match shift {
        Direction::Rising => log::warn!("rate spike detected"),
        Direction::Falling => log::warn!("rate drop detected"),
        Direction::Neutral => {}
    }
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| EventRate | Events per second per window, and the load averages |
| CUSUM | Rate shift detection |
| LevelCrossing | Count rate limit breaches |
