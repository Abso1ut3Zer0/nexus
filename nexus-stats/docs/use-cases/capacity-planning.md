# Use Case: Capacity Planning

Load distribution analysis, trend forecasting, and shard balancing.

## Recipe: Load Distribution Across Shards

```rust
use nexus_stats::frequency::{FlexProportionGlobal, FlexProportionLocal};

// Track what % of traffic each shard handles
let mut global = FlexProportionGlobal::new(100_000).unwrap(); // half-life: 100k events
let mut per_shard = vec![FlexProportionLocal::new(); num_shards];

// On each event routed to shard i:
global.update(&mut per_shard[shard_id]);

// Periodic capacity review:
for (i, shard) in per_shard.iter().enumerate() {
    let pct = shard.fraction(&global);
    if pct > 0.30 {
        log::warn!("shard {i} handles {:.0}% of traffic — consider rebalancing", pct * 100.0);
    }
}
```

## Recipe: Load Trend Forecasting

```rust
use nexus_stats::estimation::Kalman1d;

// Kalman filter for load with velocity (trend)
let mut load = Kalman1d::builder()
    .process_noise(0.5)
    .measurement_noise(10.0)
    .build().unwrap();

if let Some((current, trend)) = load.update(requests_per_sec).unwrap() {
    let forecast_1h = current + trend * 3600.0;
    if forecast_1h > capacity_limit {
        alert_warn("at current trend, capacity exceeded in ~1 hour");
    }
}
```

## Recipe: Top-K Hot Symbols

```rust
use nexus_stats::frequency::TopK;

let mut hot: TopK<String> = TopK::new(10).unwrap();

// On each market data message:
hot.update(symbol.to_string());

// Periodic review:
for (sym, count) in hot.top() {
    println!("{sym}: {count} messages");
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| [FlexProportion](../algorithms/flex-proportion.md) | Per-shard share of recent traffic |
| [Kalman1D](../algorithms/kalman1d.md) | Load forecasting with trend |
| [Holt](../algorithms/holt.md) | Simpler trend forecasting |
| [TopK](../algorithms/topk.md) | Hottest items |
| [TrendAlert](../algorithms/trend-alert.md) | Detect rising load |
