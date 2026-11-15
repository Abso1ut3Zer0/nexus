# Use Case: SRE Observability

Error budgets, SLO tracking, resource monitoring (USE method), and
service health for site reliability engineering.

## Recipe: Error Budget / SLO Tracking

```rust
use nexus_stats::Condition;
use nexus_stats::monitoring::ErrorRateF64;
use nexus_stats::control::BoolWindow;

// Track error rate with EMA
let mut error_rate = ErrorRateF64::builder()
    .span(1000)       // smooth over ~1000 requests
    .threshold(0.01)  // SLO: 99% success = 1% error budget
    .build().unwrap();

// Sliding window for precise rate (last 100 events)
let mut window = BoolWindow::<2>::new();  // 128-event window

// On each request:
let ok = response.status() < 500;
error_rate.record(ok);
window.record(ok);

// Two views:
// error_rate.error_rate() → smoothed (good for dashboards)
// window.failure_rate()   → exact over last 128 requests (good for alerting)

if let Some(Condition::Degraded) = error_rate.record(ok) {
    // Smoothed error rate exceeds 1% → burning budget
}
```

## Recipe: USE Method (Utilization, Saturation, Errors)

```rust
use nexus_stats::monitoring::{SaturationF64, CoDelI64, ErrorRateF64};

// Per resource (CPU, memory, disk, network):
struct ResourceMonitor {
    utilization: SaturationF64,     // U: how busy
    codel: CoDelI64,     // S: how queued (if applicable)
    error_rate: ErrorRateF64,       // E: how broken
}

impl ResourceMonitor {
    fn new() -> Self {
        ResourceMonitor {
            utilization: SaturationF64::builder()
                .span(20).threshold(0.80).build(),
            codel: CoDelI64::builder()
                .target(10_000).window(1_000_000_000).build(),
            error_rate: ErrorRateF64::builder()
                .span(100).threshold(0.01).build(),
        }
    }

    fn is_healthy(&self) -> bool {
        !self.utilization.is_primed()
            || !matches!(self.utilization.utilization(), Some(u) if u > 0.80)
    }
}
```

## Recipe: Service Health Composite

```rust
use nexus_stats::Direction;
use nexus_stats::monitoring::ErrorRateF64;
use nexus_stats::detection::CusumF64;
use nexus_stats::control::DebounceU32;

// Consecutive health check failures → confirmed outage
let mut health_debounce = DebounceU32::new(3);

// Error rate for gradual degradation
let mut errors = ErrorRateF64::builder()
    .span(200).threshold(0.05).build().unwrap();

// Latency shift for performance degradation
let mut latency = CusumF64::builder(baseline_ms)
    .slack(5.0).threshold(50.0).build().unwrap();

// Overall assessment:
let check_passed = ping_service();
let is_confirmed_down = health_debounce.update(!check_passed);

if is_confirmed_down {
    page_oncall();
} else if matches!(errors.error_rate(), Some(r) if r > 0.05) {
    alert_warn("elevated error rate");
} else if matches!(latency.update(response_ms), Some(Direction::Rising)) {
    alert_warn("latency degradation");
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| [ErrorRate](../algorithms/error-rate.md) | SLO / error budget tracking |
| [BoolWindow](../algorithms/bool-window.md) | Exact failure rate over last N |
| [Saturation](../algorithms/saturation.md) | Utilization (USE method) |
| [CoDel](../algorithms/codel.md) | Saturation / queueing (USE method) |
| [PollSaturation](../algorithms/poll-saturation.md) | Saturation of a consumer thread from poll outcomes (USE method) |
| [CUSUM](../algorithms/cusum.md) | Latency degradation detection |
| [Debounce](../algorithms/debounce.md) | Confirm outage (N consecutive failures) |
| [MaxGauge](../algorithms/max-gauge.md) | Worst-case per scrape interval |
