# Use Case: SRE Observability

Error budgets, SLO tracking, resource monitoring (USE method), and
service health for site reliability engineering.

## Recipe: Error Budget / SLO Tracking

```rust
use nexus_stats::monitoring::ErrorRate;
use nexus_stats::control::BoolWindow;

// Counts, a ratio per interval, and a smoothed ratio
let mut error_rate = ErrorRate::builder()
    .span(1000)       // smooth over ~1000 requests
    .build().unwrap();
const BUDGET: f64 = 0.01; // SLO: 99% success = 1% error budget

// Sliding window for the exact rate over the last 128 events
let mut window = BoolWindow::new(128).unwrap();

// On each request, one update each:
let ok = response.status() < 500;
error_rate.update(ok);
window.update(ok);

// Two views:
// error_rate.smoothed_ratio() → smoothed (good for dashboards)
// error_rate.take()           → count and ratio since the last scrape
// window.failure_rate()   → exact over last 128 requests (good for alerting)

if error_rate.smoothed_ratio().is_some_and(|r| r > BUDGET) {
    // Smoothed error rate exceeds 1% → burning budget
}
```

## Recipe: USE Method (Utilization, Saturation, Errors)

```rust
use nexus_stats::monitoring::{CoDel, ErrorRate};
use nexus_stats::smoothing::Ema;

// Per resource (CPU, memory, disk, network):
struct ResourceMonitor {
    utilization: Ema,            // U: how busy (smoothed busy fraction)
    codel: CoDel<i64>,           // S: how queued (if applicable)
    error_rate: ErrorRate,       // E: how broken
}

impl ResourceMonitor {
    fn new() -> Self {
        ResourceMonitor {
            utilization: Ema::builder().span(20).build().unwrap(),
            codel: CoDel::<i64>::builder()
                .target(10_000).interval(1_000_000_000).build().unwrap(),
            error_rate: ErrorRate::builder().span(100).build().unwrap(),
        }
    }

    fn is_healthy(&self) -> bool {
        !matches!(self.utilization.value(), Some(u) if u > 0.80)
    }
}
```

## Recipe: Service Health Composite

```rust
use nexus_stats::Direction;
use nexus_stats::monitoring::ErrorRate;
use nexus_stats::detection::Cusum;
use nexus_stats::control::Debounce;

// Consecutive health check failures → confirmed outage
let mut health_debounce = Debounce::new(3).unwrap();

// Error rate for gradual degradation
let mut errors = ErrorRate::builder().span(200).build().unwrap();

// Latency shift for performance degradation
let mut latency = Cusum::builder(baseline_ms)
    .slack(5.0).threshold(50.0).build().unwrap();

// Overall assessment:
let check_passed = ping_service();
let is_confirmed_down = health_debounce.update(!check_passed);

if is_confirmed_down {
    page_oncall();
} else if matches!(errors.smoothed_ratio(), Some(r) if r > 0.05) {
    alert_warn("elevated error rate");
} else if matches!(latency.update(response_ms), Some(Direction::Rising)) {
    alert_warn("latency degradation");
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| ErrorRate | Error counts (USE) and failure ratio (SRE) |
| BoolWindow | Exact failure rate over last N |
| CoDel | Saturation / queueing (USE method) |
| PollSaturation | Saturation of a consumer thread from poll outcomes (USE method) |
| CUSUM | Latency degradation detection |
| Debounce | Confirm outage (N consecutive failures) |
