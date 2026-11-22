# Use Case: Network Quality Monitoring

RTT tracking, jitter measurement, packet loss estimation, and bandwidth
estimation for networked systems.

## Recipe: RTT Monitoring (Jacobson/Karels Style)

```rust
use nexus_stats::smoothing::AsymEma;
use nexus_stats::statistics::EwmVar;
use nexus_stats::monitoring::WindowedMin;

// Asymmetric EMA: react fast to RTT increases, slow to decreases
// This is the pattern TCP uses (Jacobson/Karels, RFC 6298)
let mut srtt = AsymEma::builder()
    .alpha_up(0.25)    // fast response to degradation (1/4)
    .alpha_down(0.125) // slow response to improvement (1/8)
    .build().unwrap();

// RTT variance for timeout calculation
let mut rttvar = EwmVar::builder().span(7).build().unwrap();

// Min RTT baseline (BBR-style)
let mut min_rtt = WindowedMin::<f64>::new(10_000_000_000).unwrap(); // 10s window

// On each RTT measurement:
if let Some(smoothed) = srtt.update(rtt_ms).unwrap() {
    min_rtt.update(now_ns, rtt_ms).unwrap();
    // Timeout = smoothed_rtt + 4 × deviation (RFC 6298)
    if let Some(reading) = rttvar.update(rtt_ms) {
        let rto = smoothed + 4.0 * reading.std_dev();
    }
}
```

## Recipe: Jitter Buffer Sizing

```rust
use nexus_stats::monitoring::Jitter;

let mut jitter = Jitter::<f64>::builder().span(16).build().unwrap(); // RFC 3550: alpha=1/16

// On each packet:
let transit = arrival_time - send_time;
jitter.update(transit);

if let Some(j) = jitter.jitter() {
    let buffer_depth = 3.0 * j;  // 3× jitter for buffer sizing
}
```

## Recipe: Bandwidth Estimation

```rust
use nexus_stats::monitoring::WindowedMax;
use nexus_stats::statistics::HarmonicMean;

// Windowed max of delivery rate (BBR-style)
let mut bw_max = WindowedMax::<f64>::new(rtt_window_ns).unwrap();

// Harmonic mean for average throughput
let mut avg_bw = HarmonicMean::new();

// On each delivery acknowledgment:
let delivery_rate = bytes_delivered as f64 / interval_sec;
bw_max.update(now_ns, delivery_rate);
avg_bw.update(delivery_rate);
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| [WindowedMin](../algorithms/windowed-min-max.md) | Baseline RTT (BBR) |
| [WindowedMax](../algorithms/windowed-min-max.md) | Bandwidth estimation (BBR) |
| [Jitter](../algorithms/jitter.md) | Inter-arrival jitter (RFC 3550) |
