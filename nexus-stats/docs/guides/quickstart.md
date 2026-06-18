# Quick Start

Copy-paste recipes for common patterns.

## Smooth a Noisy Signal

```rust
use nexus_stats::smoothing::EmaF64;

let mut ema = EmaF64::builder().span(20).build().unwrap();

for sample in data {
    if let Some(smoothed) = ema.update(sample) {
        use_smoothed_value(smoothed);
    }
}
```

## Detect When Something Changes

```rust
use nexus_stats::{Direction, detection::CusumF64};

let mut cusum = CusumF64::builder(100.0)  // expected baseline
    .slack(5.0)
    .threshold(50.0)
    .build().unwrap();

for sample in data {
    match cusum.update(sample) {
        Some(Direction::Rising) => println!("value increased!"),
        Some(Direction::Falling) => println!("value decreased!"),
        _ => {}
    }
}
```

## Track Running Statistics

```rust
use nexus_stats::statistics::WelfordF64;

let mut stats = WelfordF64::new();

for sample in data {
    stats.update(sample);
}

println!("mean={:.2}, std_dev={:.2}",
    stats.mean().unwrap(),
    stats.std_dev().unwrap());
```

## Filter Bad Data

```rust
use nexus_stats::detection::{MultiGateF64, Verdict};

let mut gate = MultiGateF64::builder()
    .alpha(0.05)
    .hard_limit_pct(0.50)
    .suspect_z(5.0)
    .min_samples(50)
    .build().unwrap();

for sample in data {
    match gate.update(sample) {
        Some(Verdict::Accept) => process(sample),
        Some(Verdict::Reject) => log_bad(sample),
        _ => {}
    }
}
```

## Monitor a Data Source

```rust
use nexus_stats::monitoring::LivenessI64;

let mut live = LivenessI64::builder()
    .span(15)
    .deadline_multiple(5)
    .build().unwrap();

// On each message:
live.update(now_ns);

// On timer tick:
if !live.check(now_ns) {
    reconnect();
}
```

## Track Queue Health

```rust
use nexus_stats::{Condition, monitoring::CoDelI64};

let mut qd = CoDelI64::builder()
    .target(10_000)       // 10μs max wait
    .window(100_000_000)  // 100ms observation
    .build().unwrap();

// At dequeue:
let wait = now - enqueue_time;
if let Some(Condition::Degraded) = qd.update(now as u64, wait) {
    slow_down();
}
```
