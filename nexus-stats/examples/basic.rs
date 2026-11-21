//! Basic usage of nexus-stats: composing CUSUM + EMA + Welford for
//! latency monitoring.
//!
//! Run with: `cargo run --example basic -p nexus-stats`

use nexus_stats::{Direction, detection::Cusum, smoothing::Ema, statistics::Welford};

fn main() {
    // Simulated latency samples (μs): normal around 100, then a shift to 120
    let samples: &[f64] = &[
        98.0, 102.0, 97.0, 103.0, 101.0, 99.0, 100.0, 104.0, 96.0, 101.0, // normal
        98.0, 103.0, 99.0, 102.0, 100.0, 97.0, 101.0, 104.0, 98.0, 100.0, // normal
        118.0, 122.0, 119.0, 121.0, 120.0, 123.0, 117.0, 121.0, 119.0, 122.0, // shifted
        120.0, 118.0, 123.0, 121.0, 119.0, 122.0, 120.0, 117.0, 121.0, 120.0, // shifted
    ];

    // CUSUM: detect when the mean shifts
    let mut cusum = Cusum::builder(100.0)
        .slack(5.0)
        .threshold(30.0)
        .build()
        .unwrap();

    // EMA: smooth the noisy signal
    let mut ema = Ema::builder().span(10).build().unwrap();

    // Welford: track running statistics
    let mut stats = Welford::new();

    println!("sample  raw    ema     mean   std_dev  cusum");
    println!("------  ---    ---     ----   -------  -----");

    for (i, &sample) in samples.iter().enumerate() {
        let shift = cusum.update(sample).unwrap();
        let smoothed = ema.update(sample);
        stats.update(sample);

        let ema_str = smoothed.map_or_else(|| "  -  ".into(), |v| format!("{v:6.1}"));
        let mean_str = stats
            .mean()
            .map_or_else(|| "  -  ".into(), |v| format!("{v:6.1}"));
        let sd_str = stats
            .std_dev()
            .map_or_else(|| "  -  ".into(), |v| format!("{v:6.1}"));
        let shift_str = match shift {
            Some(Direction::Rising) => " ↑ SHIFT",
            Some(Direction::Falling) => " ↓ SHIFT",
            Some(Direction::Neutral) => "",
            None => " (warmup)",
        };

        println!("  {i:3}   {sample:5.1}  {ema_str}  {mean_str}  {sd_str}  {shift_str}");
    }

    println!("\nFinal statistics:");
    println!("  samples: {}", stats.count());
    println!("  mean:    {:.2}", stats.mean().unwrap());
    println!("  std_dev: {:.2}", stats.std_dev().unwrap());
}
