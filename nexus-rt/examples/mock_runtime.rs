//! Market data runtime — plugin, driver, pipeline, latency measurement.
//!
//! Demonstrates the full nexus-rt lifecycle with realistic domain types,
//! then runs 1000 iterations to measure dispatch latency in CPU cycles.
//!
//! Run with:
//! ```bash
//! taskset -c 0 cargo run --release -p nexus-rt --example mock_runtime
//! ```

#![allow(clippy::needless_pass_by_value, clippy::items_after_statements)]

use std::collections::HashMap;
use std::hint::black_box;

use nexus_rt::{
    Handler, Installer, IntoHandler, Local, PipelineBuilder, Plugin, Res, ResMut, Resource, World,
    WorldBuilder,
};

// ── Timing ──────────────────────────────────────────────────────────────

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe {
        let mut aux = 0u32;
        let tsc = core::arch::x86_64::__rdtscp(&raw mut aux);
        core::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn report(label: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "{:<44} {:>8} {:>8} {:>8}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
    );
}

// ── Domain types ────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
struct MarketTick {
    symbol: &'static str,
    price: f64,
}

#[derive(Resource)]
struct PriceCache {
    prices: HashMap<&'static str, f64>,
}

impl PriceCache {
    fn new() -> Self {
        Self {
            prices: HashMap::new(),
        }
    }
}

#[derive(Resource)]
struct SignalBuffer {
    signals: Vec<&'static str>,
}

impl SignalBuffer {
    fn new() -> Self {
        Self {
            signals: Vec::new(),
        }
    }
}

#[derive(Resource)]
struct OrderCount(u64);

/// Optional resource — may or may not be registered.
#[derive(Resource)]
struct RiskLimits {
    max_signals_per_tick: u64,
}

// ── Plugin ──────────────────────────────────────────────────────────────

struct TradingPlugin {
    initial_prices: Vec<(&'static str, f64)>,
    risk_cap: u64,
}

impl Plugin for TradingPlugin {
    fn build(self, world: &mut WorldBuilder) {
        let mut cache = PriceCache::new();
        for (sym, price) in self.initial_prices {
            cache.prices.insert(sym, price);
        }
        world.register(cache);
        world.register(OrderCount(0));
        world.register(SignalBuffer::new());
        world.register(RiskLimits {
            max_signals_per_tick: self.risk_cap,
        });
    }
}

// ── Pipeline steps ──────────────────────────────────────────────────────

/// Compare tick price against cache. Emit signal if delta > threshold.
fn check_signals(
    cache: Res<PriceCache>,
    mut signals: ResMut<SignalBuffer>,
    mut tick_count: Local<u64>,
    tick: MarketTick,
) -> MarketTick {
    *tick_count += 1;
    if let Some(&prev) = cache.prices.get(tick.symbol) {
        let delta = (tick.price - prev).abs();
        if delta > 50.0 {
            signals.signals.push(tick.symbol);
        }
    }
    tick
}

/// Update the price cache with the latest price.
fn update_price(mut cache: ResMut<PriceCache>, tick: MarketTick) -> MarketTick {
    cache.prices.insert(tick.symbol, tick.price);
    tick
}

/// Count accepted trades against risk limits.
fn count_trades(
    limits: Res<RiskLimits>,
    mut signals: ResMut<SignalBuffer>,
    mut orders: ResMut<OrderCount>,
    _tick: MarketTick,
) {
    let cap = limits.max_signals_per_tick;
    for _symbol in signals.signals.drain(..) {
        if orders.0 < cap {
            orders.0 += 1;
        }
    }
}

// ── Driver ──────────────────────────────────────────────────────────────

struct MarketDataInstaller;

struct MarketDataHandle {
    pipeline: Box<dyn Handler<MarketTick>>,
}

impl Installer for MarketDataInstaller {
    type Poller = MarketDataHandle;

    fn install(self, world: &mut WorldBuilder) -> MarketDataHandle {
        let r = world.registry();
        let pipeline = PipelineBuilder::<MarketTick>::new()
            .then(check_signals, r)
            .then(update_price, r)
            .then(count_trades, r)
            .build();
        MarketDataHandle {
            pipeline: Box::new(pipeline),
        }
    }
}

impl MarketDataHandle {
    /// Process a batch of market ticks.
    ///
    /// Advances sequence once per batch — all ticks share the same sequence
    /// number. For per-event change detection, move `next_sequence()` inside
    /// the loop.
    fn poll(&mut self, world: &mut World, ticks: &[MarketTick]) {
        if ticks.is_empty() {
            return;
        }
        world.next_sequence();
        for tick in ticks {
            self.pipeline.run(world, *tick);
        }
    }
}

// ── main ────────────────────────────────────────────────────────────────

fn main() {
    // -- Build ----------------------------------------------------------------

    let mut wb = WorldBuilder::new();
    wb.install_plugin(TradingPlugin {
        initial_prices: vec![("BTC", 50_000.0), ("ETH", 3_000.0)],
        risk_cap: 100,
    });
    let mut md = wb.install_driver(MarketDataInstaller);
    let mut world = wb.build();

    // -- Correctness check ----------------------------------------------------

    let ticks = [
        MarketTick {
            symbol: "BTC",
            price: 50_100.0,
        }, // delta=100 > 50 → signal
        MarketTick {
            symbol: "ETH",
            price: 3_010.0,
        }, // delta=10 < 50 → no signal
        MarketTick {
            symbol: "BTC",
            price: 49_900.0,
        }, // delta=200 > 50 → signal
    ];

    md.poll(&mut world, &ticks);

    // 2 signals accepted, risk cap=100 so both go through.
    assert_eq!(world.resource::<OrderCount>().0, 2);

    println!("Correctness checks passed.\n");

    // Standalone handler for dispatch benchmarking.
    fn on_signal(signals: Res<SignalBuffer>, _event: ()) {
        black_box(signals.signals.len());
    }
    let mut signal_handler = on_signal.into_handler(world.registry());

    // -- Latency measurement --------------------------------------------------

    const WARMUP: usize = 1_000;
    const ITERATIONS: usize = 1_000;

    // Ticks that exercise the full pipeline path (signal detection + cache write).
    let bench_ticks = [
        MarketTick {
            symbol: "BTC",
            price: 50_100.0,
        },
        MarketTick {
            symbol: "ETH",
            price: 3_100.0,
        },
        MarketTick {
            symbol: "BTC",
            price: 50_200.0,
        },
        MarketTick {
            symbol: "ETH",
            price: 3_200.0,
        },
    ];

    println!(
        "=== nexus-rt Dispatch Latency (cycles, {} iterations) ===\n",
        ITERATIONS
    );
    println!(
        "{:<44} {:>8} {:>8} {:>8}",
        "Operation", "p50", "p99", "p999"
    );
    println!("{}", "-".repeat(72));

    // Single tick through dyn pipeline
    {
        let tick = bench_ticks[0];
        for _ in 0..WARMUP {
            world.next_sequence();
            md.pipeline.run(&mut world, black_box(tick));
        }
        let mut samples = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            world.next_sequence();
            let start = rdtsc_start();
            md.pipeline.run(&mut world, black_box(tick));
            let end = rdtsc_end();
            samples.push(end.wrapping_sub(start));
        }
        report("single tick (dyn pipeline, 3 stages)", &mut samples);
    }

    // Standalone handler (1 param, Res<T>)
    {
        for _ in 0..WARMUP {
            black_box(());
            signal_handler.run(&mut world, ());
        }
        let mut samples = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let start = rdtsc_start();
            black_box(());
            signal_handler.run(&mut world, ());
            let end = rdtsc_end();
            samples.push(end.wrapping_sub(start));
        }
        report("handler dispatch (1 param, Res<T>)", &mut samples);
    }

    // 4-tick batch through driver poll
    {
        for _ in 0..WARMUP {
            md.poll(&mut world, &bench_ticks);
        }
        let mut samples = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let start = rdtsc_start();
            md.poll(&mut world, black_box(&bench_ticks));
            let end = rdtsc_end();
            samples.push(end.wrapping_sub(start));
        }
        let mut per_tick: Vec<u64> = samples
            .iter()
            .map(|&s| s / bench_ticks.len() as u64)
            .collect();
        report("4-tick poll (total)", &mut samples);
        report("4-tick poll (per tick)", &mut per_tick);
    }

    println!();
}
