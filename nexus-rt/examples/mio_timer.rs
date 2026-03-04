//! Echo server — timer-driven heartbeat with TCP echo clients.
//!
//! Demonstrates:
//! - World as the application (resources = state, handlers = behavior)
//! - Timer and IO drivers cooperating (heartbeat drives IO)
//! - Handler templates for zero-lookup instantiation on the hot path
//! - Context-owning callbacks (`CallbackTemplate` with per-connection index)
//! - Move-out-fire handler lifecycle with self-re-registration
//! - Pure polling event loop (no registration in the loop body)
//!
//! Flow:
//!   heartbeat timer writes "ping\n" to all connections
//!   → background echo clients read and echo back
//!   → server on_echo handler reads the echoed data
//!
//! Run with:
//! ```bash
//! taskset -c 0 cargo run --release -p nexus-rt --example mio_timer --features mio,timer
//! ```

#![allow(clippy::needless_pass_by_value, clippy::items_after_statements)]

use std::hint::black_box;
use std::io::{Read, Write};
use std::net::SocketAddr;
use std::time::{Duration, Instant};

use nexus_rt::{
    CallbackTemplate, IntoCallback, IntoHandler, MioDriver, MioInstaller, MioPoller, RegistryRef,
    Res, ResMut, TimerInstaller, TimerPoller, TimerWheel, WorldBuilder, callback_blueprint,
};

// ── Timing ──────────────────────────────────────────────────────────────

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_start() -> u64 {
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_end() -> u64 {
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
        "{:<52} {:>8} {:>8} {:>8}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
    );
}

// ── Constants ───────────────────────────────────────────────────────────

const CLIENT_COUNT: u64 = 3;
const HEARTBEAT_LIMIT: u64 = 5;
const HEARTBEAT_INTERVAL: Duration = Duration::from_millis(50);

// ── Domain types (World resources = application state) ───────────────────

struct Listener(mio::net::TcpListener);

struct Connections(Vec<mio::net::TcpStream>);

struct Stats {
    accepts: u64,
    echoes: u64,
    heartbeats: u64,
}

// ── Blueprint (template key for per-connection echo handlers) ───────────

callback_blueprint!(OnEcho, usize, mio::event::Event);

// ── Handlers ────────────────────────────────────────────────────────────

/// Startup handler — runs once after build to wire drivers to sources.
///
/// Uses `RegistryRef` here since startup is a cold path (runs once).
fn startup(
    mut driver: ResMut<MioDriver>,
    mut listener: ResMut<Listener>,
    mut wheel: ResMut<TimerWheel>,
    reg: RegistryRef,
    _event: (),
) {
    // Register on_accept for the listener.
    let h = on_accept.into_handler(&reg);
    let token = driver.insert(Box::new(h));
    driver
        .registry()
        .register(&mut listener.0, token.into(), mio::Interest::READABLE)
        .expect("register listener");

    // Schedule initial heartbeat.
    let hb = heartbeat.into_handler(&reg);
    let now = Instant::now();
    wheel.schedule_forget(now + HEARTBEAT_INTERVAL, Box::new(hb));
}

fn on_accept(
    mut driver: ResMut<MioDriver>,
    mut listener: ResMut<Listener>,
    mut conns: ResMut<Connections>,
    mut stats: ResMut<Stats>,
    echo_tpl: Res<CallbackTemplate<OnEcho>>,
    reg: RegistryRef,
    _event: mio::event::Event,
) {
    while let Ok((mut stream, _)) = listener.0.accept() {
        let idx = conns.0.len();
        // Template instantiation: ~5 cycles, zero HashMap lookups.
        // This is the high-value case — on_accept stamps out one handler
        // per connection. With 10k connections, that's 10k generations
        // at ~5 cycles each vs ~30 cycles each with into_callback.
        let h = echo_tpl.generate(idx);
        let token = driver.insert(Box::new(h));
        driver
            .registry()
            .register(&mut stream, token.into(), mio::Interest::READABLE)
            .expect("register stream");
        conns.0.push(stream);
        stats.accepts += 1;
    }
    // Self-re-register: RegistryRef is fine here — one handler created,
    // and the accept syscall dominates the cost anyway.
    let h = on_accept.into_handler(&reg);
    let token = driver.insert(Box::new(h));
    driver
        .registry()
        .reregister(&mut listener.0, token.into(), mio::Interest::READABLE)
        .expect("reregister listener");
}

fn on_echo(
    idx: &mut usize,
    mut conns: ResMut<Connections>,
    mut stats: ResMut<Stats>,
    mut driver: ResMut<MioDriver>,
    reg: RegistryRef,
    _event: mio::event::Event,
) {
    let stream = &mut conns.0[*idx];
    let mut buf = [0u8; 128];
    loop {
        match Read::read(stream, &mut buf) {
            Ok(0) => return,
            Ok(n) => stats.echoes += n as u64,
            Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
            Err(_) => return,
        }
    }
    // Re-register for next readable.
    let h = on_echo.into_callback(*idx, &reg);
    let token = driver.insert(Box::new(h));
    driver
        .registry()
        .reregister(stream, token.into(), mio::Interest::READABLE)
        .expect("reregister stream");
}

fn heartbeat(
    mut conns: ResMut<Connections>,
    mut stats: ResMut<Stats>,
    mut wheel: ResMut<TimerWheel>,
    reg: RegistryRef,
    now: Instant,
) {
    stats.heartbeats += 1;
    for stream in &mut conns.0 {
        let _ = Write::write_all(stream, b"ping\n");
    }
    if stats.heartbeats < HEARTBEAT_LIMIT {
        let h = heartbeat.into_handler(&reg);
        wheel.schedule_forget(now + HEARTBEAT_INTERVAL, Box::new(h));
    }
}

// ── Benchmark-only handlers (minimal work, no IO) ───────────────────────

fn bench_io(mut stats: ResMut<Stats>, _event: mio::event::Event) {
    stats.accepts += 1;
}

fn bench_timer(mut stats: ResMut<Stats>, _now: Instant) {
    stats.heartbeats += 1;
}

// ── main ────────────────────────────────────────────────────────────────

fn main() {
    // == Build (World = App) ==================================================

    let mut wb = WorldBuilder::new();
    wb.register(Stats {
        accepts: 0,
        echoes: 0,
        heartbeats: 0,
    });
    wb.register(Connections(Vec::new()));

    let addr: SocketAddr = "127.0.0.1:0".parse().expect("parse addr");
    let listener = mio::net::TcpListener::bind(addr).expect("bind listener");
    let listen_addr = listener.local_addr().expect("local addr");
    wb.register(Listener(listener));

    let mut mio_poller: MioPoller = wb.install_driver(MioInstaller::new());
    let mut timer_poller: TimerPoller = wb.install_driver(TimerInstaller::new(64));

    // Pre-resolve the echo handler template — HashMap lookups happen once here.
    // on_accept stamps out per-connection handlers at ~5 cycles each (zero lookups).
    let echo_tpl = CallbackTemplate::<OnEcho>::new(on_echo, wb.registry());
    wb.register(echo_tpl);

    let mut world = wb.build();

    // == Startup ==============================================================

    world.run_startup(startup);

    // Spawn echo clients.
    for _ in 0..CLIENT_COUNT {
        std::thread::spawn(move || {
            let mut stream = std::net::TcpStream::connect(listen_addr).expect("client connect");
            let mut buf = [0u8; 128];
            while let Ok(n) = stream.read(&mut buf) {
                if n == 0 {
                    break;
                }
                stream.write_all(&buf[..n]).ok();
            }
        });
    }

    // == Event loop (pure polling) ============================================

    println!("=== Echo server ({CLIENT_COUNT} clients, {HEARTBEAT_LIMIT} heartbeats) ===\n");

    loop {
        let now = Instant::now();
        let timeout = timer_poller
            .next_deadline(&world)
            .map(|d| d.saturating_duration_since(now))
            .or(Some(Duration::from_millis(100)));

        mio_poller.poll(&mut world, timeout).expect("mio poll");
        timer_poller.poll(&mut world, Instant::now());

        let stats = world.resource::<Stats>();
        if stats.heartbeats >= HEARTBEAT_LIMIT && stats.accepts >= CLIENT_COUNT {
            break;
        }
    }

    // == Results ==============================================================

    let stats = world.resource::<Stats>();
    println!("  accepts:    {}", stats.accepts);
    println!("  echoes:     {} bytes", stats.echoes);
    println!("  heartbeats: {}", stats.heartbeats);
    assert!(
        stats.accepts >= CLIENT_COUNT,
        "expected at least {CLIENT_COUNT} accepts, got {}",
        stats.accepts,
    );
    assert_eq!(stats.heartbeats, HEARTBEAT_LIMIT);
    assert!(stats.echoes > 0, "expected some echoed bytes");
    println!("\nCorrectness passed.\n");

    // == Latency measurement ==================================================

    // Reset stats and clean up echo server state for isolated benchmarks.
    {
        let stats = world.resource_mut::<Stats>();
        stats.accepts = 0;
        stats.echoes = 0;
        stats.heartbeats = 0;
    }
    // Drop echo connections. Listener deregistration skipped — stale
    // tokens are harmless, and the benchmark uses a fresh listener.
    world.resource_mut::<Connections>().0.clear();

    // Fresh listener + client for benchmark isolation.
    let bench_addr: SocketAddr = "127.0.0.1:0".parse().expect("parse bench addr");
    let mut bench_listener = mio::net::TcpListener::bind(bench_addr).expect("bind bench listener");
    let bench_listen_addr = bench_listener.local_addr().expect("bench local addr");
    let _bench_client =
        std::net::TcpStream::connect(bench_listen_addr).expect("bench client connect");

    const WARMUP: usize = 5_000;
    const ITERATIONS: usize = 10_000;

    println!("=== Dispatch Latency (cycles, {ITERATIONS} iterations) ===\n");
    println!(
        "{:<52} {:>8} {:>8} {:>8}",
        "Operation", "p50", "p99", "p999"
    );
    println!("{}", "-".repeat(80));

    // 1. Empty mio poll (zero timeout, no pending events).
    {
        for _ in 0..WARMUP {
            mio_poller
                .poll(&mut world, Some(Duration::ZERO))
                .expect("warmup");
        }
        let mut samples = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let start = rdtsc_start();
            black_box(
                mio_poller
                    .poll(&mut world, Some(Duration::ZERO))
                    .expect("poll"),
            );
            let end = rdtsc_end();
            samples.push(end.wrapping_sub(start));
        }
        report("mio poll (empty, zero timeout)", &mut samples);
    }

    // 2. IO dispatch (1 TCP readable event).
    {
        let h = bench_io.into_handler(world.registry());
        let driver = world.resource_mut::<MioDriver>();
        let token = driver.insert(Box::new(h));
        driver
            .registry()
            .register(&mut bench_listener, token.into(), mio::Interest::READABLE)
            .expect("register bench listener");
        mio_poller
            .poll(&mut world, Some(Duration::from_millis(100)))
            .expect("initial bench IO poll");

        for _ in 0..WARMUP {
            let h = bench_io.into_handler(world.registry());
            let driver = world.resource_mut::<MioDriver>();
            let t = driver.insert(Box::new(h));
            driver
                .registry()
                .reregister(&mut bench_listener, t.into(), mio::Interest::READABLE)
                .expect("reregister warmup");
            mio_poller
                .poll(&mut world, Some(Duration::from_millis(100)))
                .expect("warmup IO poll");
        }
        let mut samples = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let h = bench_io.into_handler(world.registry());
            let driver = world.resource_mut::<MioDriver>();
            let t = driver.insert(Box::new(h));
            driver
                .registry()
                .reregister(&mut bench_listener, t.into(), mio::Interest::READABLE)
                .expect("reregister bench");

            let start = rdtsc_start();
            black_box(
                mio_poller
                    .poll(&mut world, Some(Duration::from_millis(100)))
                    .expect("bench IO poll"),
            );
            let end = rdtsc_end();
            samples.push(end.wrapping_sub(start));
        }
        report("mio poll (1 TCP readable, fire handler)", &mut samples);

        world
            .resource_mut::<MioDriver>()
            .registry()
            .deregister(&mut bench_listener)
            .expect("deregister bench listener");
    }

    // 3. Timer dispatch (1 expired one-shot).
    {
        for _ in 0..WARMUP {
            let h = bench_timer.into_handler(world.registry());
            let now = Instant::now();
            world
                .resource_mut::<TimerWheel>()
                .schedule_forget(now, Box::new(h));
            timer_poller.poll(&mut world, now);
        }
        let mut samples = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let h = bench_timer.into_handler(world.registry());
            let now = Instant::now();
            world
                .resource_mut::<TimerWheel>()
                .schedule_forget(now, Box::new(h));

            let start = rdtsc_start();
            black_box(timer_poller.poll(&mut world, now));
            let end = rdtsc_end();
            samples.push(end.wrapping_sub(start));
        }
        report("timer poll (1 expired one-shot)", &mut samples);
    }

    // 4. Combined loop iteration (1 IO event + 1 timer).
    {
        let h = bench_io.into_handler(world.registry());
        let driver = world.resource_mut::<MioDriver>();
        let token = driver.insert(Box::new(h));
        driver
            .registry()
            .register(&mut bench_listener, token.into(), mio::Interest::READABLE)
            .expect("register combined");
        mio_poller
            .poll(&mut world, Some(Duration::from_millis(100)))
            .expect("initial combined poll");

        for _ in 0..WARMUP {
            let h = bench_io.into_handler(world.registry());
            let driver = world.resource_mut::<MioDriver>();
            let t = driver.insert(Box::new(h));
            driver
                .registry()
                .reregister(&mut bench_listener, t.into(), mio::Interest::READABLE)
                .expect("reregister combined warmup");

            let h = bench_timer.into_handler(world.registry());
            let now = Instant::now();
            world
                .resource_mut::<TimerWheel>()
                .schedule_forget(now, Box::new(h));

            let timeout = timer_poller
                .next_deadline(&world)
                .map(|d| d.saturating_duration_since(now));
            mio_poller
                .poll(&mut world, timeout)
                .expect("combined warmup");
            timer_poller.poll(&mut world, Instant::now());
        }
        let mut samples = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let h = bench_io.into_handler(world.registry());
            let driver = world.resource_mut::<MioDriver>();
            let t = driver.insert(Box::new(h));
            driver
                .registry()
                .reregister(&mut bench_listener, t.into(), mio::Interest::READABLE)
                .expect("reregister combined bench");

            let h = bench_timer.into_handler(world.registry());
            let now = Instant::now();
            world
                .resource_mut::<TimerWheel>()
                .schedule_forget(now, Box::new(h));

            let start = rdtsc_start();
            let timeout = timer_poller
                .next_deadline(&world)
                .map(|d| d.saturating_duration_since(now));
            black_box(mio_poller.poll(&mut world, timeout).expect("combined poll"));
            black_box(timer_poller.poll(&mut world, Instant::now()));
            let end = rdtsc_end();
            samples.push(end.wrapping_sub(start));
        }
        report("combined loop (1 IO + 1 timer)", &mut samples);
    }

    println!();
    let stats = world.resource::<Stats>();
    println!(
        "Total benchmark events: {} IO, {} timer",
        stats.accepts, stats.heartbeats,
    );
}
