//! Profiling benchmark for SPSC ring buffer performance.
//!
//! Compares nexus_queue::spsc::bounded against rtrb.
//!
//! Run with:
//!   cargo bench --bench profile_spsc_bounded
//!
//! Or for perf analysis:
//!   cargo build --release --bench profile_spsc_bounded
//!   perf stat -e cycles,instructions,cache-misses,branch-misses \
//!       ./target/release/deps/profile_spsc_bounded-*

use std::hint::black_box;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

const COUNT: u64 = 10_000_000;
const CAPACITY: usize = 1024;
const ITERATIONS: usize = 5;

// Latency test parameters
const LATENCY_SAMPLES: usize = 100_000;
const LATENCY_WARMUP: usize = 10_000;

/// 256-byte message for realistic trading system benchmarks
#[derive(Debug, Clone, Copy)]
#[repr(C, align(64))] // Cache-line aligned
struct Message {
    sequence: u64,
    _payload: [u8; 248], // Pad to 256 bytes total
}

impl Message {
    #[inline]
    fn new(seq: u64) -> Self {
        Self {
            sequence: seq,
            _payload: [0u8; 248],
        }
    }
}

// Verify size at compile time
const _: () = assert!(std::mem::size_of::<Message>() == 256);

fn bench_nexus_spsc() -> Duration {
    use nexus_queue::spsc::bounded;

    let (mut producer, mut consumer) = bounded::ring_buffer::<Message>(CAPACITY);
    let done = Arc::new(AtomicBool::new(false));
    let done_clone = done.clone();

    let producer_handle = thread::spawn(move || {
        let start = Instant::now();
        for i in 0..COUNT {
            let msg = Message::new(i);
            while producer.push(msg).is_err() {
                std::hint::spin_loop();
            }
        }
        done_clone.store(true, Ordering::Release);
        start.elapsed()
    });

    let consumer_handle = thread::spawn(move || {
        let mut received = 0u64;
        loop {
            if let Some(_msg) = consumer.pop() {
                received += 1;
                if received == COUNT {
                    break;
                }
            } else if done.load(Ordering::Acquire) {
                while consumer.pop().is_some() {
                    received += 1;
                }
                break;
            }
        }
        received
    });

    let producer_time = producer_handle.join().unwrap();
    let received = consumer_handle.join().unwrap();
    assert_eq!(received, COUNT);
    producer_time
}

fn bench_rtrb() -> Duration {
    use rtrb::RingBuffer;

    let (mut producer, mut consumer) = RingBuffer::<Message>::new(CAPACITY);
    let done = Arc::new(AtomicBool::new(false));
    let done_clone = done.clone();

    let producer_handle = thread::spawn(move || {
        let start = Instant::now();
        for i in 0..COUNT {
            let msg = Message::new(i);
            while producer.push(msg).is_err() {
                std::hint::spin_loop();
            }
        }
        done_clone.store(true, Ordering::Release);
        start.elapsed()
    });

    let consumer_handle = thread::spawn(move || {
        let mut received = 0u64;
        loop {
            if consumer.pop().is_ok() {
                received += 1;
                if received == COUNT {
                    break;
                }
            } else if done.load(Ordering::Acquire) {
                while consumer.pop().is_ok() {
                    received += 1;
                }
                break;
            }
        }
        received
    });

    let producer_time = producer_handle.join().unwrap();
    let received = consumer_handle.join().unwrap();
    assert_eq!(received, COUNT);
    producer_time
}

// Isolated push benchmark - no cross-thread coordination
fn bench_push_only_nexus_spsc() -> Duration {
    use nexus_queue::spsc::bounded;

    let (mut producer, mut consumer) = bounded::ring_buffer::<Message>(CAPACITY);

    // Pre-fill half
    for i in 0..(CAPACITY / 2) as u64 {
        producer.push(Message::new(i)).unwrap();
    }

    let start = Instant::now();
    for i in 0..COUNT {
        // Push one, pop one - keeps buffer half full
        producer.push(black_box(Message::new(i))).unwrap();
        black_box(consumer.pop());
    }
    start.elapsed()
}

fn bench_push_only_rtrb() -> Duration {
    use rtrb::RingBuffer;

    let (mut producer, mut consumer) = RingBuffer::<Message>::new(CAPACITY);

    // Pre-fill half
    for i in 0..(CAPACITY / 2) as u64 {
        producer.push(Message::new(i)).unwrap();
    }

    let start = Instant::now();
    for i in 0..COUNT {
        producer.push(black_box(Message::new(i))).unwrap();
        let _ = black_box(consumer.pop());
    }
    start.elapsed()
}

// ============================================================================
// LATENCY BENCHMARKS
// ============================================================================

/// Latency stats
struct LatencyStats {
    samples: Vec<u64>, // in cycles (RDTSC) or nanoseconds
}

impl LatencyStats {
    fn new(mut samples: Vec<u64>) -> Self {
        samples.sort_unstable();
        Self { samples }
    }

    fn min(&self) -> u64 {
        self.samples[0]
    }

    fn max(&self) -> u64 {
        *self.samples.last().unwrap()
    }

    fn median(&self) -> u64 {
        self.samples[self.samples.len() / 2]
    }

    fn percentile(&self, p: f64) -> u64 {
        let idx = ((p / 100.0) * self.samples.len() as f64) as usize;
        self.samples[idx.min(self.samples.len() - 1)]
    }
}

/// Ping-pong latency: measures true round-trip time
///
/// Producer sends message with timestamp, then busy-waits for response.
/// Consumer receives, immediately sends back on return queue.
/// This eliminates queue buildup and measures actual latency.
fn bench_latency_pingpong_nexus_spsc() -> LatencyStats {
    use nexus_queue::spsc::bounded;

    // Two queues for ping-pong
    let (mut prod_send, mut cons_recv) = bounded::ring_buffer::<u64>(64);
    let (mut cons_send, mut prod_recv) = bounded::ring_buffer::<u64>(64);

    let total_samples = LATENCY_WARMUP + LATENCY_SAMPLES;

    let consumer_handle = thread::spawn(move || {
        for _ in 0..total_samples {
            // Wait for message
            let ts = loop {
                if let Some(ts) = cons_recv.pop() {
                    break ts;
                }
                std::hint::spin_loop();
            };
            // Echo it back immediately
            while cons_send.push(ts).is_err() {
                std::hint::spin_loop();
            }
        }
    });

    let mut samples = Vec::with_capacity(LATENCY_SAMPLES);

    // Producer: send timestamp, wait for echo, measure round-trip
    for i in 0..total_samples {
        let send_time = rdtsc();

        while prod_send.push(send_time).is_err() {
            std::hint::spin_loop();
        }

        // Wait for response
        let _echo = loop {
            if let Some(ts) = prod_recv.pop() {
                break ts;
            }
            std::hint::spin_loop();
        };

        let recv_time = rdtsc();

        // Skip warmup samples
        if i >= LATENCY_WARMUP {
            // Round-trip / 2 for one-way latency estimate
            samples.push((recv_time - send_time) / 2);
        }
    }

    consumer_handle.join().unwrap();
    LatencyStats::new(samples)
}

fn bench_latency_pingpong_rtrb() -> LatencyStats {
    use rtrb::RingBuffer;

    let (mut prod_send, mut cons_recv) = RingBuffer::<u64>::new(64);
    let (mut cons_send, mut prod_recv) = RingBuffer::<u64>::new(64);

    let total_samples = LATENCY_WARMUP + LATENCY_SAMPLES;

    let consumer_handle = thread::spawn(move || {
        for _ in 0..total_samples {
            let ts = loop {
                if let Ok(ts) = cons_recv.pop() {
                    break ts;
                }
                std::hint::spin_loop();
            };
            while cons_send.push(ts).is_err() {
                std::hint::spin_loop();
            }
        }
    });

    let mut samples = Vec::with_capacity(LATENCY_SAMPLES);

    for i in 0..total_samples {
        let send_time = rdtsc();

        while prod_send.push(send_time).is_err() {
            std::hint::spin_loop();
        }

        let _echo = loop {
            if let Ok(ts) = prod_recv.pop() {
                break ts;
            }
            std::hint::spin_loop();
        };

        let recv_time = rdtsc();

        if i >= LATENCY_WARMUP {
            samples.push((recv_time - send_time) / 2);
        }
    }

    consumer_handle.join().unwrap();
    LatencyStats::new(samples)
}

/// One-way latency with atomic acknowledgment
///
/// Producer sends, consumer receives and signals via atomic.
/// Measures true one-way latency without ping-pong overhead.
fn bench_latency_oneway_nexus_spsc() -> LatencyStats {
    use nexus_queue::spsc::bounded;

    let (mut producer, mut consumer) = bounded::ring_buffer_uncached::<u64>(2);

    // Consumer signals when it has received
    let consumer_received = Arc::new(AtomicU64::new(0));
    let consumer_received_clone = consumer_received.clone();

    let total_samples = LATENCY_WARMUP + LATENCY_SAMPLES;

    let consumer_handle = thread::spawn(move || {
        for expected in 1..=total_samples as u64 {
            // Spin until we receive
            loop {
                if consumer.pop().is_some() {
                    // Signal that we received
                    consumer_received_clone.store(expected, Ordering::Release);
                    break;
                }
                std::hint::spin_loop();
            }
        }
    });

    let mut samples = Vec::with_capacity(LATENCY_SAMPLES);

    for i in 1..=total_samples as u64 {
        let send_time = rdtsc();

        producer.push(i).unwrap();

        // Wait for consumer to receive
        while consumer_received.load(Ordering::Acquire) < i {
            std::hint::spin_loop();
        }

        let recv_time = rdtsc();

        if i > LATENCY_WARMUP as u64 {
            samples.push(recv_time - send_time);
        }
    }

    consumer_handle.join().unwrap();
    LatencyStats::new(samples)
}

fn bench_latency_oneway_rtrb() -> LatencyStats {
    use rtrb::RingBuffer;

    let (mut producer, mut consumer) = RingBuffer::<u64>::new(2);

    let consumer_received = Arc::new(AtomicU64::new(0));
    let consumer_received_clone = consumer_received.clone();

    let total_samples = LATENCY_WARMUP + LATENCY_SAMPLES;

    let consumer_handle = thread::spawn(move || {
        for expected in 1..=total_samples as u64 {
            loop {
                if consumer.pop().is_ok() {
                    consumer_received_clone.store(expected, Ordering::Release);
                    break;
                }
                std::hint::spin_loop();
            }
        }
    });

    let mut samples = Vec::with_capacity(LATENCY_SAMPLES);

    for i in 1..=total_samples as u64 {
        let send_time = rdtsc();

        producer.push(i).unwrap();

        while consumer_received.load(Ordering::Acquire) < i {
            std::hint::spin_loop();
        }

        let recv_time = rdtsc();

        if i > LATENCY_WARMUP as u64 {
            samples.push(recv_time - send_time);
        }
    }

    consumer_handle.join().unwrap();
    LatencyStats::new(samples)
}

/// High-precision timestamp using RDTSC
#[inline]
fn rdtsc() -> u64 {
    #[cfg(target_arch = "x86_64")]
    {
        unsafe { core::arch::x86_64::_rdtsc() }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        use std::time::Instant;
        static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
        let start = START.get_or_init(Instant::now);
        start.elapsed().as_nanos() as u64
    }
}

fn print_results(name: &str, times: &[Duration]) {
    let total_ns: u128 = times.iter().map(|d| d.as_nanos()).sum();
    let avg_ns = total_ns / times.len() as u128;
    let throughput = (COUNT as u128 * 1_000_000_000) / avg_ns;

    let min = times.iter().min().unwrap();
    let max = times.iter().max().unwrap();

    println!(
        "{:20} avg: {:>8.2}ms  ({:>6.1} Melem/s)  min: {:>8.2}ms  max: {:>8.2}ms",
        name,
        avg_ns as f64 / 1_000_000.0,
        throughput as f64 / 1_000_000.0,
        min.as_secs_f64() * 1000.0,
        max.as_secs_f64() * 1000.0,
    );
}

fn print_latency_results(name: &str, stats: &LatencyStats) {
    #[cfg(target_arch = "x86_64")]
    let unit = "cycles";
    #[cfg(not(target_arch = "x86_64"))]
    let unit = "ns";

    println!(
        "{:20} min: {:>6}  p50: {:>6}  p99: {:>6}  p99.9: {:>6}  max: {:>6} {}",
        name,
        stats.min(),
        stats.median(),
        stats.percentile(99.0),
        stats.percentile(99.9),
        stats.max(),
        unit,
    );
}

fn main() {
    println!(
        "=== Message size: {} bytes ===\n",
        std::mem::size_of::<Message>()
    );
    println!("\n=== Single-threaded push+pop (no contention) ===");
    println!("Each iteration: {} ops\n", COUNT);

    // Warmup
    let _ = bench_push_only_nexus_spsc();
    let _ = bench_push_only_rtrb();

    let mut nexus_times = Vec::with_capacity(ITERATIONS);
    let mut rtrb_times = Vec::with_capacity(ITERATIONS);

    // Interleave to avoid ordering effects
    for _ in 0..ITERATIONS {
        nexus_times.push(bench_push_only_nexus_spsc());
        rtrb_times.push(bench_push_only_rtrb());
    }

    print_results("nexus_spsc", &nexus_times);
    print_results("rtrb", &rtrb_times);

    println!("\n=== Cross-thread throughput ===");
    println!("Each iteration: {} ops\n", COUNT);

    // Warmup
    let _ = bench_nexus_spsc();
    let _ = bench_rtrb();

    let mut nexus_times = Vec::with_capacity(ITERATIONS);
    let mut rtrb_times = Vec::with_capacity(ITERATIONS);

    for _ in 0..ITERATIONS {
        nexus_times.push(bench_nexus_spsc());
        rtrb_times.push(bench_rtrb());
    }

    print_results("nexus_spsc", &nexus_times);
    print_results("rtrb", &rtrb_times);

    println!("\n=== Cross-thread latency (ping-pong, round-trip/2) ===");
    println!("Samples: {}, Warmup: {}\n", LATENCY_SAMPLES, LATENCY_WARMUP);

    // Warmup
    let _ = bench_latency_pingpong_nexus_spsc();
    let _ = bench_latency_pingpong_rtrb();

    let nexus_latency = bench_latency_pingpong_nexus_spsc();
    let rtrb_latency = bench_latency_pingpong_rtrb();

    print_latency_results("nexus_spsc", &nexus_latency);
    print_latency_results("rtrb", &rtrb_latency);

    println!("\n=== Cross-thread latency (one-way with atomic ack) ===");
    println!("Samples: {}, Warmup: {}\n", LATENCY_SAMPLES, LATENCY_WARMUP);

    // Warmup
    let _ = bench_latency_oneway_nexus_spsc();
    let _ = bench_latency_oneway_rtrb();

    let nexus_latency = bench_latency_oneway_nexus_spsc();
    let rtrb_latency = bench_latency_oneway_rtrb();

    print_latency_results("nexus_spsc", &nexus_latency);
    print_latency_results("rtrb", &rtrb_latency);
}
