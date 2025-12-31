//! Profiling benchmark to identify performance differences.
//!
//! Run with:
//!   cargo bench --bench profile_spsc
//!
//! Or for perf analysis:
//!   cargo build --release --bench profile_spsc
//!   perf stat -e cycles,instructions,cache-misses,branch-misses \
//!       ./target/release/deps/profile_spsc-*

use std::hint::black_box;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
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
    timestamp: u64,
    sequence: u64,
    _payload: [u8; 240], // Pad to 256 bytes total
}

impl Message {
    #[inline]
    fn new(seq: u64) -> Self {
        Self {
            timestamp: 0,
            sequence: seq,
            _payload: [0u8; 240],
        }
    }

    #[inline]
    fn with_timestamp(ts: u64) -> Self {
        Self {
            timestamp: ts,
            sequence: 0,
            _payload: [0u8; 240],
        }
    }
}

// Verify size at compile time
const _: () = assert!(std::mem::size_of::<Message>() == 256);

fn bench_nexus_raw() -> Duration {
    use nexus_queue::spsc::raw;

    let (mut producer, mut consumer) = raw::ring_buffer::<Message>(CAPACITY);
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

fn bench_nexus_raw_fenced() -> Duration {
    use nexus_queue::spsc::raw_fenced;

    let (mut producer, mut consumer) = raw_fenced::ring_buffer::<Message>(CAPACITY);
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

fn bench_nexus_raw_pointer() -> Duration {
    use nexus_queue::spsc::raw_pointer;

    let (mut producer, mut consumer) = raw_pointer::ring_buffer::<Message>(CAPACITY);
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
fn bench_push_only_nexus_raw() -> Duration {
    use nexus_queue::spsc::raw;

    let (mut producer, mut consumer) = raw::ring_buffer::<Message>(CAPACITY);

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

fn bench_push_only_nexus_raw_fenced() -> Duration {
    use nexus_queue::spsc::raw_fenced;

    let (mut producer, mut consumer) = raw_fenced::ring_buffer::<Message>(CAPACITY);

    for i in 0..(CAPACITY / 2) as u64 {
        producer.push(Message::new(i)).unwrap();
    }

    let start = Instant::now();
    for i in 0..COUNT {
        producer.push(black_box(Message::new(i))).unwrap();
        black_box(consumer.pop());
    }
    start.elapsed()
}

fn bench_push_only_nexus_raw_pointer() -> Duration {
    use nexus_queue::spsc::raw_pointer;

    let (mut producer, mut consumer) = raw_pointer::ring_buffer::<Message>(CAPACITY);

    for i in 0..(CAPACITY / 2) as u64 {
        producer.push(Message::new(i)).unwrap();
    }

    let start = Instant::now();
    for i in 0..COUNT {
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
    samples: Vec<u64>, // in nanoseconds
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

    #[allow(unused)]
    fn mean(&self) -> f64 {
        self.samples.iter().sum::<u64>() as f64 / self.samples.len() as f64
    }

    fn percentile(&self, p: f64) -> u64 {
        let idx = ((p / 100.0) * self.samples.len() as f64) as usize;
        self.samples[idx.min(self.samples.len() - 1)]
    }
}

/// Measure round-trip latency: producer sends timestamp, consumer measures delta
fn bench_latency_nexus_raw() -> LatencyStats {
    use nexus_queue::spsc::raw;

    let (mut producer, mut consumer) = raw::ring_buffer::<Message>(64); // Small buffer for latency test
    let samples = Arc::new(std::sync::Mutex::new(Vec::with_capacity(LATENCY_SAMPLES)));
    let samples_clone = samples.clone();
    let ready = Arc::new(AtomicBool::new(false));
    let ready_clone = ready.clone();

    let consumer_handle = thread::spawn(move || {
        let mut local_samples = Vec::with_capacity(LATENCY_SAMPLES);

        // Signal ready
        ready_clone.store(true, Ordering::Release);

        let mut count = 0usize;
        while count < LATENCY_WARMUP + LATENCY_SAMPLES {
            if let Some(msg) = consumer.pop() {
                let recv_time = precise_time_ns();
                if count >= LATENCY_WARMUP {
                    local_samples.push(recv_time.saturating_sub(msg.timestamp));
                }
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        *samples_clone.lock().unwrap() = local_samples;
    });

    // Wait for consumer to be ready
    while !ready.load(Ordering::Acquire) {
        std::hint::spin_loop();
    }

    // Producer: send timestamps
    for _ in 0..(LATENCY_WARMUP + LATENCY_SAMPLES) {
        let msg = Message::with_timestamp(precise_time_ns());
        while producer.push(msg).is_err() {
            std::hint::spin_loop();
        }
        // Small delay to avoid overwhelming - measure realistic latency
        std::thread::yield_now();
    }

    consumer_handle.join().unwrap();
    let samples = std::mem::take(&mut *samples.lock().unwrap());
    LatencyStats::new(samples)
}

fn bench_latency_nexus_raw_fenced() -> LatencyStats {
    use nexus_queue::spsc::raw_fenced;

    let (mut producer, mut consumer) = raw_fenced::ring_buffer::<Message>(64);
    let samples = Arc::new(std::sync::Mutex::new(Vec::with_capacity(LATENCY_SAMPLES)));
    let samples_clone = samples.clone();
    let ready = Arc::new(AtomicBool::new(false));
    let ready_clone = ready.clone();

    let consumer_handle = thread::spawn(move || {
        let mut local_samples = Vec::with_capacity(LATENCY_SAMPLES);
        ready_clone.store(true, Ordering::Release);

        let mut count = 0usize;
        while count < LATENCY_WARMUP + LATENCY_SAMPLES {
            if let Some(msg) = consumer.pop() {
                let recv_time = precise_time_ns();
                if count >= LATENCY_WARMUP {
                    local_samples.push(recv_time.saturating_sub(msg.timestamp));
                }
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        *samples_clone.lock().unwrap() = local_samples;
    });

    while !ready.load(Ordering::Acquire) {
        std::hint::spin_loop();
    }

    for _ in 0..(LATENCY_WARMUP + LATENCY_SAMPLES) {
        let msg = Message::with_timestamp(precise_time_ns());
        while producer.push(msg).is_err() {
            std::hint::spin_loop();
        }
        std::thread::yield_now();
    }

    consumer_handle.join().unwrap();
    let samples = std::mem::take(&mut *samples.lock().unwrap());
    LatencyStats::new(samples)
}

fn bench_latency_nexus_raw_pointer() -> LatencyStats {
    use nexus_queue::spsc::raw_pointer;

    let (mut producer, mut consumer) = raw_pointer::ring_buffer::<Message>(64);
    let samples = Arc::new(std::sync::Mutex::new(Vec::with_capacity(LATENCY_SAMPLES)));
    let samples_clone = samples.clone();
    let ready = Arc::new(AtomicBool::new(false));
    let ready_clone = ready.clone();

    let consumer_handle = thread::spawn(move || {
        let mut local_samples = Vec::with_capacity(LATENCY_SAMPLES);
        ready_clone.store(true, Ordering::Release);

        let mut count = 0usize;
        while count < LATENCY_WARMUP + LATENCY_SAMPLES {
            if let Some(msg) = consumer.pop() {
                let recv_time = precise_time_ns();
                if count >= LATENCY_WARMUP {
                    local_samples.push(recv_time.saturating_sub(msg.timestamp));
                }
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        *samples_clone.lock().unwrap() = local_samples;
    });

    while !ready.load(Ordering::Acquire) {
        std::hint::spin_loop();
    }

    for _ in 0..(LATENCY_WARMUP + LATENCY_SAMPLES) {
        let msg = Message::with_timestamp(precise_time_ns());
        while producer.push(msg).is_err() {
            std::hint::spin_loop();
        }
        std::thread::yield_now();
    }

    consumer_handle.join().unwrap();
    let samples = std::mem::take(&mut *samples.lock().unwrap());
    LatencyStats::new(samples)
}

fn bench_latency_rtrb() -> LatencyStats {
    use rtrb::RingBuffer;

    let (mut producer, mut consumer) = RingBuffer::<Message>::new(64);
    let samples = Arc::new(std::sync::Mutex::new(Vec::with_capacity(LATENCY_SAMPLES)));
    let samples_clone = samples.clone();
    let ready = Arc::new(AtomicBool::new(false));
    let ready_clone = ready.clone();

    let consumer_handle = thread::spawn(move || {
        let mut local_samples = Vec::with_capacity(LATENCY_SAMPLES);
        ready_clone.store(true, Ordering::Release);

        let mut count = 0usize;
        while count < LATENCY_WARMUP + LATENCY_SAMPLES {
            if let Ok(msg) = consumer.pop() {
                let recv_time = precise_time_ns();
                if count >= LATENCY_WARMUP {
                    local_samples.push(recv_time.saturating_sub(msg.timestamp));
                }
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        *samples_clone.lock().unwrap() = local_samples;
    });

    while !ready.load(Ordering::Acquire) {
        std::hint::spin_loop();
    }

    for _ in 0..(LATENCY_WARMUP + LATENCY_SAMPLES) {
        let msg = Message::with_timestamp(precise_time_ns());
        while producer.push(msg).is_err() {
            std::hint::spin_loop();
        }
        std::thread::yield_now();
    }

    consumer_handle.join().unwrap();
    let samples = std::mem::take(&mut *samples.lock().unwrap());
    LatencyStats::new(samples)
}

/// High-precision timestamp in nanoseconds
#[inline]
fn precise_time_ns() -> u64 {
    #[cfg(target_arch = "x86_64")]
    {
        // Use RDTSC for highest precision on x86_64
        // Note: This is cycles, not ns, but consistent for comparison
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

    println!("=== Struct sizes ===");
    println!(
        "nexus raw Producer:         {} bytes",
        std::mem::size_of::<nexus_queue::spsc::raw::Producer<Message>>()
    );
    println!(
        "nexus raw Consumer:         {} bytes",
        std::mem::size_of::<nexus_queue::spsc::raw::Consumer<Message>>()
    );
    println!(
        "nexus raw_pointer Producer: {} bytes",
        std::mem::size_of::<nexus_queue::spsc::raw_pointer::Producer<Message>>()
    );
    println!(
        "nexus raw_pointer Consumer: {} bytes",
        std::mem::size_of::<nexus_queue::spsc::raw_pointer::Consumer<Message>>()
    );
    println!("rtrb Producer:              ~24 bytes (from source)");
    println!("rtrb Consumer:              ~24 bytes (from source)");

    println!("\n=== Single-threaded push+pop (no contention) ===");
    println!("Each iteration: {} ops\n", COUNT);

    // Warmup
    let _ = bench_push_only_nexus_raw();
    let _ = bench_push_only_nexus_raw_pointer();
    let _ = bench_push_only_rtrb();

    let mut raw_times = Vec::with_capacity(ITERATIONS);
    let mut raw_pointer_times = Vec::with_capacity(ITERATIONS);
    let mut rtrb_times = Vec::with_capacity(ITERATIONS);

    // Interleave to avoid ordering effects
    for _ in 0..ITERATIONS {
        raw_times.push(bench_push_only_nexus_raw());
        raw_pointer_times.push(bench_push_only_nexus_raw_pointer());
        rtrb_times.push(bench_push_only_rtrb());
    }

    print_results("nexus_raw", &raw_times);
    print_results("nexus_raw_pointer", &raw_pointer_times);
    print_results("rtrb", &rtrb_times);

    println!("\n=== Cross-thread throughput ===");
    println!("Each iteration: {} ops\n", COUNT);

    // Warmup
    let _ = bench_nexus_raw();
    let _ = bench_nexus_raw_pointer();
    let _ = bench_rtrb();

    let mut raw_times = Vec::with_capacity(ITERATIONS);
    let mut raw_pointer_times = Vec::with_capacity(ITERATIONS);
    let mut rtrb_times = Vec::with_capacity(ITERATIONS);

    for _ in 0..ITERATIONS {
        raw_times.push(bench_nexus_raw());
        raw_pointer_times.push(bench_nexus_raw_pointer());
        rtrb_times.push(bench_rtrb());
    }

    print_results("nexus_raw", &raw_times);
    print_results("nexus_raw_pointer", &raw_pointer_times);
    print_results("rtrb", &rtrb_times);

    println!("\n=== Cross-thread latency ===");
    println!("Samples: {}, Warmup: {}\n", LATENCY_SAMPLES, LATENCY_WARMUP);

    // Warmup
    let _ = bench_latency_nexus_raw();
    let _ = bench_latency_nexus_raw_pointer();
    let _ = bench_latency_rtrb();

    // Run latency benchmarks
    let raw_latency = bench_latency_nexus_raw();
    let raw_pointer_latency = bench_latency_nexus_raw_pointer();
    let rtrb_latency = bench_latency_rtrb();

    print_latency_results("nexus_raw", &raw_latency);
    print_latency_results("nexus_raw_pointer", &raw_pointer_latency);
    print_latency_results("rtrb", &rtrb_latency);
}
