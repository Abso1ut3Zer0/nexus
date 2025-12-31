//! Isolated benchmark for nexus_raw SPSC - for perf profiling
//!
//! Run: cargo build --release --bench perf_raw
//! Profile: sudo perf stat -e cycles,instructions,cache-misses,L1-dcache-load-misses ./target/release/deps/perf_raw-*

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

const COUNT: u64 = 10_000_000;
const CAPACITY: usize = 1024;
// Expected sum: 0 + 1 + 2 + ... + (COUNT-1) = COUNT * (COUNT-1) / 2
const EXPECTED_SUM: u64 = COUNT * (COUNT - 1) / 2;

/// 256-byte message for realistic trading system simulation
#[derive(Clone, Copy)]
#[repr(C, align(64))]
struct Message {
    sequence: u64,
    _payload: [u8; 248],
}

impl Message {
    fn new(sequence: u64) -> Self {
        Self {
            sequence,
            _payload: [0u8; 248],
        }
    }
}

fn main() {
    use nexus_queue::spsc::raw;

    // Warmup
    for _ in 0..3 {
        let (mut producer, mut consumer) = raw::ring_buffer::<Message>(CAPACITY);
        let done = Arc::new(AtomicBool::new(false));
        let done_clone = done.clone();

        let producer_handle = thread::spawn(move || {
            for i in 0..COUNT {
                while producer.push(Message::new(i)).is_err() {
                    std::hint::spin_loop();
                }
            }
            done_clone.store(true, Ordering::Release);
        });

        let consumer_handle = thread::spawn(move || {
            let mut received = 0u64;
            let mut sum = 0u64;
            loop {
                if let Some(msg) = consumer.pop() {
                    sum = sum.wrapping_add(msg.sequence);
                    received += 1;
                    if received == COUNT {
                        break;
                    }
                } else if done.load(Ordering::Acquire) {
                    while let Some(msg) = consumer.pop() {
                        sum = sum.wrapping_add(msg.sequence);
                        received += 1;
                    }
                    break;
                }
            }
            (received, sum)
        });

        producer_handle.join().unwrap();
        let (received, sum) = consumer_handle.join().unwrap();
        assert_eq!(received, COUNT);
        assert_eq!(sum, EXPECTED_SUM);
    }

    println!("nexus_raw: {} iterations complete (256-byte messages)", COUNT);
}
