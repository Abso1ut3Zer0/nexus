//! Isolated benchmark for nexus_minimal SPSC - for perf profiling
//!
//! Run: cargo build --release --bench perf_minimal
//! Profile: sudo perf stat -e cycles,instructions,cache-misses,L1-dcache-load-misses ./target/release/deps/perf_minimal-*

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

const COUNT: u64 = 10_000_000;
const CAPACITY: usize = 1024;

fn main() {
    use nexus_queue::spsc::minimal;

    // Run 3 iterations
    for _ in 0..3 {
        let (mut producer, mut consumer) = minimal::ring_buffer::<u64>(CAPACITY);
        let done = Arc::new(AtomicBool::new(false));
        let done_clone = done.clone();

        let producer_handle = thread::spawn(move || {
            for i in 0..COUNT {
                while producer.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
            done_clone.store(true, Ordering::Release);
        });

        let consumer_handle = thread::spawn(move || {
            let mut received = 0u64;
            loop {
                if consumer.pop().is_some() {
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

        producer_handle.join().unwrap();
        let received = consumer_handle.join().unwrap();
        assert_eq!(received, COUNT);
    }

    println!("nexus_minimal: {} iterations complete", COUNT * 3);
}
