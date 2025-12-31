//! Isolated benchmark for nexus_raw SPSC - for perf profiling
//!
//! Run: cargo build --release --bench perf_raw
//! Profile: sudo perf stat -e cycles,instructions,cache-misses,L1-dcache-load-misses ./target/release/deps/perf_raw-*

use std::thread;

const COUNT: u64 = 1_000_000_000;
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

    let (mut producer, mut consumer) = raw::ring_buffer::<Message>(CAPACITY);

    let producer_handle = thread::spawn(move || {
        for i in 0..COUNT {
            while producer.push(Message::new(i)).is_err() {
                std::hint::spin_loop();
            }
        }
    });

    let consumer_handle = thread::spawn(move || {
        let mut received = 0u64;
        let mut sum = 0u64;
        while received < COUNT {
            if let Some(msg) = consumer.pop() {
                sum = sum.wrapping_add(msg.sequence);
                received += 1;
            } else {
                std::hint::spin_loop();
            }
        }
        (received, sum)
    });

    producer_handle.join().unwrap();
    let (received, sum) = consumer_handle.join().unwrap();
    assert_eq!(received, COUNT);
    assert_eq!(sum, EXPECTED_SUM);

    println!(
        "nexus_raw: {} iterations complete (256-byte messages)",
        COUNT
    );
}
