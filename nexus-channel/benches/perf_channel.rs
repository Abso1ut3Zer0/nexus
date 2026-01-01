//! Isolated benchmark for nexus-channel - for perf profiling
//!
//! Run: cargo build --release --bench perf_channel_raw
//! Profile: sudo perf stat -e cycles,instructions,cache-misses,L1-dcache-load-misses \
//!          taskset -c 0,2 ./target/release/deps/perf_channel_raw-*

use std::thread;

use nexus_channel::channel;

const COUNT: u64 = 10_000_000;
const CAPACITY: usize = 1024;
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
    let (mut tx, mut rx) = channel::<Message>(CAPACITY);

    let producer = thread::spawn(move || {
        for i in 0..COUNT {
            tx.send(Message::new(i)).unwrap();
        }
    });

    let consumer = thread::spawn(move || {
        let mut received = 0u64;
        let mut sum = 0u64;
        while received < COUNT {
            let msg = rx.recv().unwrap();
            sum = sum.wrapping_add(msg.sequence);
            received += 1;
        }
        (received, sum)
    });

    producer.join().unwrap();
    let (received, sum) = consumer.join().unwrap();

    assert_eq!(received, COUNT);
    assert_eq!(sum, EXPECTED_SUM);
}
