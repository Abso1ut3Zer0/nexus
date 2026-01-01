// benches/perf_slot.rs
//! Isolated benchmark for nexus_slot - for perf profiling
//!
//! Run: cargo build --release --bench perf_slot
//! Profile: sudo perf stat -e cycles,instructions,cache-misses,L1-dcache-load-misses ./target/release/deps/perf_slot-*

use std::thread;

use nexus_slot::{self, Pod};

const COUNT: u64 = 10_000_000;

/// 256-byte message for realistic trading system simulation
#[derive(Clone)]
#[repr(C, align(64))]
struct Quote {
    sequence: u64,
    bid_price: f64,
    ask_price: f64,
    bid_size: f64,
    ask_size: f64,
    _padding: [u8; 216],
}

unsafe impl Pod for Quote {}

impl Quote {
    fn new(sequence: u64) -> Self {
        Self {
            sequence,
            bid_price: 100.0,
            ask_price: 100.01,
            bid_size: 1000.0,
            ask_size: 1000.0,
            _padding: [0u8; 216],
        }
    }
}

fn main() {
    let (mut writer, mut reader) = nexus_slot::slot::<Quote>();

    let writer_handle = thread::spawn(move || {
        for i in 0..COUNT {
            writer.write(Quote::new(i));
        }
    });

    let reader_handle = thread::spawn(move || {
        let mut last_seq = 0u64;
        let mut reads = 0u64;

        loop {
            if let Some(quote) = reader.read() {
                assert!(quote.sequence >= last_seq, "sequence must be monotonic");
                last_seq = quote.sequence;
                reads += 1;

                if last_seq >= COUNT - 1 {
                    break;
                }
            } else {
                std::hint::spin_loop();
            }
        }
        (last_seq, reads)
    });

    writer_handle.join().unwrap();
    let (last_seq, reads) = reader_handle.join().unwrap();

    assert_eq!(last_seq, COUNT - 1);
    println!("Total writes: {}", COUNT);
    println!(
        "Total reads:  {} (conflation ratio: {:.1}x)",
        reads,
        COUNT as f64 / reads as f64
    );
}
