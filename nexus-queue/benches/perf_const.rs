//! Isolated benchmark for const-generic bounded SPSC

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

const COUNT: u64 = 10_000_000;

fn main() {
    use nexus_queue::spsc::const_q::RingBuffer;

    for _ in 0..3 {
        // Must be power of 2
        let (mut producer, mut consumer) = RingBuffer::<u64, 1024>::new();

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

    println!("bounded (const generic): {} iterations complete", COUNT * 3);
}
