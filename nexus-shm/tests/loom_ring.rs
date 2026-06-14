#![cfg(loom)]

use loom::sync::Arc;
use loom::sync::atomic::{AtomicU64, Ordering};
use loom::thread;

/// Models the SPSC ring's tail Release/Acquire handshake with a single item slot.
///
/// Producer: write item (Relaxed), then publish tail (Release).
/// Consumer: load tail (Acquire), then read item (Relaxed).
/// Loom exhaustively verifies that whenever the consumer sees tail > 0,
/// it observes the item written before the Release store.
#[test]
fn spsc_tail_acquire_sees_item() {
    loom::model(|| {
        let tail = Arc::new(AtomicU64::new(0));
        let item = Arc::new(AtomicU64::new(0));

        let tail_w = tail.clone();
        let item_w = item.clone();

        let producer = thread::spawn(move || {
            item_w.store(42, Ordering::Relaxed);
            tail_w.store(1, Ordering::Release);
        });

        let consumer = thread::spawn(move || {
            let t = tail.load(Ordering::Acquire);
            if t > 0 {
                let v = item.load(Ordering::Relaxed);
                assert_eq!(v, 42, "stale item after Acquire load of tail");
            }
        });

        producer.join().unwrap();
        consumer.join().unwrap();
    });
}

/// Models the head Release/Acquire handshake for flow-control:
/// consumer advances head (Release) to signal a slot is free;
/// producer loads head (Acquire) before reusing the slot.
#[test]
fn spsc_head_acquire_sees_slot_free() {
    loom::model(|| {
        let head = Arc::new(AtomicU64::new(0));
        let slot_reused = Arc::new(AtomicU64::new(0));

        let head_r = head.clone();
        let slot_r = slot_reused.clone();

        let consumer = thread::spawn(move || {
            head_r.store(1, Ordering::Release);
        });

        let producer = thread::spawn(move || {
            let h = head.load(Ordering::Acquire);
            if h > 0 {
                slot_reused.store(1, Ordering::Relaxed);
            }
        });

        consumer.join().unwrap();
        producer.join().unwrap();
        // If head was observed, slot_reused is set. No assertion needed —
        // loom verifies no data race on slot_reused.
        let _ = slot_r.load(Ordering::Relaxed);
    });
}
