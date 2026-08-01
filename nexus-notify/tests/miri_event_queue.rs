//! Miri tests for nexus-notify's event_queue (intrusive MPSC + per-token
//! atomic dedup).
//!
//! Run: `MIRIFLAGS="-Zmiri-ignore-leaks" cargo +nightly miri test -p nexus-notify --test miri_event_queue`
//!
//! Focuses on the swap/push/pop/poll cycle and cross-thread atomic
//! ordering. The per-token `swap(true, Acquire)` paired with the
//! poller's `store(false, Release)` is the load-bearing synchronization
//! and is exactly the kind of code where miri can surface a missed
//! ordering or a torn pointer publish.
//!
//! Test counts kept small (2–4 producer threads, a few hundred ops at
//! most) because miri is ~10–100× slower than native.

use std::thread;

use nexus_notify::{Events, Token, event_queue};

// =============================================================================
// 2.1 — Single notifier → single poll cycle
// =============================================================================

#[test]
fn single_notify_single_poll() {
    let (notifier, poller) = event_queue(8);
    let mut events = Events::with_capacity(8);

    notifier.notify(Token::new(3)).unwrap();
    poller.poll(&mut events);

    assert_eq!(events.len(), 1);
    assert_eq!(events.iter().next().unwrap().index(), 3);
}

// =============================================================================
// 2.2 — Dedup invariant: notify twice without polling, see one event
// =============================================================================

#[test]
fn notify_twice_yields_one_event() {
    let (notifier, poller) = event_queue(8);
    let mut events = Events::with_capacity(8);
    let t = Token::new(2);

    notifier.notify(t).unwrap();
    notifier.notify(t).unwrap();
    poller.poll(&mut events);

    assert_eq!(events.len(), 1);
    assert_eq!(events.iter().next().unwrap().index(), 2);
}

// =============================================================================
// 2.3 — Multiple tokens, mixed-order notifies → FIFO by notify order
// =============================================================================

#[test]
fn fifo_by_notify_order() {
    let (notifier, poller) = event_queue(8);
    let mut events = Events::with_capacity(8);

    notifier.notify(Token::new(2)).unwrap();
    notifier.notify(Token::new(0)).unwrap();
    notifier.notify(Token::new(5)).unwrap();
    poller.poll(&mut events);

    let order: Vec<usize> = events.iter().map(Token::index).collect();
    assert_eq!(order, vec![2, 0, 5]);
}

// =============================================================================
// 2.4 — Notify after drain: flag must reset cleanly
// =============================================================================

#[test]
fn notify_after_drain_works() {
    let (notifier, poller) = event_queue(4);
    let mut events = Events::with_capacity(4);
    let t = Token::new(1);

    notifier.notify(t).unwrap();
    poller.poll(&mut events);
    assert_eq!(events.len(), 1);
    events.drain().for_each(drop);

    // Second cycle — flag was cleared on poll, must accept new notify.
    notifier.notify(t).unwrap();
    poller.poll(&mut events);
    assert_eq!(events.len(), 1);
    assert_eq!(events.iter().next().unwrap().index(), 1);
}

// =============================================================================
// 2.5 — Capacity boundary: fill queue to capacity, drain, refill
// =============================================================================
//
// The per-token dedup flag prevents the queue from ever holding more
// than `capacity` entries at once. Verify we can saturate at capacity
// and drain cleanly.

#[test]
fn fill_to_capacity_then_drain() {
    const CAP: usize = 4;
    let (notifier, poller) = event_queue(CAP);
    let mut events = Events::with_capacity(CAP);

    for i in 0..CAP {
        notifier.notify(Token::new(i)).unwrap();
    }
    poller.poll(&mut events);
    assert_eq!(events.len(), CAP);

    let order: Vec<usize> = events.drain().map(Token::index).collect();
    assert_eq!(order, (0..CAP).collect::<Vec<_>>());

    // Refill — flags were cleared, must work again.
    for i in (0..CAP).rev() {
        notifier.notify(Token::new(i)).unwrap();
    }
    poller.poll(&mut events);
    assert_eq!(events.len(), CAP);
    let order: Vec<usize> = events.iter().map(Token::index).collect();
    assert_eq!(order, (0..CAP).rev().collect::<Vec<_>>());
}

// =============================================================================
// 2.6 — Cross-thread Notifier clone: producer thread, consumer thread
// =============================================================================
//
// The producer threads each own a cloned `Notifier`; the poller stays on
// the main thread. Miri's data-race detector validates the
// `swap(true, Acquire)` / `store(false, Release)` pairing. We use small N
// to keep miri's runtime sane.

#[test]
fn cross_thread_notifier_clone() {
    const N: usize = 4;
    let (notifier, poller) = event_queue(N);
    let mut events = Events::with_capacity(N);

    let n2 = notifier.clone();
    let producer = thread::spawn(move || {
        // Each notify is a swap on the per-token flag + a queue push if
        // newly ready.
        for i in 0..N {
            n2.notify(Token::new(i)).unwrap();
        }
    });

    producer.join().unwrap();
    drop(notifier); // drop the original after producer finishes; queue is closed

    poller.poll(&mut events);
    assert_eq!(events.len(), N);

    // Notifies arrived in 0..N order; FIFO contract preserved.
    let order: Vec<usize> = events.iter().map(Token::index).collect();
    assert_eq!(order, (0..N).collect::<Vec<_>>());
}

// =============================================================================
// 2.7 — Multiple producer threads, single consumer
// =============================================================================
//
// Real MPSC stress under miri: 2 producer threads each notify a
// disjoint half of the token space. The poller drains both. Miri's
// scheduler interleaves the threads and validates atomic ordering on
// every interleaving it explores.

#[test]
fn two_producers_one_consumer() {
    const HALF: usize = 4;
    const TOTAL: usize = HALF * 2;
    let (notifier, poller) = event_queue(TOTAL);
    let mut events = Events::with_capacity(TOTAL);

    let n1 = notifier.clone();
    let n2 = notifier.clone();

    let p1 = thread::spawn(move || {
        for i in 0..HALF {
            n1.notify(Token::new(i)).unwrap();
        }
    });
    let p2 = thread::spawn(move || {
        for i in HALF..TOTAL {
            n2.notify(Token::new(i)).unwrap();
        }
    });

    p1.join().unwrap();
    p2.join().unwrap();
    drop(notifier);

    poller.poll(&mut events);
    assert_eq!(events.len(), TOTAL);

    // Order between the two producers is interleaved by the scheduler;
    // validate the *set* matches.
    let mut seen: Vec<usize> = events.iter().map(Token::index).collect();
    seen.sort_unstable();
    assert_eq!(seen, (0..TOTAL).collect::<Vec<_>>());
}

// =============================================================================
// 2.8 — Conflation under cross-thread spam
// =============================================================================
//
// One producer hammers a single token from a spawned thread while the
// main thread does NOT poll until the producer is done. Result: exactly
// one event for that token. Validates that the Acquire on swap is
// strong enough that concurrent notifies still conflate to one entry
// even when interleaved with — well — nothing else (single producer);
// what we're really checking is that the flag-set + queue-push pair is
// atomic enough at the protocol level. Miri's race detector covers the
// memory model side.

#[test]
fn cross_thread_conflation() {
    let (notifier, poller) = event_queue(2);
    let mut events = Events::with_capacity(2);
    let t = Token::new(1);

    let n2 = notifier.clone();
    let producer = thread::spawn(move || {
        for _ in 0..16 {
            n2.notify(t).unwrap();
        }
    });
    producer.join().unwrap();
    drop(notifier);

    poller.poll(&mut events);
    assert_eq!(events.len(), 1, "16 notifies must conflate to 1 event");
    assert_eq!(events.iter().next().unwrap().index(), 1);
}

// =============================================================================
// 2.9 — Racing notifies on the same token conflate to one polled event
// =============================================================================
//
// Two producer threads notify the same token concurrently. The per-token
// flag's `swap(true, Acquire)` pairing means exactly one wins the race
// and pushes to the queue; the other observes flag=true and skips. From
// outside the crate the swap winner isn't observable, but the
// consequence is: each round produces exactly one polled event, no
// matter how the threads interleave.

#[test]
fn racing_notifies_conflate_to_one_polled_event() {
    const ITERS: usize = 8;
    let (notifier, poller) = event_queue(1);
    let mut events = Events::with_capacity(1);
    let t = Token::new(0);

    for _ in 0..ITERS {
        let n_a = notifier.clone();
        let n_b = notifier.clone();

        let h_a = thread::spawn(move || n_a.notify(t).unwrap());
        let h_b = thread::spawn(move || n_b.notify(t).unwrap());

        h_a.join().unwrap();
        h_b.join().unwrap();

        // Both threads called notify(); the dedup contract collapses
        // them to a single queue entry.
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.iter().next().unwrap().index(), 0);
        events.drain().for_each(drop);
    }
}
