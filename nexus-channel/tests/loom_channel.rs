#![cfg(loom)]

use loom::sync::Arc;
use loom::sync::atomic::{AtomicBool, AtomicUsize, Ordering, fence};
use loom::thread;

// Models the park/notify Dekker invariant without the actual parker
// (crossbeam's Parker is not loom-instrumented).
//
// The invariant: after both sides issue fence(SeqCst), it is impossible
// for the parker to miss a ready item AND the notifier to miss the parked
// flag simultaneously. Loom exhaustively checks all interleavings.
#[test]
fn park_notify_fence_no_missed_wakeup() {
    loom::model(|| {
        let parked = Arc::new(AtomicBool::new(false));
        let item_ready = Arc::new(AtomicUsize::new(0));

        let parked2 = parked.clone();
        let item_ready2 = item_ready.clone();

        let notifier = thread::spawn(move || {
            item_ready2.store(1, Ordering::Release);
            fence(Ordering::SeqCst);
            parked2.load(Ordering::SeqCst)
        });

        let parker = thread::spawn(move || {
            parked.store(true, Ordering::SeqCst);
            fence(Ordering::SeqCst);
            item_ready.load(Ordering::Relaxed) != 0
        });

        let notifier_saw_parked = notifier.join().unwrap();
        let parker_saw_item = parker.join().unwrap();

        assert!(
            notifier_saw_parked || parker_saw_item,
            "missed wakeup: neither side observed the other"
        );
    });
}
