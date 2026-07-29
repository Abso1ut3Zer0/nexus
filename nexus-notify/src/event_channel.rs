use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use crossbeam_utils::Backoff;
use crossbeam_utils::sync::{Parker, Unparker};

use crate::event_queue::{self, Events, Notifier, NotifyError, Poller, Token};

const DEFAULT_SNOOZE_ITERS: usize = 8;

// ========================================================
// ChannelShared (parking coordination)
// ========================================================

struct ChannelShared {
    receiver_parked: AtomicBool,
}

// ========================================================
// Sender (producer)
// ========================================================

/// Producer handle for the blocking event channel.
///
/// Cloneable for MPSC. Same conflation semantics as [`Notifier`] —
/// duplicate notifications are suppressed. Automatically wakes a
/// parked [`Receiver`] on any successful notification (including
/// conflated — a spurious wakeup is safe and self-correcting).
///
/// Obtained from [`event_channel()`].
pub struct Sender {
    notifier: Notifier,
    unparker: Unparker,
    shared: Arc<ChannelShared>,
}

impl Clone for Sender {
    fn clone(&self) -> Self {
        Self {
            notifier: self.notifier.clone(),
            unparker: self.unparker.clone(),
            shared: Arc::clone(&self.shared),
        }
    }
}

impl Sender {
    /// Signal that a token is ready.
    ///
    /// Same semantics as [`Notifier::notify`] — conflated if already
    /// flagged. Additionally, wakes the receiver if it's parked.
    ///
    /// Every successful notify (including conflated) checks the parked
    /// flag. A conflated notify may cause a spurious wakeup (receiver
    /// wakes, polls, finds nothing new, re-parks). This is safe and
    /// self-correcting. Correctness beats cleverness.
    #[inline]
    pub fn notify(&self, token: Token) -> Result<(), NotifyError> {
        self.notifier.notify(token)?;
        if self.shared.receiver_parked.load(Ordering::SeqCst) {
            self.unparker.unpark();
        }
        Ok(())
    }
}

// ========================================================
// Receiver (consumer)
// ========================================================

/// Consumer handle for the blocking event channel.
///
/// Not cloneable — single consumer. Provides blocking [`recv`](Receiver::recv)
/// and [`recv_timeout`](Receiver::recv_timeout) in addition to non-blocking
/// [`try_recv`](Receiver::try_recv).
///
/// Blocking methods use a three-phase wait: fast poll → backoff (snooze)
/// → park. The receiver parks when idle and is woken by the sender on
/// new notifications.
///
/// Obtained from [`event_channel()`].
pub struct Receiver {
    poller: Poller,
    parker: Parker,
    shared: Arc<ChannelShared>,
    snooze_iters: usize,
}

impl Receiver {
    /// Block until events are ready, then drain all into the buffer.
    ///
    /// Three-phase wait: poll (fast path) → backoff (snooze) → park.
    /// Returns when at least one event is available.
    pub fn recv(&self, events: &mut Events) {
        self.recv_inner(events, usize::MAX);
    }

    /// Block until events are ready, then drain up to `limit`.
    ///
    /// Same three-phase wait. Returns when at least one event is
    /// available. Oldest notifications drain first (FIFO).
    pub fn recv_limit(&self, events: &mut Events, limit: usize) {
        self.recv_inner(events, limit);
    }

    /// Block until events are ready, with timeout.
    ///
    /// Returns `true` if events were received, `false` if the timeout
    /// elapsed with no events.
    pub fn recv_timeout(&self, events: &mut Events, timeout: Duration) -> bool {
        self.recv_timeout_inner(events, usize::MAX, timeout)
    }

    /// Block until events are ready, with timeout and limit.
    ///
    /// Returns `true` if events were received, `false` if the timeout
    /// elapsed with no events.
    pub fn recv_timeout_limit(&self, events: &mut Events, limit: usize, timeout: Duration) -> bool {
        self.recv_timeout_inner(events, limit, timeout)
    }

    /// Non-blocking poll. Same as [`Poller::poll`].
    #[inline]
    pub fn try_recv(&self, events: &mut Events) {
        self.poller.poll(events);
    }

    /// Non-blocking poll with limit. Same as [`Poller::poll_limit`].
    #[inline]
    pub fn try_recv_limit(&self, events: &mut Events, limit: usize) {
        self.poller.poll_limit(events, limit);
    }

    /// The maximum token index (exclusive).
    #[inline]
    pub fn capacity(&self) -> usize {
        self.poller.capacity()
    }

    // ========================================================
    // Internal: three-phase recv
    // ========================================================

    fn recv_inner(&self, events: &mut Events, limit: usize) {
        // Phase 1: fast path
        self.poller.poll_limit(events, limit);
        if !events.is_empty() {
            return;
        }

        // Phase 2: backoff (snooze)
        let backoff = Backoff::new();
        for _ in 0..self.snooze_iters {
            backoff.snooze();
            self.poller.poll_limit(events, limit);
            if !events.is_empty() {
                return;
            }
        }

        // Phase 3: park
        loop {
            // Set parked flag BEFORE re-checking the queue.
            // SeqCst synchronizes with the sender's SeqCst load.
            self.shared.receiver_parked.store(true, Ordering::SeqCst);

            // Re-check after setting flag — prevents lost wakeup.
            // If a producer pushed between our last poll and setting
            // the flag, we catch it here instead of sleeping forever.
            self.poller.poll_limit(events, limit);
            if !events.is_empty() {
                self.shared.receiver_parked.store(false, Ordering::Relaxed);
                return;
            }

            // Safe to park — flag is set, queue is empty.
            self.parker.park();
            self.shared.receiver_parked.store(false, Ordering::Relaxed);

            // Re-check after waking.
            self.poller.poll_limit(events, limit);
            if !events.is_empty() {
                return;
            }
            // Spurious wakeup or conflated notify — loop and re-park.
        }
    }

    fn recv_timeout_inner(&self, events: &mut Events, limit: usize, timeout: Duration) -> bool {
        let deadline = Instant::now() + timeout;

        // Phase 1: fast path
        self.poller.poll_limit(events, limit);
        if !events.is_empty() {
            return true;
        }

        // Phase 2: backoff (snooze)
        let backoff = Backoff::new();
        for _ in 0..self.snooze_iters {
            if Instant::now() >= deadline {
                return false;
            }
            backoff.snooze();
            self.poller.poll_limit(events, limit);
            if !events.is_empty() {
                return true;
            }
        }

        // Phase 3: park with timeout
        loop {
            let now = Instant::now();
            if now >= deadline {
                return false;
            }

            self.shared.receiver_parked.store(true, Ordering::SeqCst);

            // Re-check after setting flag.
            self.poller.poll_limit(events, limit);
            if !events.is_empty() {
                self.shared.receiver_parked.store(false, Ordering::Relaxed);
                return true;
            }

            let remaining = deadline - now;
            self.parker.park_timeout(remaining);
            self.shared.receiver_parked.store(false, Ordering::Relaxed);

            self.poller.poll_limit(events, limit);
            if !events.is_empty() {
                return true;
            }
        }
    }
}

// ========================================================
// Constructor
// ========================================================

/// Create a blocking event channel with capacity for `max_tokens`
/// unique tokens.
///
/// Returns a `(Sender, Receiver)` pair. The `Sender` is cloneable
/// for multiple producers. The `Receiver` is single-consumer.
///
/// The sender automatically wakes a parked receiver on new
/// notifications. Conflated notifications may cause spurious
/// wakeups (safe and self-correcting).
///
/// # Panics
///
/// Panics if `max_tokens` is 0.
///
/// # Examples
///
/// ```
/// use nexus_notify::{event_channel, Token, Events};
/// use std::thread;
///
/// let (sender, receiver) = event_channel(64);
/// let mut events = Events::with_capacity(64);
///
/// // Producer thread
/// let s = sender.clone();
/// let handle = thread::spawn(move || {
///     s.notify(Token::new(42)).unwrap();
/// });
///
/// // Consumer blocks until event arrives
/// receiver.recv(&mut events);
/// assert_eq!(events.len(), 1);
/// assert_eq!(events.as_slice()[0].index(), 42);
///
/// handle.join().unwrap();
/// ```
#[cold]
pub fn event_channel(max_tokens: usize) -> (Sender, Receiver) {
    let (notifier, poller) = event_queue::event_queue(max_tokens);
    let shared = Arc::new(ChannelShared {
        receiver_parked: AtomicBool::new(false),
    });
    let parker = Parker::new();
    let unparker = parker.unparker().clone();
    (
        Sender {
            notifier,
            unparker,
            shared: Arc::clone(&shared),
        },
        Receiver {
            poller,
            parker,
            shared,
            snooze_iters: DEFAULT_SNOOZE_ITERS,
        },
    )
}

// ========================================================
// Tests
// ========================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_recv_non_blocking() {
        let (sender, receiver) = event_channel(64);
        let mut events = Events::with_capacity(64);

        receiver.try_recv(&mut events);
        assert!(events.is_empty());

        sender.notify(Token::new(5)).unwrap();
        receiver.try_recv(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.iter().next().unwrap().index(), 5);
    }

    #[test]
    fn try_recv_limit() {
        let (sender, receiver) = event_channel(64);
        let mut events = Events::with_capacity(64);

        for i in 0..10 {
            sender.notify(Token::new(i)).unwrap();
        }

        receiver.try_recv_limit(&mut events, 3);
        assert_eq!(events.len(), 3);
        events.drain().for_each(drop);

        receiver.try_recv(&mut events);
        assert_eq!(events.len(), 7);
    }

    #[test]
    fn recv_returns_immediately_when_data_ready() {
        let (sender, receiver) = event_channel(64);
        let mut events = Events::with_capacity(64);

        sender.notify(Token::new(10)).unwrap();
        receiver.recv(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.iter().next().unwrap().index(), 10);
    }

    #[test]
    fn recv_blocks_and_wakes() {
        let (sender, receiver) = event_channel(64);

        let handle = std::thread::spawn(move || {
            let mut events = Events::with_capacity(64);
            receiver.recv(&mut events);
            events.iter().map(Token::index).collect::<Vec<_>>()
        });

        // Small delay to let receiver park
        std::thread::sleep(Duration::from_millis(50));
        sender.notify(Token::new(42)).unwrap();

        let indices = handle.join().unwrap();
        assert_eq!(indices, vec![42]);
    }

    #[test]
    fn recv_limit_blocks_and_wakes() {
        let (sender, receiver) = event_channel(64);

        let handle = std::thread::spawn(move || {
            let mut events = Events::with_capacity(64);
            receiver.recv_limit(&mut events, 2);
            events.iter().map(Token::index).collect::<Vec<_>>()
        });

        std::thread::sleep(Duration::from_millis(50));
        for i in 0..5 {
            sender.notify(Token::new(i)).unwrap();
        }

        let indices = handle.join().unwrap();
        // Should get at most 2 (limit)
        assert!(indices.len() <= 2);
        assert!(!indices.is_empty());
    }

    #[test]
    fn recv_timeout_returns_true_on_data() {
        let (sender, receiver) = event_channel(64);
        let mut events = Events::with_capacity(64);

        sender.notify(Token::new(7)).unwrap();
        let got_data = receiver.recv_timeout(&mut events, Duration::from_secs(1));
        assert!(got_data);
        assert_eq!(events.len(), 1);
    }

    #[test]
    fn recv_timeout_returns_false_on_timeout() {
        let (_, receiver) = event_channel(64);
        let mut events = Events::with_capacity(64);

        let got_data = receiver.recv_timeout(&mut events, Duration::from_millis(10));
        assert!(!got_data);
        assert!(events.is_empty());
    }

    #[test]
    fn recv_timeout_wakes_before_timeout() {
        let (sender, receiver) = event_channel(64);

        let handle = std::thread::spawn(move || {
            let mut events = Events::with_capacity(64);
            let got_data = receiver.recv_timeout(&mut events, Duration::from_secs(5));
            (
                got_data,
                events.iter().map(Token::index).collect::<Vec<_>>(),
            )
        });

        std::thread::sleep(Duration::from_millis(50));
        sender.notify(Token::new(42)).unwrap();

        let (got_data, indices) = handle.join().unwrap();
        assert!(got_data);
        assert_eq!(indices, vec![42]);
    }

    #[test]
    fn conflation() {
        let (sender, receiver) = event_channel(64);
        let mut events = Events::with_capacity(64);
        let t = Token::new(7);

        for _ in 0..100 {
            sender.notify(t).unwrap();
        }

        receiver.recv(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.iter().next().unwrap().index(), 7);
    }

    #[test]
    fn fifo_ordering() {
        let (sender, receiver) = event_channel(64);
        let mut events = Events::with_capacity(64);

        for i in 0..10 {
            sender.notify(Token::new(i)).unwrap();
        }

        receiver.recv(&mut events);
        let indices: Vec<usize> = events.iter().map(Token::index).collect();
        assert_eq!(indices, vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn multiple_recv_drains_incrementally() {
        let (sender, receiver) = event_channel(64);
        let mut events = Events::with_capacity(64);

        for i in 0..10 {
            sender.notify(Token::new(i)).unwrap();
        }

        receiver.recv_limit(&mut events, 3);
        assert_eq!(events.len(), 3);
        events.drain().for_each(drop);

        receiver.recv_limit(&mut events, 3);
        assert_eq!(events.len(), 3);
        events.drain().for_each(drop);

        receiver.try_recv(&mut events);
        assert_eq!(events.len(), 4);
    }

    #[test]
    fn capacity_1() {
        let (sender, receiver) = event_channel(1);
        let mut events = Events::with_capacity(1);

        sender.notify(Token::new(0)).unwrap();
        receiver.recv(&mut events);
        assert_eq!(events.len(), 1);
    }

    #[test]
    fn recv_timeout_zero_is_try_recv() {
        let (_, receiver) = event_channel(64);
        let mut events = Events::with_capacity(64);

        let got_data = receiver.recv_timeout(&mut events, Duration::ZERO);
        assert!(!got_data);
        assert!(events.is_empty());
    }
}
