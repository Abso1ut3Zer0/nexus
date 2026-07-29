use crate::loom_impl::{Flags, Ordering};

use nexus_queue::mpsc;

// ========================================================
// Token
// ========================================================

/// Opaque handle identifying a notification source.
///
/// Created by the user from their own key space (slab keys, array
/// indices). The event queue never assigns tokens — it treats the
/// index as an offset into its internal per-token state. Passing a
/// token whose index exceeds the queue's capacity will panic on use
/// (e.g., in [`Notifier::notify`]).
///
/// # Examples
///
/// ```
/// use nexus_notify::Token;
///
/// let token = Token::new(42);
/// assert_eq!(token.index(), 42);
///
/// let from_usize = Token::from(7usize);
/// assert_eq!(from_usize.index(), 7);
/// ```
///
/// # Type-tag intent
///
/// `Token` is a `usize` newtype with no invariants beyond what the
/// underlying integer provides. The newtype exists purely to prevent
/// accidentally passing some other identifier (slab key, array index,
/// raw `usize`) where a `Token` is expected. Don't reduce it to a type
/// alias and don't add invariants the rest of the crate doesn't enforce.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Token(usize);

impl Token {
    /// Create a token from a raw index.
    #[inline]
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    /// Returns the raw index for use in lookup tables.
    #[inline]
    pub const fn index(self) -> usize {
        self.0
    }
}

impl From<usize> for Token {
    #[inline]
    fn from(index: usize) -> Self {
        Self(index)
    }
}

// ========================================================
// Notifier (producer)
// ========================================================

/// Producer handle for signaling token readiness.
///
/// Cloneable for multiple producers (MPSC pattern). Each `notify()`
/// first checks the per-token dedup flag — if already set, the
/// notification is conflated (single atomic swap, no queue push).
/// Otherwise, the flag is set and the token index is pushed to the
/// FIFO queue.
///
/// Obtained from [`event_queue()`].
pub struct Notifier {
    flags: Flags,
    tx: mpsc::Producer<usize>,
}

impl Clone for Notifier {
    fn clone(&self) -> Self {
        Self {
            flags: self.flags.clone(),
            tx: self.tx.clone(),
        }
    }
}

// Notifier is !Sync: mpsc::Producer contains Cell fields (cached_head).
// Clone the Notifier to use from multiple threads — each gets its own Producer.

impl Notifier {
    /// Notify that a token is ready.
    ///
    /// If this token is already flagged (not yet consumed by the poller),
    /// this is a no-op — the notification is conflated. Returns `Ok(())`.
    ///
    /// Returns `Err(NotifyError)` if the internal queue push fails.
    /// This should never happen (the per-token flag prevents more entries
    /// than capacity), but if it does, the flag is cleared so future
    /// notifications to this token can retry.
    ///
    /// Wait-free on the conflation path (single atomic swap).
    /// Lock-free on the push path (CAS on queue tail).
    #[inline]
    pub fn notify(&self, token: Token) -> Result<(), NotifyError> {
        let idx = token.0;
        debug_assert!(
            idx < self.flags.len(),
            "token index {idx} exceeds capacity {}",
            self.flags.len()
        );

        // Dedup gate: Acquire synchronizes with the consumer's Release
        // on the flag clear, establishing happens-before: the consumer's
        // queue pop (which frees the slot) is visible to this producer
        // before the push. Without Acquire, the producer can see
        // flag=false but the queue slot still occupied (on weak memory
        // models the Release flag clear can propagate before the queue's
        // turn counter store). Release side is not needed — no downstream
        // consumer reads depend on writes before this swap.
        if self.flags.get(idx).swap(true, Ordering::Acquire) {
            return Ok(());
        }

        // Newly ready — push index to FIFO queue.
        self.tx.push(idx).map_err(|_| {
            // Invariant violated. Clear flag so future notifies can retry.
            self.flags.get(idx).store(false, Ordering::Relaxed);
            NotifyError { token }
        })
    }
}

// ========================================================
// Poller (consumer)
// ========================================================

/// Consumer handle for polling ready tokens.
///
/// Not cloneable — single consumer. Pops tokens from the FIFO queue
/// in notification arrival order.
///
/// Obtained from [`event_queue()`].
pub struct Poller {
    flags: Flags,
    rx: mpsc::Consumer<usize>,
}

impl Poller {
    /// The maximum token index this set supports (exclusive).
    #[inline]
    pub fn capacity(&self) -> usize {
        self.flags.len()
    }

    /// Drain all ready tokens into the events buffer.
    ///
    /// Pops from the MPSC queue until empty. Clears the per-token
    /// flag for each drained token (allowing future re-notification).
    ///
    /// The events buffer is cleared then filled. Tokens appear in
    /// notification arrival order (FIFO).
    #[inline]
    pub fn poll(&self, events: &mut Events) {
        self.poll_limit(events, usize::MAX);
    }

    /// Drain up to `limit` ready tokens into the events buffer.
    ///
    /// Pops from the MPSC queue up to `limit` times. Remaining
    /// items stay in the queue for the next poll/poll_limit call.
    ///
    /// Tokens appear in notification arrival order (FIFO).
    /// Prevents starvation: oldest notifications drain first.
    ///
    /// If `limit` is 0, the events buffer is cleared and no tokens
    /// are drained.
    ///
    /// # Panics
    ///
    /// In debug builds, panics if `events` still has undrained tokens
    /// from a previous poll — see [`Events::drain`].
    #[inline]
    pub fn poll_limit(&self, events: &mut Events, limit: usize) {
        debug_assert!(
            events.is_drained(),
            "poll_limit called with undrained tokens still in the buffer — \
             drain the previous batch before polling again"
        );
        events.clear();
        for _ in 0..limit {
            match self.rx.pop() {
                Some(idx) => {
                    // Release: ensures the queue pop's slot-free writes are
                    // ordered before this flag clear becomes visible to producers.
                    self.flags.get(idx).store(false, Ordering::Release);
                    events.tokens.push(Token(idx));
                }
                None => break,
            }
        }
    }
}

// ========================================================
// NotifyError
// ========================================================

/// Push failed — internal queue was unexpectedly full.
///
/// This indicates a logic bug (the per-token flag should prevent
/// more entries than capacity). The flag has been cleared so future
/// notifications to this token can retry.
#[derive(Debug)]
pub struct NotifyError {
    /// The token that failed to notify.
    pub token: Token,
}

impl std::fmt::Display for NotifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "notify failed for token {}: queue unexpectedly full",
            self.token.0
        )
    }
}

impl std::error::Error for NotifyError {}

// ========================================================
// Events
// ========================================================

/// Pre-allocated buffer of tokens returned by [`Poller::poll`].
///
/// Follows the mio `Events` pattern: allocate once at setup,
/// pass to `poll()` each iteration. The buffer is cleared and
/// refilled on each poll.
///
/// # Consuming tokens
///
/// [`drain`](Events::drain) removes tokens as they're taken; stopping
/// early (breaking the loop, dropping the iterator) leaves the rest in
/// the buffer instead of discarding them. This is a deliberate
/// divergence from mio's `Events`, which exposes only borrowing
/// accessors (`iter()`, `IntoIterator for &Events`): mio's readiness
/// notifications re-fire on the next poll, so a token a caller fails to
/// act on is self-correcting. These tokens are one-shot and deduped —
/// one that isn't consumed here is gone for good — so `poll`/`poll_limit`
/// refuse, in debug builds, to clear a buffer that still has undrained
/// tokens in it.
pub struct Events {
    tokens: Vec<Token>,
    /// Read cursor. Tokens before `head` have been taken via `drain()`;
    /// `clear()` resets it to 0. Keeping this on `Events` (rather than in
    /// `Drain`) means partial consumption is a pointer bump, not a
    /// `Vec::drain`-style memmove of the remainder.
    head: usize,
}

impl Events {
    /// Create a buffer that can hold up to `capacity` tokens
    /// per poll without reallocating.
    #[cold]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            tokens: Vec::with_capacity(capacity),
            head: 0,
        }
    }

    /// Number of undrained tokens from the last poll.
    #[inline]
    pub fn len(&self) -> usize {
        self.tokens.len() - self.head
    }

    /// Returns true if no undrained tokens remain.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head == self.tokens.len()
    }

    /// Clear the buffer.
    #[inline]
    pub fn clear(&mut self) {
        self.tokens.clear();
        self.head = 0;
    }

    /// Push a token into the buffer.
    #[inline]
    pub(crate) fn push(&mut self, token: Token) {
        self.tokens.push(token);
    }

    /// True if every token from the last poll has been drained.
    ///
    /// Used by `Poller::poll_limit`/`LocalNotify::poll_limit` to assert
    /// the caller finished with the previous batch before clearing and
    /// refilling.
    #[inline]
    pub(crate) fn is_drained(&self) -> bool {
        self.head == self.tokens.len()
    }

    /// View the undrained tokens as a slice.
    #[inline]
    pub fn as_slice(&self) -> &[Token] {
        &self.tokens[self.head..]
    }

    /// Iterate over the undrained tokens.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = Token> + '_ {
        self.tokens[self.head..].iter().copied()
    }

    /// Drain tokens by value, removing each as it's yielded.
    ///
    /// Unlike [`Vec::drain`], stopping early leaves the untaken
    /// remainder in the buffer rather than discarding it — the cursor
    /// only advances as far as `next()` was actually called.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_> {
        Drain { events: self }
    }
}

impl<'a> IntoIterator for &'a Events {
    type Item = Token;
    type IntoIter = std::iter::Copied<std::slice::Iter<'a, Token>>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.tokens[self.head..].iter().copied()
    }
}

/// Draining iterator over undrained [`Token`]s in an [`Events`] buffer.
///
/// Created by [`Events::drain`]. Advances the buffer's internal cursor
/// as tokens are yielded; stopping early (dropping this iterator before
/// it's exhausted) leaves everything past the cursor in place for the
/// next `drain()` call.
pub struct Drain<'a> {
    events: &'a mut Events,
}

impl Iterator for Drain<'_> {
    type Item = Token;

    #[inline]
    fn next(&mut self) -> Option<Token> {
        if self.events.head < self.events.tokens.len() {
            let token = self.events.tokens[self.events.head];
            self.events.head += 1;
            Some(token)
        } else {
            None
        }
    }
}

// ========================================================
// Constructor
// ========================================================

/// Create a notification channel with capacity for `max_tokens` unique tokens.
///
/// Returns a `(Notifier, Poller)` pair. The `Notifier` is cloneable
/// for multiple producers. The `Poller` is single-consumer.
///
/// The underlying MPSC queue is sized to `max_tokens` — since the
/// per-token dedup flag prevents duplicates, the queue can never overflow.
///
/// # Panics
///
/// Panics if `max_tokens` is 0.
///
/// # Examples
///
/// ```
/// use nexus_notify::{event_queue, Token};
///
/// let (notifier, poller) = event_queue(128);
/// let token = Token::new(42);
///
/// notifier.notify(token).unwrap();
/// ```
#[cold]
pub fn event_queue(max_tokens: usize) -> (Notifier, Poller) {
    assert!(max_tokens > 0, "event queue capacity must be non-zero");
    let flags = Flags::new(max_tokens);
    let (tx, rx) = mpsc::ring_buffer(max_tokens);
    (
        Notifier {
            flags: flags.clone(),
            tx,
        },
        Poller { flags, rx },
    )
}

// ========================================================
// Tests
// ========================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_round_trip() {
        let t = Token::new(42);
        assert_eq!(t.index(), 42);
    }

    #[test]
    fn token_from_usize() {
        let t = Token::from(7usize);
        assert_eq!(t.index(), 7);
    }

    #[test]
    fn notify_and_poll_single() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        notifier.notify(Token::new(5)).unwrap();
        poller.poll(&mut events);

        assert_eq!(events.len(), 1);
        assert_eq!(events.iter().next().unwrap().index(), 5);
    }

    #[test]
    fn notify_and_poll_multiple_fifo() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        notifier.notify(Token::new(0)).unwrap();
        notifier.notify(Token::new(3)).unwrap();
        notifier.notify(Token::new(63)).unwrap();

        poller.poll(&mut events);
        assert_eq!(events.len(), 3);

        let indices: Vec<usize> = events.iter().map(Token::index).collect();
        assert_eq!(indices, vec![0, 3, 63]);
    }

    #[test]
    fn poll_empty() {
        let (_, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        poller.poll(&mut events);
        assert!(events.is_empty());
    }

    #[test]
    fn poll_clears_flags() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        notifier.notify(Token::new(10)).unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        events.drain().for_each(drop);

        poller.poll(&mut events);
        assert!(events.is_empty());
    }

    #[test]
    fn conflation() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);
        let t = Token::new(7);

        for _ in 0..100 {
            notifier.notify(t).unwrap();
        }

        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.iter().next().unwrap().index(), 7);
    }

    #[test]
    fn flag_cleared_after_poll() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);
        let t = Token::new(5);

        notifier.notify(t).unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        events.drain().for_each(drop);

        notifier.notify(t).unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.iter().next().unwrap().index(), 5);
    }

    #[test]
    fn token_stability_across_polls() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);
        let t = Token::new(5);

        for _ in 0..10 {
            notifier.notify(t).unwrap();
            poller.poll(&mut events);
            assert_eq!(events.len(), 1);
            assert_eq!(events.drain().next().unwrap().index(), 5);
        }
    }

    #[test]
    fn events_buffer_reuse() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        notifier.notify(Token::new(0)).unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        events.drain().for_each(drop);

        notifier.notify(Token::new(1)).unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.iter().next().unwrap().index(), 1);
    }

    #[test]
    fn events_as_slice() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        notifier.notify(Token::new(10)).unwrap();
        notifier.notify(Token::new(20)).unwrap();
        poller.poll(&mut events);

        let slice = events.as_slice();
        assert_eq!(slice.len(), 2);
        assert_eq!(slice[0].index(), 10);
        assert_eq!(slice[1].index(), 20);
    }

    #[test]
    fn capacity_1() {
        let (notifier, poller) = event_queue(1);
        let mut events = Events::with_capacity(1);

        notifier.notify(Token::new(0)).unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "token index 64 exceeds capacity 64")]
    fn notify_out_of_bounds_panics() {
        let (notifier, _) = event_queue(64);
        let _ = notifier.notify(Token::new(64));
    }

    #[test]
    #[should_panic(expected = "capacity must be non-zero")]
    fn zero_capacity_panics() {
        event_queue(0);
    }

    // ====================================================
    // poll_limit tests
    // ====================================================

    #[test]
    fn poll_limit_drains_exactly_limit() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        for i in 0..10 {
            notifier.notify(Token::new(i)).unwrap();
        }

        poller.poll_limit(&mut events, 3);
        assert_eq!(events.len(), 3);
        events.drain().for_each(drop);

        poller.poll(&mut events);
        assert_eq!(events.len(), 7);
    }

    #[test]
    fn poll_limit_larger_than_ready() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        for i in 0..5 {
            notifier.notify(Token::new(i)).unwrap();
        }

        poller.poll_limit(&mut events, 100);
        assert_eq!(events.len(), 5);
        events.drain().for_each(drop);

        poller.poll(&mut events);
        assert!(events.is_empty());
    }

    #[test]
    fn poll_limit_zero_is_noop() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        notifier.notify(Token::new(0)).unwrap();

        poller.poll_limit(&mut events, 0);
        assert!(events.is_empty());

        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
    }

    #[test]
    fn poll_limit_fifo_ordering() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        for &i in &[10, 20, 30, 40, 50] {
            notifier.notify(Token::new(i)).unwrap();
        }

        poller.poll_limit(&mut events, 2);
        let indices: Vec<usize> = events.drain().map(Token::index).collect();
        assert_eq!(indices, vec![10, 20]);

        poller.poll_limit(&mut events, 2);
        let indices: Vec<usize> = events.drain().map(Token::index).collect();
        assert_eq!(indices, vec![30, 40]);

        poller.poll(&mut events);
        let indices: Vec<usize> = events.iter().map(Token::index).collect();
        assert_eq!(indices, vec![50]);
    }

    #[test]
    fn poll_limit_pending_carryover() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        for i in 0..10 {
            notifier.notify(Token::new(i)).unwrap();
        }

        poller.poll_limit(&mut events, 3);
        assert_eq!(events.len(), 3);
        events.drain().for_each(drop);

        poller.poll_limit(&mut events, 3);
        assert_eq!(events.len(), 3);
        events.drain().for_each(drop);

        poller.poll(&mut events);
        assert_eq!(events.len(), 4);
        events.drain().for_each(drop);

        poller.poll(&mut events);
        assert!(events.is_empty());
    }

    #[test]
    fn conflation_across_poll_limit_boundary() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);

        for i in 0..10 {
            notifier.notify(Token::new(i)).unwrap();
        }

        poller.poll_limit(&mut events, 3);
        let drained: Vec<usize> = events.drain().map(Token::index).collect();
        assert_eq!(drained.len(), 3);

        // Re-notify a token NOT yet drained — flag is still true. Conflated.
        let undrained: Vec<usize> = (0..10).filter(|i| !drained.contains(i)).collect();
        notifier.notify(Token::new(undrained[0])).unwrap();

        poller.poll(&mut events);
        assert_eq!(events.len(), 7);
    }

    #[test]
    fn conflation_after_drain() {
        let (notifier, poller) = event_queue(64);
        let mut events = Events::with_capacity(64);
        let t = Token::new(5);

        notifier.notify(t).unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        events.drain().for_each(drop);

        notifier.notify(t).unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.iter().next().unwrap().index(), 5);
    }
}
