//! Single-threaded notification with dedup.
//!
//! [`LocalNotify`] is the single-threaded counterpart to the cross-thread
//! [`event_queue`](crate::event_queue). Same dedup semantics — each token
//! fires at most once per poll cycle — but uses `&mut self` instead of
//! atomics.
//!
//! # API correspondence
//!
//! | Cross-thread | Single-threaded | Notes |
//! |--------------|-----------------|-------|
//! | [`event_queue(n)`](crate::event_queue) | [`LocalNotify::with_capacity`] | |
//! | [`Notifier::notify(token)`](crate::Notifier::notify) | [`LocalNotify::mark(token)`](LocalNotify::mark) | `&mut self` vs `&self` |
//! | [`Poller::poll(events)`](crate::Poller::poll) | [`LocalNotify::poll(events)`](LocalNotify::poll) | same `Events` buffer |
//! | `AtomicBool` per token | bitset (`Vec<u64>`) | |
//! | MPSC ring buffer | `Vec<usize>` dispatch list | |
//!
//! # Performance targets
//!
//! | Operation | Target | Notes |
//! |-----------|--------|-------|
//! | `mark(token)` | ~5-7 cy | bit test + conditional push |
//! | `poll()` per token | ~2 cy | sequential drain |
//! | frame clear (poll) | <1 cy amortized | memset bits + vec clear |
//! | `register()` | ~30 cy | cold path |
//!
//! # Example
//!
//! ```
//! use nexus_notify::local::LocalNotify;
//! use nexus_notify::Token;
//!
//! let mut notify = LocalNotify::with_capacity(4);
//! let mut events = nexus_notify::Events::with_capacity(4);
//!
//! let t0 = notify.register();
//! let t1 = notify.register();
//!
//! // Mark both tokens
//! notify.mark(t0);
//! notify.mark(t1);
//! notify.mark(t0); // deduped — already marked
//!
//! // Poll — each token appears once
//! notify.poll(&mut events);
//! assert_eq!(events.len(), 2);
//!
//! // Frame cleared — ready for next cycle
//! assert!(!notify.has_notified());
//! ```

use crate::event_queue::{Events, Token};

// =============================================================================
// LocalNotify
// =============================================================================

/// Single-threaded notification with per-token dedup.
///
/// Mirrors [`event_queue`](crate::event_queue) semantics for
/// single-threaded use. Tokens are registered, marked as changed,
/// and polled. Each token appears at most once per poll cycle.
///
/// The interest/subscription layer (mapping data sources to reactors)
/// is a higher-level concern handled by the consumer (e.g., the
/// reactor system in nexus-rt).
#[derive(Debug)]
pub struct LocalNotify {
    /// Dedup bitset. Bit N = token N is in `dispatch_list`.
    /// `bits[N / 64] & (1 << (N % 64))`. Grows when tokens are
    /// registered beyond current capacity.
    bits: Vec<u64>,

    /// Token indices queued for dispatch this cycle (deduped via `bits`).
    dispatch_list: Vec<usize>,

    /// Index of the next token to dispatch. Advances on partial drain
    /// instead of shifting the Vec; reset to 0 on full drain.
    dispatch_head: usize,

    /// High-water mark for token allocation.
    num_tokens: usize,
}

impl LocalNotify {
    /// Create with an initial capacity hint. Grows as needed.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            bits: vec![0u64; capacity.div_ceil(64)],
            dispatch_list: Vec::with_capacity(capacity),
            dispatch_head: 0,
            num_tokens: 0,
        }
    }

    /// Register a new token. Returns its identifier.
    ///
    /// Grows the dedup bitset if needed.
    pub fn register(&mut self) -> Token {
        let idx = self.num_tokens;
        self.num_tokens += 1;
        let word = idx / 64;
        if word >= self.bits.len() {
            self.bits.push(0);
        }
        Token::new(idx)
    }

    /// Ensure the bitset can hold a token at the given index.
    ///
    /// Use this when token indices are managed externally (e.g., by a
    /// slab) and may not be sequential. Grows the bitset and updates
    /// the high-water mark if needed.
    pub fn ensure_capacity(&mut self, idx: usize) {
        if idx >= self.num_tokens {
            self.num_tokens = idx + 1;
        }
        let word = idx / 64;
        if word >= self.bits.len() {
            self.bits.resize(word + 1, 0);
        }
    }

    /// Mark a token as changed this cycle.
    ///
    /// If the token is already marked (deduped), this is a no-op.
    ///
    /// # Panics
    ///
    /// Panics if `token.index() >= num_tokens` (unregistered token).
    #[inline]
    pub fn mark(&mut self, token: Token) {
        let idx = token.index();
        // Match the sync variant (event_queue.rs:107) which uses
        // debug_assert! for the same precondition. Release builds skip
        // the bounds check; the underlying `bits[word]` index would panic
        // on out-of-bounds anyway.
        debug_assert!(
            idx < self.num_tokens,
            "token index {} out of range ({})",
            idx,
            self.num_tokens,
        );
        let word = idx / 64;
        let bit = 1u64 << (idx % 64);
        // Invariant: bits is always large enough for any registered
        // token — register() grows it on allocation.
        if self.bits[word] & bit == 0 {
            self.bits[word] |= bit;
            self.dispatch_list.push(idx);
        }
    }

    /// Drain all marked tokens into the events buffer.
    ///
    /// The events buffer is cleared then filled. Tokens appear in
    /// mark order. After polling, all dedup state is cleared —
    /// ready for the next cycle.
    ///
    /// Mirrors [`Poller::poll`](crate::Poller::poll).
    #[inline]
    pub fn poll(&mut self, events: &mut Events) {
        self.poll_limit(events, usize::MAX);
    }

    /// Drain up to `limit` marked tokens into the events buffer.
    ///
    /// Remaining tokens stay queued for the next poll call.
    /// Tokens appear in mark order (FIFO).
    ///
    /// Mirrors [`Poller::poll_limit`](crate::Poller::poll_limit).
    #[inline]
    pub fn poll_limit(&mut self, events: &mut Events, limit: usize) {
        events.clear();
        let remaining = self.dispatch_list.len() - self.dispatch_head;
        let drain_count = remaining.min(limit);
        let head = self.dispatch_head;
        for &idx in &self.dispatch_list[head..head + drain_count] {
            events.push(Token::new(idx));
        }
        if drain_count == remaining {
            // Full drain — bulk clear and reset cursor.
            self.bits.fill(0);
            self.dispatch_list.clear();
            self.dispatch_head = 0;
        } else {
            // Partial drain — clear bits for drained tokens, advance cursor.
            for &idx in &self.dispatch_list[head..head + drain_count] {
                self.bits[idx / 64] &= !(1u64 << (idx % 64));
            }
            self.dispatch_head += drain_count;
        }
    }

    /// Returns `true` if any token is marked.
    #[inline]
    pub fn has_notified(&self) -> bool {
        self.dispatch_head < self.dispatch_list.len()
    }

    /// Number of tokens currently marked.
    #[inline]
    pub fn notified_count(&self) -> usize {
        self.dispatch_list.len() - self.dispatch_head
    }

    /// Number of registered tokens.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.num_tokens
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn register_and_mark() {
        let mut notify = LocalNotify::with_capacity(4);
        let mut events = Events::with_capacity(4);

        let t = notify.register();
        notify.mark(t);
        assert!(notify.has_notified());

        notify.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.as_slice()[0], t);

        // Frame cleared
        assert!(!notify.has_notified());
    }

    #[test]
    fn dedup() {
        let mut notify = LocalNotify::with_capacity(4);
        let mut events = Events::with_capacity(4);

        let t = notify.register();
        notify.mark(t);
        notify.mark(t); // duplicate
        notify.mark(t); // triplicate

        notify.poll(&mut events);
        assert_eq!(events.len(), 1);
    }

    #[test]
    fn multiple_tokens() {
        let mut notify = LocalNotify::with_capacity(4);
        let mut events = Events::with_capacity(4);

        let t0 = notify.register();
        let _t1 = notify.register();
        let t2 = notify.register();

        notify.mark(t0);
        notify.mark(t2);
        // _t1 not marked

        notify.poll(&mut events);
        assert_eq!(events.len(), 2);
        assert!(events.as_slice().contains(&t0));
        assert!(events.as_slice().contains(&t2));
    }

    #[test]
    fn mark_order_preserved() {
        let mut notify = LocalNotify::with_capacity(4);
        let mut events = Events::with_capacity(4);

        let t0 = notify.register();
        let t1 = notify.register();
        let t2 = notify.register();

        notify.mark(t2);
        notify.mark(t0);
        notify.mark(t1);

        notify.poll(&mut events);
        assert_eq!(events.as_slice(), &[t2, t0, t1]);
    }

    #[test]
    fn multiple_cycles() {
        let mut notify = LocalNotify::with_capacity(4);
        let mut events = Events::with_capacity(4);

        let t = notify.register();

        // Cycle 1
        notify.mark(t);
        notify.poll(&mut events);
        assert_eq!(events.len(), 1);

        // Cycle 2 — same token fires again
        notify.mark(t);
        notify.poll(&mut events);
        assert_eq!(events.len(), 1);
    }

    #[test]
    fn no_marks_empty_poll() {
        let mut notify = LocalNotify::with_capacity(4);
        let mut events = Events::with_capacity(4);

        let _t = notify.register();
        notify.poll(&mut events);
        assert!(events.is_empty());
        assert!(!notify.has_notified());
    }

    #[test]
    fn zero_capacity() {
        let mut notify = LocalNotify::with_capacity(0);
        let mut events = Events::with_capacity(4);

        let t = notify.register();
        notify.mark(t);

        notify.poll(&mut events);
        assert_eq!(events.len(), 1);
    }

    #[test]
    fn word_boundary_tokens() {
        let mut notify = LocalNotify::with_capacity(0);
        let mut events = Events::with_capacity(256);

        // Register 130 tokens — spans 3 u64 words
        let mut tokens = Vec::new();
        for _ in 0..130 {
            tokens.push(notify.register());
        }

        // Mark boundary tokens
        let boundary = [
            tokens[0],
            tokens[63],  // last in word 0
            tokens[64],  // first in word 1
            tokens[127], // last in word 1
            tokens[128], // first in word 2
        ];
        for &t in &boundary {
            notify.mark(t);
        }

        notify.poll(&mut events);
        assert_eq!(events.len(), 5);
        for &t in &boundary {
            assert!(events.as_slice().contains(&t));
        }

        // Second cycle — bits cleared correctly across word boundaries
        for &t in &boundary {
            notify.mark(t);
        }
        notify.poll(&mut events);
        assert_eq!(events.len(), 5);
    }

    #[test]
    fn grows_beyond_initial_capacity() {
        let mut notify = LocalNotify::with_capacity(2);
        let mut events = Events::with_capacity(256);

        let mut tokens = Vec::new();
        for _ in 0..200 {
            tokens.push(notify.register());
        }

        for &t in &tokens {
            notify.mark(t);
        }

        notify.poll(&mut events);
        assert_eq!(events.len(), 200);
    }

    #[test]
    fn poll_limit_partial() {
        let mut notify = LocalNotify::with_capacity(8);
        let mut events = Events::with_capacity(8);

        let mut tokens = Vec::new();
        for _ in 0..5 {
            tokens.push(notify.register());
        }
        for &t in &tokens {
            notify.mark(t);
        }

        // Drain only 2
        notify.poll_limit(&mut events, 2);
        assert_eq!(events.len(), 2);
        assert_eq!(notify.notified_count(), 3); // 3 remaining

        // Drain rest
        notify.poll(&mut events);
        assert_eq!(events.len(), 3);
        assert!(!notify.has_notified());
    }

    #[test]
    fn poll_limit_exceeds_count() {
        let mut notify = LocalNotify::with_capacity(4);
        let mut events = Events::with_capacity(4);

        let t = notify.register();
        notify.mark(t);

        notify.poll_limit(&mut events, 100);
        assert_eq!(events.len(), 1);
        assert!(!notify.has_notified());
    }

    #[test]
    fn notified_count() {
        let mut notify = LocalNotify::with_capacity(4);

        let t0 = notify.register();
        let t1 = notify.register();

        assert_eq!(notify.notified_count(), 0);
        notify.mark(t0);
        assert_eq!(notify.notified_count(), 1);
        notify.mark(t1);
        assert_eq!(notify.notified_count(), 2);
        notify.mark(t0); // dedup
        assert_eq!(notify.notified_count(), 2);
    }

    #[test]
    fn capacity_tracks_registrations() {
        let mut notify = LocalNotify::with_capacity(4);
        assert_eq!(notify.capacity(), 0);

        notify.register();
        notify.register();
        assert_eq!(notify.capacity(), 2);
    }
}
