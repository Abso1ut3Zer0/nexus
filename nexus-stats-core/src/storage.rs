//! Fixed-capacity storage shared by the windowed types.
//!
//! Built for the nexus-stats crates, not as a general-purpose collection:
//! the API is shaped by what the windowed statistics need on their hot paths
//! (the evicted sample from `push`, the fill-returning `replace`, the
//! storage-order `raw`), and it is public because the subcrates live in
//! separate crates. One allocation at construction, nothing after. The length
//! lives in the slice and nowhere else, and the wrap is a compare, not a `%`:
//! the two things that keep a ring's bounds checks folding on the hot path.

use alloc::boxed::Box;
use alloc::vec;

use crate::ConfigError;

/// Fixed-capacity ring of `Copy` samples: the newest sample overwrites the
/// oldest. A sliding window, not a queue: there is no pop.
///
/// Shaped for the nexus-stats windowed types rather than as a general-purpose
/// ring buffer; see the module docs.
///
/// `push` hands back the sample it evicted once the ring is full, which is
/// the "value from `capacity` steps ago" every lagged computation wants;
/// `replace` is the same write returning the slot's previous content
/// unconditionally (the fill while filling), for arithmetic that absorbs the
/// fill. `as_slices` and `iter` walk the contents oldest-first at any fill, so
/// a caller never reads the fill value by mistake.
///
/// Per push this is one store, one increment and one compare (the wrap);
/// fullness is a flag set inside that wrap, so nothing is added to the hot
/// path for it.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::storage::Ring;
///
/// let mut lagged = Ring::new(3, 0.0).unwrap();
/// assert_eq!(lagged.push(1.0), None);
/// assert_eq!(lagged.push(2.0), None);
/// assert_eq!(lagged.push(3.0), None);
/// assert!(lagged.is_full());
/// assert_eq!(lagged.push(4.0), Some(1.0)); // the sample from 3 pushes ago
/// assert_eq!(lagged.iter().copied().collect::<Vec<_>>(), [2.0, 3.0, 4.0]);
/// ```
#[derive(Clone)]
pub struct Ring<T> {
    buf: Box<[T]>,
    /// Slot the next push writes: the oldest sample once the ring is full.
    head: usize,
    /// Set the first time `head` wraps; from then on every slot is a sample.
    full: bool,
}

impl<T: Copy> Ring<T> {
    /// Allocates a ring of `capacity` slots, each set to `fill`.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `capacity` is zero.
    pub fn new(capacity: usize, fill: T) -> Result<Self, ConfigError> {
        if capacity == 0 {
            return Err(ConfigError::Invalid("ring capacity must be > 0"));
        }
        Ok(Self {
            buf: vec![fill; capacity].into_boxed_slice(),
            head: 0,
            full: false,
        })
    }

    /// Appends `sample`, overwriting the oldest slot once the ring is full.
    ///
    /// Returns the evicted sample, `None` while the ring is still filling.
    #[inline]
    pub fn push(&mut self, sample: T) -> Option<T> {
        let was_full = self.full;
        let previous = self.replace(sample);
        was_full.then_some(previous)
    }

    /// Appends `sample` and returns the slot's previous content: the evicted
    /// sample once the ring is full, the fill value before that.
    ///
    /// Prefer [`push`](Self::push) unless the fill value is a valid operand
    /// (a `0.0` that leaves a running sum unchanged, say).
    #[inline]
    pub fn replace(&mut self, sample: T) -> T {
        let previous = core::mem::replace(&mut self.buf[self.head], sample);
        self.head += 1;
        if self.head == self.buf.len() {
            self.head = 0;
            self.full = true;
        }
        previous
    }

    /// Samples held so far (saturates at the capacity).
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        if self.full { self.buf.len() } else { self.head }
    }

    /// Whether no sample has been pushed since construction or `clear`.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        !self.full && self.head == 0
    }

    /// Number of slots, fixed at construction.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.buf.len()
    }

    /// Whether every slot holds a pushed sample.
    #[inline]
    #[must_use]
    pub fn is_full(&self) -> bool {
        self.full
    }

    /// The held samples, oldest first, as two contiguous runs.
    ///
    /// The second run is empty until the ring has wrapped. Iterate the first
    /// then the second for chronological order; neither contains fill.
    #[inline]
    #[must_use]
    pub fn as_slices(&self) -> (&[T], &[T]) {
        if self.full {
            let (newer, older) = self.buf.split_at(self.head);
            (older, newer)
        } else {
            (&self.buf[..self.head], &[])
        }
    }

    /// The held samples, oldest first. `.rev()` gives newest first.
    #[inline]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &T> {
        let (older, newer) = self.as_slices();
        older.iter().chain(newer.iter())
    }

    /// The backing slice in storage order and the index of the slot the next
    /// push writes.
    ///
    /// Once the ring is full that index is the oldest sample, and
    /// `slice[head..]` followed by `slice[..head]` is chronological order with
    /// no fullness test; before that, `slice[head..]` still holds the fill.
    /// Prefer [`as_slices`](Self::as_slices) unless the caller has already
    /// established fullness and the per-update cost of the test matters.
    #[inline]
    #[must_use]
    pub fn raw(&self) -> (&[T], usize) {
        (&self.buf, self.head)
    }

    /// The oldest held sample.
    #[inline]
    #[must_use]
    pub fn oldest(&self) -> Option<&T> {
        self.as_slices().0.first()
    }

    /// The most recently pushed sample.
    #[inline]
    #[must_use]
    pub fn newest(&self) -> Option<&T> {
        if self.is_empty() {
            return None;
        }
        let last = if self.head == 0 {
            self.buf.len() - 1
        } else {
            self.head - 1
        };
        Some(&self.buf[last])
    }

    /// Empties the ring, setting every slot back to `fill`.
    #[inline]
    pub fn clear(&mut self, fill: T) {
        self.buf.fill(fill);
        self.head = 0;
        self.full = false;
    }
}

impl<T: Copy> core::fmt::Debug for Ring<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Ring")
            .field("capacity", &self.buf.len())
            .field("len", &self.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::collections::VecDeque;
    use std::vec::Vec;

    use super::*;

    /// Every operation agrees with a deque oracle at every fill level.
    #[test]
    fn matches_a_deque_oracle_at_every_fill() {
        for capacity in 1..=8usize {
            let mut ring = Ring::new(capacity, -1i64).unwrap();
            let mut oracle: VecDeque<i64> = VecDeque::new();
            for step in 0..(3 * capacity + 2) {
                let x = step as i64 * 10;
                let evicted = if oracle.len() == capacity {
                    oracle.pop_front()
                } else {
                    None
                };
                oracle.push_back(x);
                assert_eq!(ring.push(x), evicted, "cap {capacity} step {step}");
                assert_eq!(ring.len(), oracle.len());
                assert_eq!(ring.is_full(), oracle.len() == capacity);
                let (older, newer) = ring.as_slices();
                let chrono: Vec<i64> = older.iter().chain(newer).copied().collect();
                assert_eq!(chrono, oracle.iter().copied().collect::<Vec<_>>());
                assert_eq!(ring.iter().copied().collect::<Vec<_>>(), chrono);
                assert_eq!(ring.iter().count(), oracle.len());
                let newest_first: Vec<i64> = ring.iter().rev().copied().collect();
                assert_eq!(
                    newest_first,
                    oracle.iter().rev().copied().collect::<Vec<_>>()
                );
                assert_eq!(ring.oldest(), oracle.front());
                assert_eq!(ring.newest(), oracle.back());
            }
            ring.clear(-1);
            assert!(ring.is_empty());
            assert_eq!(ring.as_slices(), (&[][..], &[][..]));
            assert_eq!(ring.oldest(), None);
            assert_eq!(ring.newest(), None);
            assert_eq!(ring.capacity(), capacity);
        }
    }

    /// `replace` is `push` without the fullness test: the fill until full,
    /// then the evicted sample.
    #[test]
    fn replace_returns_the_fill_then_the_evicted_sample() {
        let mut ring = Ring::new(3, -1i64).unwrap();
        let mut oracle: VecDeque<i64> = VecDeque::new();
        for x in 0..10 {
            let expected = if oracle.len() == 3 {
                oracle.pop_front().unwrap()
            } else {
                -1
            };
            oracle.push_back(x);
            assert_eq!(ring.replace(x), expected, "step {x}");
            assert_eq!(
                ring.iter().copied().collect::<Vec<_>>(),
                oracle.iter().copied().collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn raw_is_chronological_once_full() {
        let mut ring = Ring::new(4, 0i64).unwrap();
        for x in 1..=6 {
            ring.push(x);
        }
        let (buf, head) = ring.raw();
        let chrono: Vec<i64> = buf[head..].iter().chain(&buf[..head]).copied().collect();
        assert_eq!(chrono, [3, 4, 5, 6]);
        assert_eq!(chrono, ring.iter().copied().collect::<Vec<_>>());
    }

    #[test]
    fn zero_capacity_is_rejected() {
        assert!(matches!(Ring::new(0, 0.0f64), Err(ConfigError::Invalid(_))));
    }

    #[test]
    fn fill_never_leaks_into_the_slices() {
        let mut ring = Ring::new(4, f64::NAN).unwrap();
        ring.push(1.0);
        ring.push(2.0);
        let (older, newer) = ring.as_slices();
        assert_eq!(older, [1.0, 2.0]);
        assert!(newer.is_empty());
        assert!(ring.iter().all(|x| x.is_finite()));
    }
}
