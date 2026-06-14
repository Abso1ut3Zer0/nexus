//! Single-acquirer pool: one thread acquires, any thread can return.
//!
//! Items are acquired from a single point (the `Acquirer`) and can be
//! returned from any thread via `Drop` on `Pooled`.
//!
//! Uses LIFO ordering for cache locality.

use std::fmt;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, DerefMut};

use crate::loom_impl::{Arc, AtomicUsize, Ordering, UnsafeCell};

const NONE: usize = usize::MAX;

// =============================================================================
// Slot - individual pool entry
// =============================================================================

struct Slot<T> {
    value: UnsafeCell<MaybeUninit<T>>,
    next: AtomicUsize,
}

// SAFETY: Slot is Send because value is only accessed when the slot is "owned"
// (popped from free list), so no concurrent access occurs. next is AtomicUsize.
unsafe impl<T: Send> Send for Slot<T> {}
// SAFETY: Slot is Sync because value (UnsafeCell) is only accessed when owned
// (not in the free list), so no data race is possible. next is AtomicUsize (Sync).
unsafe impl<T: Send + Sync> Sync for Slot<T> {}

// =============================================================================
// Inner - shared pool state
// =============================================================================

struct Inner<T> {
    slots: Box<[Slot<T>]>,
    free_head: AtomicUsize,
    free_count: AtomicUsize,
    reset: Box<dyn Fn(&mut T) + Send + Sync>,
}

impl<T> Inner<T> {
    /// Push a slot back onto the free list. Called from any thread.
    fn push(&self, idx: usize, mut value: T) {
        // Reset the value
        (self.reset)(&mut value);

        // SAFETY: We own this slot (it was popped from the free list via CAS).
        // No other thread can access it until we push it back. MaybeUninit::write
        // initializes the slot for the next acquirer.
        self.slots[idx].value.with_mut(|ptr| unsafe {
            (*ptr).write(value);
        });

        // Link into free list with CAS loop
        loop {
            let head = self.free_head.load(Ordering::Relaxed);
            self.slots[idx].next.store(head, Ordering::Relaxed);

            match self.free_head.compare_exchange_weak(
                head,
                idx,
                Ordering::Release, // Publishes value write + next write
                Ordering::Relaxed, // Failure just retries
            ) {
                Ok(_) => {
                    self.free_count.fetch_add(1, Ordering::Relaxed);
                    return;
                }
                Err(_) => std::hint::spin_loop(),
            }
        }
    }

    /// Pop a slot from the free list. Called only from Acquirer thread.
    fn pop(&self) -> Option<usize> {
        loop {
            let head = self.free_head.load(Ordering::Acquire);
            if head == NONE {
                return None;
            }

            // Read next - safe because we Acquired head, syncs with pusher's Release
            let next = self.slots[head].next.load(Ordering::Relaxed);

            match self.free_head.compare_exchange_weak(
                head,
                next,
                Ordering::Acquire, // Syncs with pusher's Release
                Ordering::Acquire, // On fail, need to see new head
            ) {
                Ok(_) => {
                    self.free_count.fetch_sub(1, Ordering::Relaxed);
                    return Some(head);
                }
                Err(_) => {
                    // Pusher added something newer - retry for hotter item
                    std::hint::spin_loop();
                }
            }
        }
    }

    /// Get reference to value at index.
    ///
    /// # Safety
    ///
    /// Caller must own the slot (have popped it) and slot must contain valid value.
    unsafe fn read_value(&self, idx: usize) -> T {
        // SAFETY: Caller guarantees slot was popped (owned) and contains a valid value
        // written by new() or push(). assume_init_read moves the value out without
        // dropping the MaybeUninit, which is correct since the slot will be rewritten
        // on the next push.
        self.slots[idx]
            .value
            .with_mut(|ptr| unsafe { (*ptr).assume_init_read() })
    }
}

impl<T> Drop for Inner<T> {
    fn drop(&mut self) {
        // Inner::drop runs only when the last Arc dies — which means
        // no `Pooled` guards are alive (each guard holds a strong
        // Arc). So every slot that was ever acquired has been pushed
        // back via `Pooled::drop`, and the free list now contains
        // every slot we own. Drop them all here. The only way a slot
        // can be missing from the free list at this point is if a
        // reset closure panicked during a guard's drop — that path
        // leaks the value (documented in caveats.md §1) and is the
        // same as the 1.0.x behavior.
        let mut idx = self.free_head.load(Ordering::Relaxed);
        while idx != NONE {
            // SAFETY: Slots in the free list contain valid values (written by new()
            // or push()). Slots NOT in the free list have been moved out via
            // assume_init_read in pop and are handled by Pooled's Drop. We have
            // &mut self (exclusive access during drop), so Relaxed load is correct.
            self.slots[idx].value.with_mut(|ptr| unsafe {
                (*ptr).assume_init_drop();
            });
            idx = self.slots[idx].next.load(Ordering::Relaxed);
        }
        // MaybeUninit doesn't drop contents, so Box<[Slot<T>]> will just
        // deallocate memory without double-dropping.
    }
}

// =============================================================================
// Pool - the pool and acquire handle combined
// =============================================================================

/// A bounded pool where one thread acquires and any thread can return.
///
/// Only one `Pool` exists per pool. It cannot be cloned or shared
/// across threads (it is `Send` but not `Sync` or `Clone`).
///
/// When the `Pool` is dropped while `Pooled` guards are still alive,
/// the guards keep `Inner` alive via a strong `Arc`. Each guard, on
/// drop, returns its value to the (now-orphaned) free list; the last
/// guard to drop releases `Inner`, which drops every in-pool slot.
/// See `docs/caveats.md` §2.
///
/// # Example
///
/// ```
/// use nexus_pool::sync::Pool;
///
/// let acquirer = Pool::new(
///     100,
///     || Vec::<u8>::with_capacity(1024),
///     |v| v.clear(),
/// );
///
/// // Acquirer thread
/// let mut buf = acquirer.try_acquire().unwrap();
/// buf.extend_from_slice(b"hello");
///
/// // Can send buf to another thread
/// std::thread::spawn(move || {
///     println!("{:?}", &*buf);
///     // buf returns to pool on drop
/// }).join().unwrap();
/// ```
pub struct Pool<T> {
    inner: Arc<Inner<T>>,
}

// SAFETY: Pool is Send (can be moved to another thread) but not Sync (not shared).
// Inner uses atomics for the free list. Values in UnsafeCell are only accessed
// when a slot is owned (popped via CAS). T: Send ensures values can cross threads.
// Pool is not Clone — single acquirer enforced at the type level.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<T: Send> Send for Pool<T> {}

impl<T> Pool<T> {
    /// Creates a pool with `capacity` pre-initialized objects.
    ///
    /// # Arguments
    ///
    /// * `capacity` - Number of objects to pre-allocate
    /// * `init` - Factory function to create each object
    /// * `reset` - Called when object returns to pool (e.g., `Vec::clear`)
    ///
    /// # Panics
    ///
    /// Panics if capacity is zero or exceeds `usize::MAX - 1`.
    ///
    /// The `reset` closure must not panic. If it does, the value is leaked
    /// and the pool slot is not returned. Use simple operations like
    /// `Vec::clear()` or field resets.
    pub fn new<I, R>(capacity: usize, mut init: I, reset: R) -> Self
    where
        I: FnMut() -> T,
        R: Fn(&mut T) + Send + Sync + 'static,
    {
        assert!(capacity > 0, "capacity must be non-zero");
        assert!(capacity < NONE, "capacity must be less than {}", NONE);

        // Build slots with linked free list: 0 -> 1 -> 2 -> ... -> NONE
        let slots: Box<[Slot<T>]> = (0..capacity)
            .map(|i| Slot {
                value: UnsafeCell::new(MaybeUninit::new(init())),
                next: AtomicUsize::new(if i + 1 < capacity { i + 1 } else { NONE }),
            })
            .collect();

        Self {
            inner: Arc::new(Inner {
                slots,
                free_head: AtomicUsize::new(0), // Head of free list
                free_count: AtomicUsize::new(capacity),
                reset: Box::new(reset),
            }),
        }
    }

    /// Attempts to acquire an object from the pool.
    ///
    /// Returns `None` if all objects are currently in use.
    #[inline]
    pub fn try_acquire(&self) -> Option<Pooled<T>> {
        self.inner.pop().map(|idx| {
            // SAFETY: We just popped this slot via CAS (exclusive ownership).
            // The slot contains a valid value written by new() or a prior push().
            let value = unsafe { self.inner.read_value(idx) };
            Pooled {
                value: ManuallyDrop::new(value),
                idx,
                inner: Arc::clone(&self.inner),
            }
        })
    }

    /// Returns the number of available objects.
    ///
    /// O(1) — backed by an atomic counter. This is a snapshot and may
    /// be immediately outdated if other threads are returning objects
    /// concurrently.
    #[inline]
    pub fn available(&self) -> usize {
        self.inner.free_count.load(Ordering::Relaxed)
    }
}

// =============================================================================
// Pooled - RAII guard
// =============================================================================

/// RAII guard that returns the object to the pool on drop.
///
/// This guard can be sent to other threads. When dropped, the object
/// is automatically returned to the pool's storage. If the pool was
/// already dropped, the value goes back into the orphaned `Inner`,
/// which finally dies (along with every in-pool value) when the last
/// `Pooled` exits. See `docs/caveats.md` §2.
#[must_use = "dropping the guard immediately returns the object to the pool"]
pub struct Pooled<T> {
    value: ManuallyDrop<T>,
    idx: usize,
    inner: Arc<Inner<T>>,
}

// SAFETY: Pooled owns its value exclusively (ManuallyDrop<T>). The Arc<Inner<T>>
// is only used during drop to push the slot back via atomic CAS. T: Send ensures
// the value can cross threads. Arc<T: Send> is itself Send (same as Weak was).
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<T: Send> Send for Pooled<T> {}
// SAFETY: Pooled's &self access goes through Deref to &T, which requires T: Sync.
// The Arc and idx fields are not mutated through &self.
unsafe impl<T: Send + Sync> Sync for Pooled<T> {}

impl<T> Deref for Pooled<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T> DerefMut for Pooled<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T> Drop for Pooled<T> {
    fn drop(&mut self) {
        // SAFETY: self.inner is a strong Arc — Inner is alive by
        // construction. Value is valid (ManuallyDrop preserves it
        // until explicit take/drop). After take, self.value is
        // consumed; inner.push writes it back to the slot.
        let value = unsafe { ManuallyDrop::take(&mut self.value) };
        self.inner.push(self.idx, value);
        // self.inner Arc drops here: one strong fetch_sub. If we were
        // the last reference, Inner::drop walks the free list and
        // assume_init_drops every in-pool slot (including the one we
        // just pushed). Arc's fetch_sub(Release) + last-drop
        // fence(Acquire) is the canonical "single-writer drops after
        // all readers" pattern — sufficient for the refcount alone;
        // the value transfer is independently ordered by the Release
        // CAS in `Inner::push`.
    }
}

impl<T> fmt::Debug for Pool<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Pool")
            .field("capacity", &self.inner.slots.len())
            .field("available", &self.available())
            .finish_non_exhaustive()
    }
}

impl<T> fmt::Debug for Pooled<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Pooled").finish_non_exhaustive()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;
    use std::thread;

    #[test]
    fn basic_acquire_release() {
        let acquirer = Pool::new(3, || Vec::<u8>::with_capacity(16), Vec::clear);

        let mut a = acquirer.try_acquire().unwrap();
        a.extend_from_slice(b"hello");
        assert_eq!(&*a, b"hello");

        let _b = acquirer.try_acquire().unwrap();
        let _c = acquirer.try_acquire().unwrap();

        // Pool exhausted
        assert!(acquirer.try_acquire().is_none());

        // Return one
        drop(a);

        // Can acquire again - and it's been cleared
        let d = acquirer.try_acquire().unwrap();
        assert!(d.is_empty());
    }

    #[test]
    fn cross_thread_return() {
        let acquirer = Pool::new(2, || 42u32, |_| {});

        let item = acquirer.try_acquire().unwrap();
        assert_eq!(*item, 42);

        // Send to another thread to drop
        thread::spawn(move || {
            assert_eq!(*item, 42);
            drop(item);
        })
        .join()
        .unwrap();

        // Should be back in pool
        let item2 = acquirer.try_acquire().unwrap();
        assert_eq!(*item2, 42);
    }

    #[test]
    fn acquirer_dropped_first() {
        let item;
        {
            let acquirer = Pool::new(1, || String::from("test"), String::clear);
            item = acquirer.try_acquire().unwrap();
            // acquirer drops here — its Arc decrements but the item
            // still holds a strong Arc, so Inner survives.
        }
        // item still valid — we can access it.
        assert_eq!(&*item, "test");
        // item drops here: returns slot to the orphan free list, Arc
        // hits zero, Inner::drop walks the free list and drops every
        // in-pool slot. No leak, no UAF.
    }

    #[test]
    fn reset_called_on_return() {
        let reset_count = Arc::new(AtomicUsize::new(0));
        let reset_count_clone = Arc::clone(&reset_count);

        let acquirer = Pool::new(
            2,
            || 0u32,
            move |_| {
                reset_count_clone.fetch_add(1, Ordering::Relaxed);
            },
        );

        let a = acquirer.try_acquire().unwrap();
        assert_eq!(reset_count.load(Ordering::Relaxed), 0);

        drop(a);
        assert_eq!(reset_count.load(Ordering::Relaxed), 1);

        let b = acquirer.try_acquire().unwrap();
        let c = acquirer.try_acquire().unwrap();
        drop(b);
        drop(c);
        assert_eq!(reset_count.load(Ordering::Relaxed), 3);
    }

    #[test]
    fn lifo_ordering() {
        let acquirer = Pool::new(3, Vec::<u8>::new, Vec::clear);

        let mut guard_a = acquirer.try_acquire().unwrap();
        let mut guard_b = acquirer.try_acquire().unwrap();
        let mut guard_c = acquirer.try_acquire().unwrap();

        guard_a.push(1);
        guard_b.push(2);
        guard_c.push(3);

        // Return in order: a, b, c
        drop(guard_a);
        drop(guard_b);
        drop(guard_c);

        // Should get back in LIFO order: c, b, a
        let reacquired_1 = acquirer.try_acquire().unwrap();
        assert!(reacquired_1.is_empty()); // reset was called, but this was 'c'

        let reacquired_2 = acquirer.try_acquire().unwrap();
        assert!(reacquired_2.is_empty()); // this was 'b'

        let reacquired_3 = acquirer.try_acquire().unwrap();
        assert!(reacquired_3.is_empty()); // this was 'a'
    }

    #[test]
    #[should_panic(expected = "capacity must be non-zero")]
    fn zero_capacity_panics() {
        let _ = Pool::new(0, || (), |()| {});
    }

    // =========================================================================
    // Stress tests
    // =========================================================================

    #[test]
    fn stress_single_thread() {
        let acquirer = Pool::new(100, || Vec::<u8>::with_capacity(64), Vec::clear);

        for _ in 0..10_000 {
            let mut items: Vec<_> = (0..50).filter_map(|_| acquirer.try_acquire()).collect();

            for item in &mut items {
                item.extend_from_slice(b"data");
            }

            drop(items);
        }

        // All items should be back
        let count = acquirer.available();
        assert_eq!(count, 100);
    }

    #[test]
    fn stress_multi_thread_return() {
        let acquirer = Pool::new(
            100,
            || AtomicUsize::new(0),
            |v| {
                v.store(0, Ordering::Relaxed);
            },
        );

        let returned = Arc::new(AtomicUsize::new(0));

        thread::scope(|s| {
            let (tx, rx) = std::sync::mpsc::channel();
            let returned_clone = Arc::clone(&returned);

            // Single worker thread receives and returns items
            s.spawn(move || {
                while let Ok(item) = rx.recv() {
                    let _item: Pooled<AtomicUsize> = item;
                    returned_clone.fetch_add(1, Ordering::Relaxed);
                    // item drops here, returns to pool
                }
            });

            // Main thread acquires and sends to worker
            let mut sent = 0;
            while sent < 1000 {
                if let Some(item) = acquirer.try_acquire() {
                    tx.send(item).unwrap();
                    sent += 1;
                } else {
                    // Pool exhausted, wait a bit for returns
                    thread::yield_now();
                }
            }
            // tx drops here, worker sees disconnect
        });

        assert_eq!(returned.load(Ordering::Relaxed), 1000);
    }

    #[test]
    fn stress_concurrent_return() {
        // Multiple threads returning simultaneously
        let acquirer = Pool::new(1000, || 0u64, |_| {});

        // Acquire all items
        let items: Vec<_> = (0..1000).filter_map(|_| acquirer.try_acquire()).collect();
        assert_eq!(items.len(), 1000);

        // Split items across threads and return concurrently
        let items_per_thread = 250;
        let mut item_chunks: Vec<Vec<_>> = Vec::new();
        let mut iter = items.into_iter();
        for _ in 0..4 {
            item_chunks.push(iter.by_ref().take(items_per_thread).collect());
        }

        thread::scope(|s| {
            for chunk in item_chunks {
                s.spawn(move || {
                    for item in chunk {
                        drop(item);
                    }
                });
            }
        });

        // All items should be back
        let count = acquirer.available();
        assert_eq!(count, 1000);
    }
}
