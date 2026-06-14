//! Single-threaded object pools.
//!
//! Two variants:
//! - [`BoundedPool`]: Fixed capacity, pre-initialized objects
//! - [`Pool`]: Growable, creates objects on demand via factory
//!
//! Both use LIFO ordering for cache locality.

use std::cell::UnsafeCell;
use std::fmt;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

// =============================================================================
// Inner - shared storage for both pool types
// =============================================================================

#[repr(C)]
struct Inner<T> {
    /// Stack of available objects (LIFO)
    data: UnsafeCell<Vec<T>>,

    /// Reset function - called when object returns to pool
    #[allow(clippy::type_complexity)]
    reset: UnsafeCell<Box<dyn FnMut(&mut T)>>,

    /// Factory function - only initialized for Pool, not BoundedPool
    #[allow(clippy::type_complexity)]
    factory: UnsafeCell<MaybeUninit<Box<dyn FnMut() -> T>>>,
}

impl<T> Inner<T> {
    /// Create inner for BoundedPool - factory is NOT initialized
    fn new_bounded<R>(data: Vec<T>, reset: R) -> Self
    where
        R: FnMut(&mut T) + 'static,
    {
        Self {
            data: UnsafeCell::new(data),
            reset: UnsafeCell::new(Box::new(reset)),
            factory: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Create inner for Pool - factory IS initialized
    fn new_growable<F, R>(data: Vec<T>, factory: F, reset: R) -> Self
    where
        F: FnMut() -> T + 'static,
        R: FnMut(&mut T) + 'static,
    {
        Self {
            data: UnsafeCell::new(data),
            reset: UnsafeCell::new(Box::new(reset)),
            factory: UnsafeCell::new(MaybeUninit::new(Box::new(factory))),
        }
    }

    /// Try to pop from available stack. Used by both pool types.
    fn try_pop(&self) -> Option<T> {
        // SAFETY: Single-threaded access enforced by !Sync on BoundedPool/Pool
        // (both use Rc<Inner<T>> which is !Send + !Sync). No concurrent mutation.
        let data = unsafe { &mut *self.data.get() };
        data.pop()
    }

    /// Pop or create via factory.
    ///
    /// # Safety
    ///
    /// Caller must ensure factory was initialized (i.e., this is Pool, not BoundedPool)
    #[allow(clippy::option_if_let_else)]
    unsafe fn pop_or_create(&self) -> T {
        // SAFETY: Single-threaded access enforced by !Sync on Pool (Rc-based).
        // Caller guarantees factory is initialized (only called from Pool, not BoundedPool).
        // assume_init_mut is sound because new_growable writes MaybeUninit::new(factory).
        unsafe {
            let data = &mut *self.data.get();
            if let Some(value) = data.pop() {
                value
            } else {
                let factory = &mut *self.factory.get();
                (factory.assume_init_mut())()
            }
        }
    }

    /// Reset and return value to available stack
    fn return_value(&self, value: &mut T) {
        // SAFETY: Single-threaded access enforced by !Sync on BoundedPool/Pool (Rc-based).
        // No concurrent mutation of the reset closure.
        let reset = unsafe { &mut *self.reset.get() };
        reset(value);
    }

    /// Push value back to available stack
    fn push(&self, value: T) {
        // SAFETY: Single-threaded access enforced by !Sync on BoundedPool/Pool (Rc-based).
        // No concurrent mutation of the data vec.
        let data = unsafe { &mut *self.data.get() };
        data.push(value);
    }

    fn available(&self) -> usize {
        // SAFETY: Single-threaded access enforced by !Sync (Rc-based). Reading len
        // while no concurrent mutation is possible.
        unsafe { (*self.data.get()).len() }
    }

    fn is_empty(&self) -> bool {
        self.available() == 0
    }
}

// =============================================================================
// BoundedPool - fixed capacity, pre-initialized
// =============================================================================

/// Fixed-capacity object pool with LIFO reuse.
///
/// All objects are pre-initialized at construction. When all objects are
/// acquired, `try_acquire()` returns `None`.
///
/// # Example
///
/// ```
/// use nexus_pool::local::BoundedPool;
///
/// let pool = BoundedPool::new(
///     100,
///     || Vec::<u8>::with_capacity(1024),
///     |v| v.clear(),
/// );
///
/// let mut buf = pool.try_acquire().unwrap();
/// buf.extend_from_slice(b"hello");
/// // buf auto-returns to pool on drop, clear() is called
/// ```
pub struct BoundedPool<T> {
    inner: Rc<Inner<T>>,
}

impl<T> BoundedPool<T> {
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
    /// Panics if capacity is zero.
    pub fn new<I, R>(capacity: usize, mut init: I, reset: R) -> Self
    where
        I: FnMut() -> T,
        R: FnMut(&mut T) + 'static,
    {
        assert!(capacity > 0, "capacity must be non-zero");

        let mut data = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            data.push(init());
        }

        Self {
            inner: Rc::new(Inner::new_bounded(data, reset)),
        }
    }

    /// Attempts to acquire an object from the pool.
    ///
    /// Returns `None` if all objects are currently in use.
    #[inline]
    pub fn try_acquire(&self) -> Option<Pooled<T>> {
        self.inner.try_pop().map(|value| Pooled {
            value: ManuallyDrop::new(value),
            inner: Rc::clone(&self.inner),
        })
    }

    /// Returns the number of available objects.
    #[inline]
    pub fn available(&self) -> usize {
        self.inner.available()
    }

    /// Returns true if there are no more available objects.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

// =============================================================================
// Pool - growable, creates on demand
// =============================================================================

/// Growable object pool with LIFO reuse.
///
/// Objects are created on demand via the factory function when the pool
/// is empty. Use `try_acquire()` for the fast path that only returns
/// pooled objects, or `acquire()` which may create new objects.
///
/// # Example
///
/// ```
/// use nexus_pool::local::Pool;
///
/// let pool = Pool::new(
///     || Vec::<u8>::with_capacity(1024),
///     |v| v.clear(),
/// );
///
/// let mut buf = pool.acquire(); // Creates new object
/// buf.extend_from_slice(b"hello");
/// drop(buf); // Returns to pool, clear() is called
///
/// let buf2 = pool.acquire(); // Reuses existing (now empty) object
/// ```
pub struct Pool<T> {
    inner: Rc<Inner<T>>,
}

impl<T> Pool<T> {
    /// Creates an empty pool with the given factory and reset functions.
    ///
    /// # Arguments
    ///
    /// * `factory` - Creates new objects when pool is empty
    /// * `reset` - Called when object returns to pool (e.g., `Vec::clear`)
    pub fn new<F, R>(factory: F, reset: R) -> Self
    where
        F: FnMut() -> T + 'static,
        R: FnMut(&mut T) + 'static,
    {
        Self {
            inner: Rc::new(Inner::new_growable(Vec::new(), factory, reset)),
        }
    }

    /// Creates a pool pre-populated with `capacity` objects.
    pub fn with_capacity<F, R>(capacity: usize, mut factory: F, reset: R) -> Self
    where
        F: FnMut() -> T + 'static,
        R: FnMut(&mut T) + 'static,
    {
        let mut data = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            data.push(factory());
        }

        Self {
            inner: Rc::new(Inner::new_growable(data, factory, reset)),
        }
    }

    /// Acquires an object from the pool, creating one if necessary.
    ///
    /// This always succeeds but may allocate if the pool is empty.
    pub fn acquire(&self) -> Pooled<T> {
        // SAFETY: Pool::new/with_capacity always calls new_growable, which
        // initializes the factory via MaybeUninit::new. pop_or_create's
        // precondition (factory initialized) is satisfied.
        let value = unsafe { self.inner.pop_or_create() };
        Pooled {
            value: ManuallyDrop::new(value),
            inner: Rc::clone(&self.inner),
        }
    }

    /// Attempts to acquire an object from the pool without creating.
    ///
    /// Returns `None` if the pool is empty. This is the fast path.
    #[inline]
    pub fn try_acquire(&self) -> Option<Pooled<T>> {
        self.inner.try_pop().map(|value| Pooled {
            value: ManuallyDrop::new(value),
            inner: Rc::clone(&self.inner),
        })
    }

    /// Takes an object from the pool without an RAII guard, creating one
    /// via the factory if the pool is empty.
    ///
    /// The caller is responsible for returning the object via [`put()`](Pool::put).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_pool::local::Pool;
    ///
    /// let pool = Pool::new(
    ///     || Vec::<u8>::with_capacity(1024),
    ///     |v| v.clear(),
    /// );
    ///
    /// let mut buf = pool.take();
    /// buf.extend_from_slice(b"hello");
    /// pool.put(buf); // manual return, reset is called
    /// ```
    #[inline]
    pub fn take(&self) -> T {
        // SAFETY: Pool::new/with_capacity always calls new_growable, which
        // initializes the factory via MaybeUninit::new. pop_or_create's
        // precondition (factory initialized) is satisfied.
        unsafe { self.inner.pop_or_create() }
    }

    /// Takes an object from the pool if one is available, without creating.
    ///
    /// Returns `None` if the pool is empty. The caller is responsible for
    /// returning the object via [`put()`](Pool::put).
    #[inline]
    pub fn try_take(&self) -> Option<T> {
        self.inner.try_pop()
    }

    /// Returns an object to the pool.
    ///
    /// Calls the reset function, then pushes the value back onto the
    /// available stack for reuse.
    ///
    /// # Panics
    ///
    /// If the reset closure panics, the value is leaked and the pool slot
    /// is not returned. The panic propagates normally. Reset closures must
    /// not panic — use simple operations like `Vec::clear()` or field resets.
    #[inline]
    pub fn put(&self, mut value: T) {
        self.inner.return_value(&mut value);
        self.inner.push(value);
    }

    /// Returns the number of available objects.
    #[inline]
    pub fn available(&self) -> usize {
        self.inner.available()
    }
}

impl<T> Drop for Pool<T> {
    fn drop(&mut self) {
        // SAFETY: Pool::new/with_capacity always calls new_growable, which
        // initializes the factory via MaybeUninit::new. We must drop it here
        // before the strong-count reaches zero, because Inner's Drop doesn't
        // know whether factory was initialized (BoundedPool leaves it uninit).
        //
        // Factory-ownership invariant: the factory is reachable only through
        // `Pool::acquire` / `Pool::take`, both of which take `&self` on
        // `Pool`. Once `Pool` drops, no code path can touch the factory
        // again — even if `Pooled` guards keep `Inner` alive past this
        // point via the strong Rc, the factory has been destroyed and is
        // unreachable. Inner has no `Drop` of its own, so the (now-empty)
        // `MaybeUninit` slot dies harmlessly when the last guard drops.
        unsafe {
            let factory = &mut *self.inner.factory.get();
            factory.assume_init_drop();
        }
    }
}

// =============================================================================
// Pooled - RAII guard
// =============================================================================

/// RAII guard that returns the object to the pool on drop.
///
/// The object is always returned to the pool when the guard is dropped.
/// There is no way to "take" the object out permanently.
#[must_use = "dropping the guard immediately returns the object to the pool"]
pub struct Pooled<T> {
    value: ManuallyDrop<T>,
    inner: Rc<Inner<T>>,
}

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
        // Reset and return to pool. The strong Rc guarantees Inner is
        // alive — no upgrade check needed. If `Pool` already dropped,
        // Inner is now an "orphan": values keep flowing into its Vec
        // and stay there until the last `Pooled` drops, at which point
        // the strong-count hits zero and the Vec drops in one shot.
        self.inner.return_value(&mut self.value);
        // SAFETY: value is valid (ManuallyDrop preserves it until
        // explicit take/drop). After take we never touch self.value
        // again; Inner takes ownership via push.
        let value = unsafe { ManuallyDrop::take(&mut self.value) };
        self.inner.push(value);
        // self.inner Rc drops here: one strong-count--. If we were the
        // last guard, Inner's `data: UnsafeCell<Vec<T>>` drops, which
        // drops every value still in the pool.
    }
}

impl<T> fmt::Debug for BoundedPool<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BoundedPool")
            .field("available", &self.available())
            .finish_non_exhaustive()
    }
}

impl<T> fmt::Debug for Pool<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Pool")
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
    use std::cell::Cell;
    use std::rc::Rc as StdRc;

    #[test]
    fn bounded_pool_basic() {
        let pool = BoundedPool::new(3, || Vec::<u8>::with_capacity(16), Vec::clear);

        assert_eq!(pool.available(), 3);

        let mut a = pool.try_acquire().unwrap();
        assert_eq!(pool.available(), 2);

        a.extend_from_slice(b"hello");
        assert_eq!(&*a, b"hello");

        let _b = pool.try_acquire().unwrap();
        let _c = pool.try_acquire().unwrap();

        assert_eq!(pool.available(), 0);

        // Pool exhausted
        assert!(pool.try_acquire().is_none());

        drop(a);
        assert_eq!(pool.available(), 1);

        // Can acquire again - and it's been cleared
        let d = pool.try_acquire().unwrap();
        assert!(d.is_empty()); // reset was called
    }

    #[test]
    fn bounded_pool_reset_called() {
        let reset_count = StdRc::new(Cell::new(0));
        let reset_count_clone = reset_count.clone();

        let pool = BoundedPool::new(
            2,
            || 0u32,
            move |_| {
                reset_count_clone.set(reset_count_clone.get() + 1);
            },
        );

        let a = pool.try_acquire().unwrap();
        assert_eq!(reset_count.get(), 0);

        drop(a);
        assert_eq!(reset_count.get(), 1);

        let b = pool.try_acquire().unwrap();
        let c = pool.try_acquire().unwrap();
        drop(b);
        drop(c);
        assert_eq!(reset_count.get(), 3);
    }

    #[test]
    fn bounded_pool_outlives_guard() {
        let guard;
        {
            let pool = BoundedPool::new(1, || String::from("test"), String::clear);
            guard = pool.try_acquire().unwrap();
        }
        // Pool dropped, guard still valid (Inner survives via the
        // strong Rc the guard holds).
        assert_eq!(&*guard, "test");
        // Drop guard — value returns to the orphaned Inner, then Inner
        // dies (last strong ref) and drops the value. No leak, no UAF.
        drop(guard);
    }

    #[test]
    fn growable_pool_basic() {
        let pool = Pool::new(|| Vec::<u8>::with_capacity(16), Vec::clear);

        assert_eq!(pool.available(), 0);

        // acquire creates new object
        let mut a = pool.acquire();
        a.extend_from_slice(b"hello");

        drop(a);
        assert_eq!(pool.available(), 1);

        // acquire reuses - and it's been cleared
        let b = pool.acquire();
        assert!(b.is_empty()); // reset was called
        assert_eq!(pool.available(), 0);
    }

    #[test]
    fn growable_pool_try_acquire() {
        let pool = Pool::new(|| 42u32, |_| {});

        // Empty pool, try_acquire returns None
        assert!(pool.try_acquire().is_none());

        // acquire creates
        let a = pool.acquire();
        drop(a);

        // Now try_acquire succeeds
        let b = pool.try_acquire().unwrap();
        assert_eq!(*b, 42);
    }

    #[test]
    fn growable_pool_with_capacity() {
        let pool = Pool::with_capacity(5, String::new, String::clear);

        assert_eq!(pool.available(), 5);

        let _a = pool.try_acquire().unwrap();
        let _b = pool.try_acquire().unwrap();
        assert_eq!(pool.available(), 3);
    }

    #[test]
    fn growable_pool_outlives_guard() {
        let guard;
        {
            let pool = Pool::new(|| String::from("test"), String::clear);
            guard = pool.acquire();
        }
        // Pool dropped, guard still valid (Inner alive via guard's Rc).
        assert_eq!(&*guard, "test");
        // Guard drops; value returns to orphan, last strong ref dies,
        // Inner's Vec drops the value. No leak, no UAF.
        drop(guard);
    }

    #[test]
    #[should_panic(expected = "capacity must be non-zero")]
    fn bounded_pool_zero_capacity_panics() {
        let _ = BoundedPool::new(0, || (), |()| {});
    }

    #[test]
    fn take_put_basic() {
        let pool = Pool::new(|| Vec::<u8>::with_capacity(16), Vec::clear);

        let mut buf = pool.take();
        buf.extend_from_slice(b"hello");
        assert_eq!(&buf, b"hello");

        pool.put(buf);
        assert_eq!(pool.available(), 1);

        let reused = pool.take();
        assert!(reused.is_empty()); // reset was called
    }

    #[test]
    fn try_take_empty_returns_none() {
        let pool = Pool::new(|| 0u32, |_| {});

        assert!(pool.try_take().is_none());

        let v = pool.take(); // creates via factory
        pool.put(v);

        assert!(pool.try_take().is_some());
    }

    #[test]
    fn take_put_reset_called() {
        let reset_count = StdRc::new(Cell::new(0));
        let rc = reset_count.clone();

        let pool = Pool::new(
            || 0u32,
            move |_| {
                rc.set(rc.get() + 1);
            },
        );

        let v = pool.take();
        assert_eq!(reset_count.get(), 0);

        pool.put(v);
        assert_eq!(reset_count.get(), 1);

        let v = pool.take();
        pool.put(v);
        assert_eq!(reset_count.get(), 2);
    }

    #[test]
    fn take_put_with_capacity() {
        let pool = Pool::with_capacity(5, || String::from("init"), String::clear);
        assert_eq!(pool.available(), 5);

        let s = pool.try_take().unwrap();
        assert_eq!(s, "init");
        assert_eq!(pool.available(), 4);

        pool.put(s);
        assert_eq!(pool.available(), 5);
    }

    #[test]
    fn mix_raii_and_manual() {
        let pool = Pool::with_capacity(3, Vec::<u8>::new, Vec::clear);

        // Take one manually
        let mut manual = pool.take();
        manual.push(1);

        // Acquire one via RAII
        let mut guard = pool.acquire();
        guard.push(2);

        assert_eq!(pool.available(), 1);

        // Return manual
        pool.put(manual);
        assert_eq!(pool.available(), 2);

        // Drop guard
        drop(guard);
        assert_eq!(pool.available(), 3);
    }
}
