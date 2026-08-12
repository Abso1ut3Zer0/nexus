//! Timer driver backed by nexus-timer wheel.
//!
//! O(1) insert and cancel via hierarchical timer wheel. Expired timers
//! are collected into a pre-allocated buffer and their wakers fired.
//! Integrates with the mio poll timeout — the nearest deadline
//! determines how long epoll blocks.

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::time::{Duration, Instant};

use nexus_timer::Wheel;

// =============================================================================
// TimerDriver — owned by Runtime
// =============================================================================

/// Timer wheel driver. O(1) insert, O(1) cancel, O(fired) poll.
pub(crate) struct TimerDriver {
    wheel: Wheel<Waker>,
    /// Pre-allocated buffer for expired wakers. Reused across cycles.
    expired: Vec<Waker>,
}

impl TimerDriver {
    pub(crate) fn new(capacity: usize) -> Self {
        let now = Instant::now();
        let wheel = Wheel::unbounded(capacity, now);
        Self {
            wheel,
            expired: Vec::with_capacity(64),
        }
    }

    /// Schedule a deadline with a waker to call on expiry.
    /// Fire-and-forget — no handle returned (the Sleep future
    /// doesn't need to cancel).
    pub(crate) fn schedule(&mut self, deadline: Instant, waker: Waker) {
        self.wheel.schedule_forget(deadline, waker);
    }

    /// Returns the nearest deadline, or `None` if no timers are pending.
    pub(crate) fn next_deadline(&self) -> Option<Instant> {
        self.wheel.next_deadline()
    }

    /// Drain all expired timers and wake their tasks.
    ///
    /// Returns the number of timers fired.
    pub(crate) fn fire_expired(&mut self, now: Instant) -> usize {
        self.expired.clear();
        let fired = self.wheel.poll(now, &mut self.expired);
        for waker in self.expired.drain(..) {
            waker.wake();
        }
        fired
    }
}

// =============================================================================
// TimerHandle — Copy handle for tasks
// =============================================================================

/// [`Copy`] handle for scheduling timers from async tasks.
#[derive(Clone, Copy)]
pub struct TimerHandle {
    driver: *mut TimerDriver,
}

impl TimerHandle {
    pub(crate) fn new(driver: &mut TimerDriver) -> Self {
        Self {
            driver: std::ptr::from_mut(driver),
        }
    }

    /// Create a [`Sleep`] future that completes after `duration`.
    pub fn sleep(&self, duration: Duration) -> Sleep {
        Sleep {
            deadline: Instant::now() + duration,
            driver: self.driver,
            registered: false,
            waker: None,
        }
    }

    /// Create a [`Sleep`] future that completes at `deadline`.
    pub fn sleep_until(&self, deadline: Instant) -> Sleep {
        Sleep {
            deadline,
            driver: self.driver,
            registered: false,
            waker: None,
        }
    }
}

// =============================================================================
// Sleep future
// =============================================================================

/// Future that completes when a deadline expires.
///
/// On first poll, registers the deadline with the timer wheel. On
/// subsequent polls, re-registers if the waker has changed (the timer
/// wheel stores a clone of the waker — a stale waker means the
/// expiry notification goes to the wrong task).
pub struct Sleep {
    deadline: Instant,
    driver: *mut TimerDriver,
    registered: bool,
    waker: Option<Waker>,
}

impl Future for Sleep {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if Instant::now() >= self.deadline {
            return Poll::Ready(());
        }

        let needs_register =
            !self.registered || self.waker.as_ref().is_none_or(|w| !w.will_wake(cx.waker()));

        if needs_register {
            // SAFETY: driver pointer is valid (Runtime lifetime).
            let driver = unsafe { &mut *self.driver };
            driver.schedule(self.deadline, cx.waker().clone());
            self.registered = true;
            self.waker = Some(cx.waker().clone());
        }

        Poll::Pending
    }
}

// =============================================================================
// Timeout — wraps a future with a deadline
// =============================================================================

/// Error returned when a [`Timeout`] expires.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Elapsed;

impl std::fmt::Display for Elapsed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("deadline elapsed")
    }
}

impl std::error::Error for Elapsed {}

/// Future that completes with `Ok(T)` if the inner future finishes
/// before the deadline, or `Err(Elapsed)` if the deadline fires first.
pub struct Timeout<F> {
    future: F,
    sleep: Sleep,
}

impl<F> Timeout<F> {
    pub(crate) fn new(future: F, sleep: Sleep) -> Self {
        Self { future, sleep }
    }

    /// Recover the wrapped future, discarding the timeout.
    pub fn into_inner(self) -> F {
        self.future
    }
}

impl<F: Future> Future for Timeout<F> {
    type Output = Result<F::Output, Elapsed>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: Pin projection — we never move `future` or `sleep` out
        // of the struct. `sleep` is Unpin (no self-referential data), so
        // Pin::new is fine. `future` may not be Unpin, hence new_unchecked.
        let this = unsafe { self.get_unchecked_mut() };

        // Check the deadline first so already-expired timeouts reliably
        // return Err(Elapsed) even if the inner future is also ready.
        if Pin::new(&mut this.sleep).poll(cx).is_ready() {
            return Poll::Ready(Err(Elapsed));
        }

        // SAFETY: `this.future` is structurally pinned — self is pinned
        // and we never move future out (only into_inner consumes by value,
        // which requires ownership of Self, not Pin<&mut Self>).
        if let Poll::Ready(val) = unsafe { Pin::new_unchecked(&mut this.future) }.poll(cx) {
            return Poll::Ready(Ok(val));
        }

        Poll::Pending
    }
}

// =============================================================================
// Interval — periodic ticks
// =============================================================================

/// Strategy for handling missed interval ticks.
///
/// When processing takes longer than the interval period, ticks are
/// "missed." This enum controls how the interval catches up.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MissedTickBehavior {
    /// Fire missed ticks immediately to catch up (default).
    /// Maintains the original schedule timestamps.
    Burst,
    /// Skip missed ticks and jump to the next future tick aligned
    /// with the original start time.
    Skip,
    /// Reschedule from now — the next tick fires one full period
    /// from the current time, discarding the original schedule.
    Delay,
}

/// Periodic timer that ticks at a fixed interval.
///
/// Created via [`crate::context::interval`]. Call `.tick().await` to
/// wait for the next tick.
pub struct Interval {
    period: Duration,
    start: Instant,
    next_deadline: Instant,
    sleep: Option<Sleep>,
    missed_tick_behavior: MissedTickBehavior,
}

impl Interval {
    pub(crate) fn new(period: Duration) -> Self {
        assert!(!period.is_zero(), "interval period must be non-zero");
        let now = Instant::now();
        Self {
            period,
            start: now,
            next_deadline: now + period,
            sleep: None,
            missed_tick_behavior: MissedTickBehavior::Burst,
        }
    }

    pub(crate) fn new_at(start: Instant, period: Duration) -> Self {
        assert!(!period.is_zero(), "interval period must be non-zero");
        Self {
            period,
            start,
            next_deadline: start,
            sleep: None,
            missed_tick_behavior: MissedTickBehavior::Burst,
        }
    }

    /// Wait for the next tick.
    pub async fn tick(&mut self) {
        if self.sleep.is_none() {
            self.sleep = Some(crate::context::sleep_until(self.next_deadline));
        }

        if let Some(ref mut sleep) = self.sleep {
            Pin::new(sleep).await;
        }

        let now = Instant::now();
        self.sleep = None;

        match self.missed_tick_behavior {
            MissedTickBehavior::Burst => {
                // Advance by one period. If behind, next tick fires immediately.
                self.next_deadline += self.period;
            }
            MissedTickBehavior::Skip => {
                // Jump to the next tick aligned with the original start.
                if now >= self.next_deadline {
                    let elapsed = now.duration_since(self.start);
                    let period_nanos = self.period.as_nanos();
                    let periods = elapsed.as_nanos() / period_nanos;
                    // Compute next deadline in nanos to avoid u32 truncation
                    // (Duration * u32 wraps after ~49 days at 1ms intervals).
                    let next_nanos = (periods + 1).saturating_mul(period_nanos);
                    let offset =
                        Duration::from_nanos(u64::try_from(next_nanos).unwrap_or(u64::MAX));
                    self.next_deadline = self.start + offset;
                } else {
                    self.next_deadline += self.period;
                }
            }
            MissedTickBehavior::Delay => {
                // Reschedule from now.
                self.next_deadline = now + self.period;
            }
        }
    }

    /// Reset the interval to fire one period from now.
    pub fn reset(&mut self) {
        self.next_deadline = Instant::now() + self.period;
        self.sleep = None;
    }

    /// Reset the interval to fire at a specific instant.
    pub fn reset_at(&mut self, deadline: Instant) {
        self.next_deadline = deadline;
        self.sleep = None;
    }

    /// Get the interval period.
    pub fn period(&self) -> Duration {
        self.period
    }

    /// Get the current missed tick behavior.
    pub fn missed_tick_behavior(&self) -> MissedTickBehavior {
        self.missed_tick_behavior
    }

    /// Set the missed tick behavior.
    pub fn set_missed_tick_behavior(&mut self, behavior: MissedTickBehavior) {
        self.missed_tick_behavior = behavior;
    }
}

// =============================================================================
// YieldNow — cooperative yield
// =============================================================================

/// Future that yields once, then completes.
///
/// Returns `Pending` on first poll, wakes itself, completes on second poll.
/// Other ready tasks get a turn before this task resumes.
///
/// # Caveat: cross-thread waits
///
/// `yield_now` is a *cooperative* yield within the executor. It does not
/// park the executor or yield CPU to other OS threads. On a single-threaded
/// runtime, a tight wait loop like
///
/// ```ignore
/// while !cross_thread_state_ready() {
///     yield_now().await;
/// }
/// ```
///
/// will busy-spin and starve other OS threads (a tokio worker thread, an
/// Aeron media driver, a separate sender thread) of CPU. The producer
/// can't fire its wake in time, the loop appears hung even though the
/// external work would have completed eventually.
///
/// For cross-thread waits, use a parking primitive instead:
/// - `await rx.recv()` on a channel — parks until the sender wakes
/// - `await notify.notified()` on a `Notify` — parks until `notify_one()`
/// - mix `yield_now` with periodic `sleep` — bounded park gives the OS
///   time to schedule producer threads
pub struct YieldNow(pub(crate) bool);

impl Future for YieldNow {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            Poll::Ready(())
        } else {
            self.0 = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::task::{RawWaker, RawWakerVTable};

    fn noop_waker() -> Waker {
        fn noop(_: *const ()) {}
        fn clone(p: *const ()) -> RawWaker {
            RawWaker::new(p, &VTABLE)
        }
        static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
        // SAFETY: all vtable fns are no-ops; null data is never deref'd.
        unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
    }

    #[test]
    fn timer_driver_fire_expired() {
        let mut driver = TimerDriver::new(64);
        let now = Instant::now();
        let waker = noop_waker();

        driver.schedule(
            now.checked_sub(Duration::from_millis(10)).unwrap(),
            waker.clone(),
        );
        driver.schedule(now + Duration::from_secs(100), waker);

        let fired = driver.fire_expired(now);
        assert_eq!(fired, 1);
        assert!(driver.next_deadline().unwrap() > now);
    }

    #[test]
    fn timer_driver_next_deadline() {
        let mut driver = TimerDriver::new(64);
        assert!(driver.next_deadline().is_none());

        let now = Instant::now();
        let soon = now + Duration::from_millis(10);
        let later = now + Duration::from_millis(100);
        let waker = noop_waker();

        driver.schedule(later, waker.clone());
        driver.schedule(soon, waker);

        let next = driver.next_deadline().unwrap();
        // Timer wheel has tick-resolution quantization, so check within 2ms.
        assert!(next <= soon + Duration::from_millis(2));
    }
}
