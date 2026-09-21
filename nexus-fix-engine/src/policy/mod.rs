//! Policy primitives for FIX session management.
//!
//! This module provides curated, sans-IO, opt-in policy types that compose
//! with the mechanism in [`crate::FixSession`]. The session holds no policy;
//! these types let you bolt on the common behaviors with confidence.
//!
//! ## Variant roadmap
//!
//! Variants are separate structs sharing the [`LivenessAction`] return type so
//! call sites can switch variants without changing the match arm signatures.
//! Shipping order (most-common first):
//!
//! 1. [`PeerLiveness`] (this release): two-phase probe. Inbound silence past
//!    `HBI + grace` triggers a `TestRequest`; no reply before `probe_timeout`
//!    means the peer is gone. The FIX-spec-prescribed behavior, hand-rolled in
//!    `timer_recipes.rs` before this release.
//!
//! 2. `IdleTimeout` (planned): single-phase. Always-chatter feeds where any
//!    silence is immediately fatal. No probe phase.
//!
//! 3. `EchoMatchLiveness` (planned): strict echo match. Only a Heartbeat
//!    carrying our `TestReqID` resets liveness. Gets its own struct and its
//!    own record method that can carry the echoed `TestReqID`; this variant
//!    does not change [`PeerLiveness::record_inbound`] when it lands.
//!
//! ## Wiring PeerLiveness into a session loop
//!
//! On each loop wakeup, call [`PeerLiveness::poll`] with the current time:
//!
//! - [`LivenessAction::Probe`]: send a `TestRequest`. It is an outbound send,
//!   so record it against your heartbeat timer at the call site.
//!   [`PeerLiveness`] will not emit `Probe` again until the episode resolves.
//! - [`LivenessAction::Dead`]: tear the session down. Disconnect, drop
//!   `PeerLiveness`, and do not call `poll` again.
//! - [`LivenessAction::Live`]: nothing to do.
//!
//! Use [`PeerLiveness::next_deadline`] as the sleep bound for a `select` loop.
//! When it returns `None` the session is dead or disabled; do not sleep on it.
//!
//! There is no `reset` method. Drop and recreate `PeerLiveness` on each
//! new connection. The type is cheap to construct and intentionally stateless
//! across sessions.

use std::time::{Duration, Instant};

/// The action [`PeerLiveness::poll`] asks the caller to take.
///
/// Shared by all liveness variants so call sites can switch variants without
/// changing the match arm signatures.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LivenessAction {
    /// The peer is within its liveness window. Nothing to do.
    Live,
    /// Inbound silence exceeded `HBI + grace`. Send a `TestRequest`.
    ///
    /// It is an outbound send, so record it against your heartbeat timer at
    /// the call site. [`PeerLiveness`] will not emit `Probe` again until the
    /// episode resolves.
    Probe,
    /// The probe went unanswered. Disconnect and drop this type.
    ///
    /// Subsequent calls to `poll` also return `Dead`, but the contract is to
    /// disconnect and drop the type on the first `Dead`.
    Dead,
}

#[derive(Debug, Clone, Copy)]
enum Phase {
    Healthy,
    Probed { deadline: Instant },
    Dead,
    Disabled,
}

/// Two-phase peer-liveness probe (timer 2 from the FIX timer recipes).
///
/// Tracks inbound silence on the local monotonic clock. When silence exceeds
/// `HBI + grace`, [`poll`](Self::poll) returns [`LivenessAction::Probe`] once
/// and arms a shorter countdown. If no inbound arrives before that deadline,
/// [`poll`](Self::poll) returns [`LivenessAction::Dead`].
///
/// Any inbound message at any phase (except `Dead`) resets the type to
/// `Healthy`. No `TestReqID` matching: any inbound traffic is proof enough;
/// `record_inbound` takes no ID.
///
/// # Sans-IO contract
///
/// `PeerLiveness` reads no clock and does no I/O. The caller passes `now` to
/// every method and owns the probe send and the disconnect.
///
/// # One probe per episode
///
/// [`poll`](Self::poll) returns [`LivenessAction::Probe`] exactly once per
/// silence episode. Subsequent calls while waiting for the peer to answer
/// return [`LivenessAction::Live`], not a stream of probes.
///
/// # Disabled mode (HeartBtInt = 0)
///
/// A `PeerLiveness` built with `hbi == Duration::ZERO` is permanently
/// disabled. [`poll`](Self::poll) always returns [`LivenessAction::Live`] and
/// [`next_deadline`](Self::next_deadline) always returns `None`. This matches
/// the FIX convention that `HeartBtInt=0` means heartbeats are disabled: there
/// is nothing to monitor. [`record_inbound`](Self::record_inbound) is safe to
/// call and has no effect in this mode.
///
/// # No reset
///
/// There is no `reset` method. Drop and recreate `PeerLiveness` on each new
/// connection.
#[derive(Debug)]
pub struct PeerLiveness {
    hbi: Duration,
    grace: Duration,
    probe_timeout: Duration,
    last_inbound: Instant,
    phase: Phase,
}

impl PeerLiveness {
    /// Build from the negotiated HBI. `grace` and `probe_timeout` default to
    /// `hbi / 2`. `now` seeds the inbound clock so no probe fires spuriously
    /// on the first wakeup.
    ///
    /// If `hbi` is zero the instance is permanently disabled: `poll` always
    /// returns `Live` and `next_deadline` always returns `None`. See the
    /// [type-level docs](Self#disabled-mode-heartbtint--0).
    pub fn new(hbi: Duration, now: Instant) -> Self {
        Self::new_with(hbi, hbi / 2, hbi / 2, now)
    }

    /// Build with explicit grace and probe-timeout values.
    ///
    /// Use this for venues with tighter or looser liveness windows. If `hbi`
    /// is zero the instance is permanently disabled regardless of `grace` and
    /// `probe_timeout`.
    pub fn new_with(hbi: Duration, grace: Duration, probe_timeout: Duration, now: Instant) -> Self {
        let phase = if hbi.is_zero() {
            Phase::Disabled
        } else {
            Phase::Healthy
        };
        Self {
            hbi,
            grace,
            probe_timeout,
            last_inbound: now,
            phase,
        }
    }

    /// Record that an inbound message arrived.
    ///
    /// Resets liveness to `Healthy` regardless of phase, unless the type is
    /// already `Dead`. Call for every inbound result that is not `Ok(None)`.
    /// Do not call on a bare timeout wakeup.
    pub fn record_inbound(&mut self, now: Instant) {
        if !matches!(self.phase, Phase::Dead | Phase::Disabled) {
            self.last_inbound = now;
            self.phase = Phase::Healthy;
        }
    }

    /// Evaluate liveness and return the action to take.
    ///
    /// Call on every loop wakeup (message or timeout). When `Dead` is
    /// returned, disconnect and drop this type.
    ///
    /// [`LivenessAction::Probe`] is returned at most once per silence episode.
    /// Repeated calls while waiting for the peer to answer return
    /// [`LivenessAction::Live`].
    pub fn poll(&mut self, now: Instant) -> LivenessAction {
        match self.phase {
            Phase::Disabled => LivenessAction::Live,
            Phase::Dead => LivenessAction::Dead,
            Phase::Probed { deadline } => {
                if now >= deadline {
                    self.phase = Phase::Dead;
                    LivenessAction::Dead
                } else {
                    LivenessAction::Live
                }
            }
            Phase::Healthy => {
                if now >= self.last_inbound + self.hbi + self.grace {
                    self.phase = Phase::Probed {
                        deadline: now + self.probe_timeout,
                    };
                    LivenessAction::Probe
                } else {
                    LivenessAction::Live
                }
            }
        }
    }

    /// The monotonic timestamp at which [`poll`](Self::poll) will next change state.
    ///
    /// - `Healthy`: `last_inbound + hbi + grace`.
    /// - `Probed`: probe deadline.
    /// - `Dead` or `Disabled`: `None`. There is no next event; the caller
    ///   should already have disconnected and dropped this type.
    pub fn next_deadline(&self) -> Option<Instant> {
        match self.phase {
            Phase::Healthy => Some(self.last_inbound + self.hbi + self.grace),
            Phase::Probed { deadline } => Some(deadline),
            Phase::Dead | Phase::Disabled => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Duration, Instant};

    // 1. Probe emits exactly once per silence episode.
    #[test]
    fn probe_fires_once_per_episode() {
        let now = Instant::now();
        let hbi = Duration::from_secs(10);
        let mut p = PeerLiveness::new(hbi, now);

        // Before threshold: Live.
        assert_eq!(p.poll(now + hbi), LivenessAction::Live);

        // At threshold: exactly one Probe.
        let threshold = now + hbi + hbi / 2;
        assert_eq!(p.poll(threshold), LivenessAction::Probe);

        // Repeated polls before deadline: Live, not Probe.
        assert_eq!(
            p.poll(threshold + Duration::from_millis(100)),
            LivenessAction::Live
        );
        assert_eq!(
            p.poll(threshold + Duration::from_millis(200)),
            LivenessAction::Live
        );
        assert_eq!(
            p.poll(threshold + Duration::from_millis(300)),
            LivenessAction::Live
        );
    }

    // 2. After a Probe, any inbound resets to Healthy; next episode produces
    //    exactly one new Probe.
    #[test]
    fn inbound_after_probe_resets_and_next_episode_probes_once() {
        let now = Instant::now();
        let hbi = Duration::from_secs(10);
        let mut p = PeerLiveness::new(hbi, now);

        // Trigger first probe.
        let threshold = now + hbi + hbi / 2;
        assert_eq!(p.poll(threshold), LivenessAction::Probe);

        // Inbound while Probed: back to Healthy.
        let inbound_at = threshold + Duration::from_millis(100);
        p.record_inbound(inbound_at);
        assert_eq!(
            p.poll(inbound_at + Duration::from_millis(1)),
            LivenessAction::Live
        );

        // Second episode: exactly one Probe.
        let second = inbound_at + hbi + hbi / 2;
        assert_eq!(p.poll(second), LivenessAction::Probe);
        assert_eq!(
            p.poll(second + Duration::from_millis(100)),
            LivenessAction::Live
        );
    }

    // 3. Probed past deadline -> Dead. poll after Dead keeps Dead.
    //    next_deadline after Dead is None.
    #[test]
    fn probed_past_deadline_becomes_dead() {
        let now = Instant::now();
        let hbi = Duration::from_secs(10);
        let mut p = PeerLiveness::new(hbi, now);

        // Trigger probe.
        let threshold = now + hbi + hbi / 2;
        assert_eq!(p.poll(threshold), LivenessAction::Probe);

        // Past probe deadline: Dead.
        let past = threshold + hbi / 2 + Duration::from_millis(1);
        assert_eq!(p.poll(past), LivenessAction::Dead);

        // Subsequent polls also Dead.
        assert_eq!(p.poll(past + Duration::from_secs(1)), LivenessAction::Dead);
        assert_eq!(p.poll(past + Duration::from_secs(2)), LivenessAction::Dead);

        // next_deadline is None.
        assert_eq!(p.next_deadline(), None);
    }

    // 4. next_deadline in Healthy and Probed equals the documented formula.
    #[test]
    fn next_deadline_formula() {
        let now = Instant::now();
        let hbi = Duration::from_secs(10);
        let grace = Duration::from_secs(3);
        let probe_timeout = Duration::from_secs(4);
        let mut p = PeerLiveness::new_with(hbi, grace, probe_timeout, now);

        // Healthy: last_inbound + hbi + grace.
        assert_eq!(p.next_deadline(), Some(now + hbi + grace));

        // Record inbound at t=5; new Healthy deadline.
        let t5 = now + Duration::from_secs(5);
        p.record_inbound(t5);
        assert_eq!(p.next_deadline(), Some(t5 + hbi + grace));

        // Trigger probe; Probed deadline = threshold + probe_timeout.
        let threshold = t5 + hbi + grace;
        assert_eq!(p.poll(threshold), LivenessAction::Probe);
        assert_eq!(p.next_deadline(), Some(threshold + probe_timeout));
    }

    // 5. new uses hbi/2 for both; new_with honours explicit values.
    #[test]
    fn constructors_set_defaults_and_explicit() {
        let now = Instant::now();
        let hbi = Duration::from_secs(10);

        // Default: threshold = now + hbi + hbi/2.
        let mut p = PeerLiveness::new(hbi, now);
        assert_eq!(p.next_deadline(), Some(now + hbi + hbi / 2));

        // Trigger probe; probe deadline = threshold + hbi/2.
        let threshold = now + hbi + hbi / 2;
        assert_eq!(p.poll(threshold), LivenessAction::Probe);
        assert_eq!(p.next_deadline(), Some(threshold + hbi / 2));

        // new_with with explicit values.
        let grace = Duration::from_secs(1);
        let probe_timeout = Duration::from_secs(2);
        let p2 = PeerLiveness::new_with(hbi, grace, probe_timeout, now);
        assert_eq!(p2.next_deadline(), Some(now + hbi + grace));
    }

    // 6. No probe before hbi + grace of silence (boundary on both sides).
    #[test]
    fn no_probe_before_threshold() {
        let now = Instant::now();
        let hbi = Duration::from_secs(10);
        let grace = hbi / 2;
        let mut p = PeerLiveness::new(hbi, now);

        // One nanosecond before threshold: Live.
        let just_before = (now + hbi + grace)
            .checked_sub(Duration::from_nanos(1))
            .unwrap();
        assert_eq!(p.poll(just_before), LivenessAction::Live);

        // At threshold: Probe.
        assert_eq!(p.poll(now + hbi + grace), LivenessAction::Probe);
    }

    // 7. Zero-hbi: always Live, next_deadline always None.
    #[test]
    fn zero_hbi_never_probes() {
        let now = Instant::now();
        let mut p = PeerLiveness::new(Duration::ZERO, now);

        assert_eq!(p.next_deadline(), None);

        // Far past any deadline that would matter for non-zero hbi.
        for offset_secs in [0u64, 1, 10, 100, 3600] {
            assert_eq!(
                p.poll(now + Duration::from_secs(offset_secs)),
                LivenessAction::Live
            );
            assert_eq!(p.next_deadline(), None);
        }
    }

    // 8. Zero-hbi: record_inbound is a no-op and does not change the disabled state.
    #[test]
    fn zero_hbi_record_inbound_is_noop() {
        let now = Instant::now();
        let mut p = PeerLiveness::new(Duration::ZERO, now);

        p.record_inbound(now + Duration::from_secs(1));
        assert_eq!(p.next_deadline(), None);
        assert_eq!(p.poll(now + Duration::from_secs(100)), LivenessAction::Live);
    }

    // 9. Non-zero hbi still behaves correctly after the zero-hbi path is added.
    #[test]
    fn nonzero_hbi_unaffected() {
        let now = Instant::now();
        let hbi = Duration::from_secs(30);
        let mut p = PeerLiveness::new(hbi, now);

        assert_eq!(p.poll(now + hbi), LivenessAction::Live);
        assert_eq!(p.poll(now + hbi + hbi / 2), LivenessAction::Probe);
        assert_eq!(
            p.poll(now + hbi + hbi / 2 + hbi / 2 + Duration::from_millis(1)),
            LivenessAction::Dead
        );
    }
}
