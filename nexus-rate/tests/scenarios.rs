//! Integration tests: realistic rate limiting scenarios and edge cases.

use std::time::{Duration, Instant};

use nexus_rate::{ConfigError, local};

// =============================================================================
// Realistic scenarios
// =============================================================================

#[test]
fn binance_style_sliding_window() {
    let start = Instant::now();
    // 1200 requests per 60s, 10 sub-windows (6s each)
    // Using nanos = milliseconds * 1_000_000
    let mut sw = local::SlidingWindow::builder()
        .window(Duration::from_millis(60_000))
        .sub_windows(10)
        .limit(1200)
        .now(start)
        .build()
        .unwrap();

    // Steady rate just under limit: 1200 requests spread over 60s
    // = 20 per second = 1 per 50ms
    for i in 0..1200u64 {
        let now = start + Duration::from_millis(i * 50);
        assert!(
            sw.try_acquire(1, now),
            "request {i} at {}ms should be allowed",
            i * 50
        );
    }
    assert_eq!(sw.count(), 1200);

    // One more at the end of the window — should be rejected
    assert!(
        !sw.try_acquire(1, start + Duration::from_millis(59_999)),
        "should be at limit"
    );

    // After the window rolls, capacity frees up
    assert!(
        sw.try_acquire(1, start + Duration::from_millis(66_001)),
        "should be allowed after first sub-window expires"
    );
}

#[test]
fn multi_rate_composition() {
    let start = Instant::now();
    // Short-term: GCRA at 10 per 1000ns (burst 5)
    // Long-term: SlidingWindow at 100 per 60_000ns
    let mut gcra = local::Gcra::builder()
        .rate(10)
        .period(Duration::from_nanos(1000))
        .burst(5)
        .now(start)
        .build()
        .unwrap();

    let mut sw = local::SlidingWindow::builder()
        .window(Duration::from_nanos(60_000))
        .sub_windows(10)
        .limit(100)
        .now(start)
        .build()
        .unwrap();

    let mut total_allowed = 0u64;
    let mut total_rejected_gcra = 0u64;

    // Send at 1 request per 50ns for 10000ns
    // Check GCRA first (short-term), then SW (long-term)
    for i in 0..200u64 {
        let now = start + Duration::from_nanos(i * 50);
        let gcra_ok = gcra.try_acquire(1, now);
        if !gcra_ok {
            total_rejected_gcra += 1;
            continue;
        }
        if sw.try_acquire(1, now) {
            total_allowed += 1;
        }
    }

    // GCRA should have rejected some (rate = 10/1000ns, we send 20/1000ns)
    assert!(total_rejected_gcra > 0, "GCRA should reject some");
    // SW at 100/60000ns — allowed requests capped
    assert!(total_allowed <= 100, "SW should cap at 100");
}

#[test]
fn weighted_exchange_scenario() {
    let start = Instant::now();
    // Exchange rate limit: 50 weight per second, burst of 10 extra
    // emission_interval = 1000/50 = 20, tau = 20 * (10+1) = 220
    // Burst capacity = tau / emission_interval = 11 units of weight-1
    let mut gcra = local::Gcra::builder()
        .rate(50)
        .period(Duration::from_nanos(1000))
        .burst(10)
        .now(start)
        .build()
        .unwrap();

    // Send weighted requests: cancel=1, new=2, amend=3
    // TAT tracks: 0, 20, 60, 120, 160, 180 → all within tau=220
    let mut total_weight = 0u64;
    let ops = [
        (1u64, "cancel"),
        (2, "new"),
        (3, "amend"),
        (2, "new"),
        (1, "cancel"),
    ];
    for &(weight, _op) in &ops {
        assert!(gcra.try_acquire(weight, start));
        total_weight += weight;
    }
    assert_eq!(total_weight, 9); // TAT = 9 * 20 = 180

    // Next amend (weight 3): TAT = 180 + 60 = 240. Excess = 240, tau = 220. REJECTED.
    assert!(!gcra.try_acquire(3, start), "should exceed burst capacity");

    // But a lighter request (weight 1) fits: TAT = 180 + 20 = 200. Excess = 200 <= 220.
    assert!(gcra.try_acquire(1, start));
    // And another: TAT = 200 + 20 = 220. Excess = 220 <= 220. Exactly at limit.
    assert!(gcra.try_acquire(1, start));
    // One more: TAT = 220 + 20 = 240. Excess = 240 > 220. REJECTED.
    assert!(!gcra.try_acquire(1, start));
}

// =============================================================================
// Reconfigure validation
// =============================================================================

#[test]
fn gcra_reconfigure_zero_rate() {
    let mut g = local::Gcra::builder()
        .rate(10)
        .period(Duration::from_nanos(1000))
        .burst(0)
        .build()
        .unwrap();
    let result = g.reconfigure(0, Duration::from_nanos(1000), 0);
    assert!(matches!(result, Err(ConfigError::Invalid(_))));
}

#[test]
fn gcra_reconfigure_zero_period() {
    let mut g = local::Gcra::builder()
        .rate(10)
        .period(Duration::from_nanos(1000))
        .burst(0)
        .build()
        .unwrap();
    let result = g.reconfigure(10, Duration::ZERO, 0);
    assert!(matches!(result, Err(ConfigError::Invalid(_))));
}

#[test]
fn token_bucket_reconfigure_zero_rate() {
    let start = Instant::now();
    let mut tb = local::TokenBucket::builder()
        .rate(10)
        .period(Duration::from_nanos(1000))
        .burst(10)
        .now(start)
        .build()
        .unwrap();
    let result = tb.reconfigure(0, Duration::from_nanos(1000), 10);
    assert!(matches!(result, Err(ConfigError::Invalid(_))));
}

#[test]
fn sliding_window_reconfigure_zero_limit() {
    let start = Instant::now();
    let mut sw = local::SlidingWindow::builder()
        .window(Duration::from_nanos(1000))
        .sub_windows(10)
        .limit(100)
        .now(start)
        .build()
        .unwrap();
    let result = sw.reconfigure(0);
    assert!(matches!(result, Err(ConfigError::Invalid(_))));
}

#[test]
fn gcra_build_rate_exceeds_period() {
    // rate=1000, period=100ns → ceil(100/1000) = 1ns emission_interval.
    // This is valid: the limiter is conservative (1 token/ns vs configured
    // 10 tokens/ns) but functional. Ceiling division prevents over-issuance.
    let start = Instant::now();
    let mut g = local::Gcra::builder()
        .rate(1000)
        .period(Duration::from_nanos(100))
        .burst(5)
        .now(start)
        .build()
        .unwrap();

    // With emission_interval=1 and burst=5, tau=6.
    // First 6 requests should succeed (burst+1), then reject.
    for _ in 0..6 {
        assert!(g.try_acquire(1, start));
    }
    assert!(!g.try_acquire(1, start), "should reject after burst+1");
}

// =============================================================================
// Overflow defense
// =============================================================================

#[test]
fn gcra_huge_burst_saturates() {
    let start = Instant::now();
    let mut g = local::Gcra::builder()
        .rate(1)
        .period(Duration::from_nanos(1000))
        .burst(u64::MAX - 1)
        .now(start)
        .build()
        .unwrap();
    // tau should be saturated, not wrapped
    // The limiter should still work (just very permissive)
    assert!(g.try_acquire(1, start));
}

#[test]
fn token_bucket_large_timestamp() {
    let start = Instant::now();
    let mut tb = local::TokenBucket::builder()
        .rate(10)
        .period(Duration::from_nanos(1000))
        .burst(100)
        .now(start)
        .build()
        .unwrap();

    // Advance by 1000 nanos — should produce 10 tokens
    let now = start + Duration::from_nanos(1000);
    assert!(tb.try_acquire(10, now));
    // Shouldn't wrap or panic
    assert!(!tb.try_acquire(1, now));
}

#[test]
// Debug builds guard oversized cost with a `debug_assert!`; this validates the
// release-mode safety-net (huge cost is rejected, not wrapped).
#[cfg(not(debug_assertions))]
fn sliding_window_huge_cost_rejected() {
    let start = Instant::now();
    let mut sw = local::SlidingWindow::builder()
        .window(Duration::from_nanos(1000))
        .sub_windows(10)
        .limit(100)
        .now(start)
        .build()
        .unwrap();

    // cost = u64::MAX should be rejected, not wrapped to allow
    assert!(
        !sw.try_acquire(u64::MAX, start),
        "huge cost should be rejected"
    );
    assert_eq!(sw.count(), 0, "nothing should have been recorded");
}

#[test]
fn token_bucket_consume_advances_zero_time() {
    let start = Instant::now();
    // Verify that consuming always advances zero_time by at least 1
    // even with unfavorable rate/period ratios.
    //
    // nanos_per_token = 10 / 3 = 3 (truncated). This means available tokens
    // are computed as elapsed / 3, and consuming 1 token advances zero_time
    // by 3 nanos. The truncation error is <1 nanosecond per token —
    // negligible for rate limiting.
    let mut tb = local::TokenBucket::builder()
        .rate(3)
        .period(Duration::from_nanos(10))
        .burst(100)
        .now(start)
        .build()
        .unwrap();

    // nanos_per_token = ceil(10/3) = 4. At time 100ns: available = 100/4 = 25.
    // This is conservative (30 would be exact for 3 tokens/10ns over 10 periods).
    // Ceiling division guarantees we never exceed the configured rate.
    let available_before = tb.available(start + Duration::from_nanos(100));
    assert_eq!(available_before, 25);
    assert!(tb.try_acquire(1, start + Duration::from_nanos(100)));
    // After consuming 1: zero_time = 4, available = (100 - 4) / 4 = 24
    let available_after = tb.available(start + Duration::from_nanos(100));
    assert_eq!(available_after, 24);
}

// =============================================================================
// No-over-issuance guarantee
// =============================================================================

/// Verifies that ceiling division prevents the token bucket from ever issuing
/// more than `rate` tokens per `period`, regardless of configuration.
#[test]
fn token_bucket_never_over_issues() {
    let start = Instant::now();

    // Pathological config: rate=3, period=7ns. Floor would give nanos_per_token=2,
    // producing 7/2=3.5 → 3 tokens/period (accidentally ok). But rate=3, period=5ns
    // with floor gives nanos_per_token=1, producing 5 tokens/period (over-issue!).
    // Ceiling: ceil(5/3)=2, producing 5/2=2 tokens/period (conservative, safe).
    let tb = local::TokenBucket::builder()
        .rate(3)
        .period(Duration::from_nanos(5))
        .burst(100)
        .now(start)
        .build()
        .unwrap();

    // After exactly one period (5ns), available must be <= rate (3)
    let available = tb.available(start + Duration::from_nanos(5));
    assert!(
        available <= 3,
        "must never exceed configured rate: got {available}, max 3"
    );

    // After 10 periods (50ns), available must be <= 10 * rate = 30
    let available_10 = tb.available(start + Duration::from_nanos(50));
    assert!(
        available_10 <= 30,
        "must never exceed rate*periods: got {available_10}, max 30"
    );
}

/// Same guarantee for GCRA: never allows more than rate requests per period.
#[test]
fn gcra_never_over_issues() {
    let start = Instant::now();

    // rate=3, period=5ns. ceil(5/3)=2 emission_interval.
    // tau = 2 * (burst+1) = 2 * 4 = 8 for burst=3.
    let mut g = local::Gcra::builder()
        .rate(3)
        .period(Duration::from_nanos(5))
        .burst(3)
        .now(start)
        .build()
        .unwrap();

    // Count how many requests succeed in exactly one period (5ns)
    let mut accepted = 0;
    for _ in 0..100 {
        if g.try_acquire(1, start + Duration::from_nanos(5)) {
            accepted += 1;
        } else {
            break;
        }
    }
    // Must not exceed rate (3). With burst, initial burst allows more,
    // but steady-state should not exceed rate per period.
    // At t=5ns, TAT starts at 0. First request: new_tat = max(0,5)+2=7.
    // excess = 7-5=2 <= tau(8). OK. Second: new_tat=7+2=9. excess=9-5=4 <= 8. OK.
    // Third: new_tat=9+2=11. excess=11-5=6 <= 8. OK.
    // Fourth: new_tat=11+2=13. excess=13-5=8 <= 8. OK (burst allows this).
    // Fifth: new_tat=13+2=15. excess=15-5=10 > 8. REJECTED.
    assert_eq!(accepted, 4, "burst+1 requests allowed, then reject");
    assert!(
        accepted <= 3 + 3, // rate + burst
        "total accepted must not exceed rate + burst: got {accepted}"
    );
}

/// Sliding window uses direct counting — no division-based token computation.
/// Verify it enforces the limit exactly (no over-issuance by construction).
#[test]
fn sliding_window_exact_limit() {
    let start = Instant::now();
    let mut sw = local::SlidingWindow::builder()
        .window(Duration::from_nanos(100))
        .sub_windows(10)
        .limit(5)
        .now(start)
        .build()
        .unwrap();

    // Exactly 5 should succeed, 6th should fail
    for i in 0..5 {
        assert!(sw.try_acquire(1, start), "request {i} should succeed");
    }
    assert!(
        !sw.try_acquire(1, start),
        "must reject at limit — sliding window enforces exact count"
    );
}
