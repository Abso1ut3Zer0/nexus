//! Integration tests for `#[derive(Dispatchable)]` and the `Dispatchable` /
//! `VariantOf` traits.
//!
//! Run in the default (debug) profile so the `debug_assert!` inside the
//! generated `unwrap_unchecked` is active — every unwrap here targets the
//! matching variant, so the happy path must not trip it.

use nexus_rt::{Dispatchable, VariantOf};

// Mixed variant shapes: single unnamed field, multi-field tuple, and unit.
#[derive(Dispatchable)]
enum Cmd {
    RouteAway(u32),
    Reprice(u32, i64),
    Halt,
}

#[test]
fn variant_count_is_dense() {
    assert_eq!(Cmd::VARIANTS, 3);
}

#[test]
fn ordinal_follows_declaration_order() {
    assert_eq!(Cmd::RouteAway(7).ordinal(), 0);
    assert_eq!(Cmd::Reprice(1, -2).ordinal(), 1);
    assert_eq!(Cmd::Halt.ordinal(), 2);
}

#[test]
fn ordinal_constants_match_ordinal_method() {
    assert_eq!(cmd_variants::RouteAway::ORDINAL, 0);
    assert_eq!(cmd_variants::Reprice::ORDINAL, 1);
    assert_eq!(cmd_variants::Halt::ORDINAL, 2);
}

#[test]
fn unwrap_single_field_returns_payload() {
    // SAFETY: the value is the `RouteAway` variant.
    let payload = unsafe { cmd_variants::RouteAway::unwrap_unchecked(Cmd::RouteAway(7)) };
    assert_eq!(payload, 7u32);
}

#[test]
fn unwrap_tuple_field_returns_payload_tuple() {
    // SAFETY: the value is the `Reprice` variant.
    let payload = unsafe { cmd_variants::Reprice::unwrap_unchecked(Cmd::Reprice(3, -9)) };
    assert_eq!(payload, (3u32, -9i64));
}

#[test]
fn unit_variant_payload_is_unit() {
    // The `let ()` pattern type-checks only if `Halt`'s Payload is exactly
    // `()`, so this is a compile-time proof plus a happy-path unwrap.
    // SAFETY: the value is the `Halt` variant.
    let () = unsafe { cmd_variants::Halt::unwrap_unchecked(Cmd::Halt) };
}

// Explicit/sparse discriminants: `ordinal()` must normalize to a dense
// declaration-order index, which is the reason we derive it instead of
// using `as usize`.
#[derive(Dispatchable)]
enum Sparse {
    A = 5,
    B = 10,
    C = 100,
}

#[test]
fn ordinal_normalizes_sparse_discriminants() {
    assert_eq!(Sparse::VARIANTS, 3);
    assert_eq!(Sparse::A.ordinal(), 0);
    assert_eq!(Sparse::B.ordinal(), 1);
    assert_eq!(Sparse::C.ordinal(), 2);
}

// Multi-word enum name exercises the snake_case module-name conversion:
// `RouteDecision` → `route_decision_variants`.
#[derive(Dispatchable)]
enum RouteDecision {
    KeepLocal,
    SendAway(u8),
}

#[test]
fn snake_case_module_name_and_variant_markers() {
    assert_eq!(RouteDecision::VARIANTS, 2);
    assert_eq!(RouteDecision::KeepLocal.ordinal(), 0);
    assert_eq!(RouteDecision::SendAway(1).ordinal(), 1);
    assert_eq!(route_decision_variants::KeepLocal::ORDINAL, 0);
    assert_eq!(route_decision_variants::SendAway::ORDINAL, 1);
    // SAFETY: the value is the `SendAway` variant.
    let payload =
        unsafe { route_decision_variants::SendAway::unwrap_unchecked(RouteDecision::SendAway(42)) };
    assert_eq!(payload, 42u8);
}

// Single-variant enum exercises the `#[allow(unreachable_patterns)]` on the
// generated unwrap_unchecked's fallthrough arm (the `_` arm is unreachable when the
// enum has exactly one variant).
#[derive(Dispatchable)]
enum Solo {
    Only(u64),
}

#[test]
fn single_variant_enum() {
    assert_eq!(Solo::VARIANTS, 1);
    assert_eq!(Solo::Only(123).ordinal(), 0);
    // SAFETY: the value is the `Only` variant.
    let payload = unsafe { solo_variants::Only::unwrap_unchecked(Solo::Only(123)) };
    assert_eq!(payload, 123u64);
}
