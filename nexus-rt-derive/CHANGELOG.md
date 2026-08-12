# Changelog

All notable changes to nexus-rt-derive are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Fixed

- `#[derive(Resource)]` on a **concrete** type no longer emits an explicit
  `where Self: Send + 'static` predicate. The `Resource: Send + 'static`
  supertrait already enforces the bound — and reports it cleanly at the derived
  type — but the explicit predicate additionally forced the `Send` auto-trait to
  be proven *eagerly*, which **overflowed** on legitimately self-referential
  resource types (e.g. a timer-wheel slot
  `struct Pending(Option<TemplatedCallback<K>>)`, the shape the self-rescheduling
  callback pattern uses). Such a type now derives `Resource`; a genuinely
  non-`Send` concrete type is still rejected at the derive.

  **Generic** types keep the conditional `where Self: Send + 'static` predicate,
  so `impl<T> Resource for Foo<T>` applies exactly when `Foo<T>: Send + 'static`
  (rather than requiring every instantiation to be `Send`). Behavior for generic
  types is unchanged.

## [1.2.0] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
