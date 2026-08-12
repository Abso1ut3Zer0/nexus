# nexus-timer documentation

Hierarchical, rebalancing timer wheel with O(1) insert and cancel: entries
rebalance down to finer levels as they near their deadline, so `poll` collects
ready timers from small, exact slots.

## Contents

- [overview.md](overview.md) — when a timer wheel is the right tool, and why
  the collect / rebalance design matters
- [wheel.md](wheel.md) — `Wheel`, `BoundedWheel`, `WheelBuilder`, scheduling
  and cancellation
- [bounded-vs-unbounded.md](bounded-vs-unbounded.md) — the two storage
  backends and their tradeoffs
- [patterns.md](patterns.md) — cookbook: timeouts, heartbeats, periodic
  tasks, deadline scheduling
- [perf-walk-locality.md](perf-walk-locality.md) — cache/locality audit (#669):
  the poll walk is compute-bound and cache-resident at realistic sizes; when
  slab fragmentation actually bites (> L3 working set), and why free-list
  ordering is the wrong fix

## Related crates

- [`nexus-slab`](../../nexus-slab) — the underlying slab allocator
- [`nexus-collections`](../../nexus-collections) — includes a simpler
  binary heap if you just need one priority queue
- [`nexus-rt`](../../nexus-rt) — the runtime layer that typically *owns*
  the wheel and exposes it as a resource
