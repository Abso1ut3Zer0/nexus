# Nexus Workspace Documentation

Top-level guide to the Nexus workspace. Per-crate docs live in each
crate's `docs/` directory — these docs explain how to **combine**
crates to build real systems.

If you're new here, start with [onboarding.md](./onboarding.md).

---

## Onboarding

- [**onboarding.md**](./onboarding.md) — 20-minute tour of the workspace.
  Philosophy, crate map, "if you need X look in Y" decision tree, how
  to run tests, where architectural decisions live.

## Cookbooks

End-to-end recipes combining multiple crates to solve real trading
infrastructure problems. Each is self-contained with imports and
gotchas called out.

- [**cookbook-market-data-gateway.md**](./cookbook-market-data-gateway.md) —
  WebSocket feed → parse → archive → fan out → monitor. Combines
  `nexus-async-web`, `nexus-async-rt`, `nexus-queue`, `nexus-slot`,
  `nexus-logbuf`, `nexus-stats`.

- [**cookbook-strategy-handler.md**](./cookbook-strategy-handler.md) —
  Writing a trading strategy on `nexus-rt`. Resources, handlers,
  streaming stats, fixed-point prices, testing. Combines `nexus-rt`,
  `nexus-stats`, `nexus-decimal`, `nexus-collections`.

- [**cookbook-latency-monitoring.md**](./cookbook-latency-monitoring.md) —
  Measuring, alerting, and diagnosing latency in a live system.
  Combines `nexus-stats`, `nexus-rt`, `nexus-logbuf`.

- [**cookbook-exchange-connection.md**](./cookbook-exchange-connection.md) —
  End-to-end exchange connectivity: TLS, reconnect, rate limiting,
  order IDs, archival. Combines `nexus-async-web`, `nexus-async-rt`,
  `nexus-rate`, `nexus-id`, `nexus-logbuf`.

## Benchmarking

- [**benchmarking.md**](./benchmarking.md) — Methodology, controlled
  conditions (turbo off, core pinning), criterion vs cycle examples,
  reading p50/p99/p999/p9999, A/B comparison, common pitfalls.
  **Read this before running your first benchmark.**

## Per-crate documentation

Each crate owns its own deep-dive docs. When you need the internals of
a specific primitive, go there — not here.

| Crate | Location |
|-------|----------|
| `nexus-queue` | `nexus-queue/docs/` and `README.md` |
| `nexus-channel` | `nexus-channel/docs/` and `README.md` |
| `nexus-slot` | `nexus-slot/docs/` |
| `nexus-logbuf` | `nexus-logbuf/docs/` |
| `nexus-notify` | `nexus-notify/docs/` |
| `nexus-slab` | `nexus-slab/docs/` |
| `nexus-pool` | `nexus-pool/docs/` |
| `nexus-collections` | `nexus-collections/docs/` |
| `nexus-bits` / `nexus-bits-derive` | `nexus-bits/docs/` |
| `nexus-id` | `nexus-id/docs/` |
| `nexus-ascii` | `nexus-ascii/docs/` |
| `nexus-stats` | `nexus-stats/docs/` (cycle counts: `nexus-stats/docs/reference/performance.md`) |
| `nexus-rate` | `nexus-rate/docs/` |
| `nexus-decimal` | `nexus-decimal/docs/` |
| `nexus-net` | `nexus-net/docs/` |
| `nexus-web` | `nexus-web/docs/` |
| `nexus-async-web` | `nexus-async-web/docs/` |
| `nexus-rt` | `nexus-rt/docs/` (extensive — start with `INDEX.md`) |
| `nexus-async-rt` | `nexus-async-rt/docs/`, `nexus-async-rt/BENCHMARKS.md` |
| `nexus-timer` | `nexus-timer/docs/` |
| `nexus-inference` | `nexus-inference/docs/` (start with `INDEX.md`) |
| `nexus-smartptr` | `nexus-smartptr/docs/` |

Rustdoc: `cargo doc --workspace --no-deps --open`.

## Design documents

Pre-implementation architecture planning for upcoming crates.
Open questions are presented with both paths so tradeoffs can
be discussed before code is written.

- [`design/README.md`](design/README.md) — Index
- [`design/nexus-shm.md`](design/nexus-shm.md) — Shared memory
  primitives (mmap foundation, ring buffers, journal, slot, map)
- [`design/nexus-fix.md`](design/nexus-fix.md) — FIX protocol
  codec generation and session engine

## Architecture decisions

- [`../README.md`](../README.md) — Public-facing crate table and
  workspace overview.
- [`../CONTRIBUTING.md`](../CONTRIBUTING.md) — Design philosophy and the
  benchmarking standards a change is reviewed against.
- The [issue tracker](https://github.com/Abso1ut3Zer0/nexus/issues) is the
  roadmap: open issues carry the design discussion for future work.
- `nexus-rt/docs/ARCHITECTURE.md` — Runtime layer design.
- `nexus-async-rt/docs/` — Async executor architecture.

Per-crate `ARCHITECTURE.md` files capture the "why" for each crate —
read them before proposing structural changes.
