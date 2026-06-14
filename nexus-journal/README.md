# nexus-journal

Append-only and bounded-rotation mmap'd journals for trading systems.

## Overview

`nexus-journal` provides two durable, memory-mapped logs for moving records to
disk without syscalls, allocation, or formatting on the hot path:

- **`AppendOnlyJournal`** — a linear, never-evicting log. Full history, simple
  recovery. Segment rolls happen *inline*.
- **`RotatingJournal`** — a bounded log with a background **Conductor** that
  keeps the `mmap`/file-create work *off* the hot path. The hot-path append is a
  pointer swap; old segments rotate out (and can be archived).

Both are single-process, single-writer. They build directly on
[`nexus-platform`](../nexus-platform)'s `Mapping` — no shared-memory control
block, no atomics, no cross-process liveness. (For the cross-process variants,
see [`nexus-shm`](../nexus-shm).)

## Which one?

| | `AppendOnlyJournal` | `RotatingJournal` |
|---|---|---|
| Retention | Unbounded — keeps everything | Bounded live window (+ optional archive) |
| Segment roll | **Inline** — `mmap` on the writing thread | **Off-thread** — Conductor maps ahead; append is a pointer swap |
| Hot-path cost | Low, with a ~millisecond tail when a segment rolls | Low and flat; rolls don't stall the writer |
| Random read | By sequence range over the whole log | `read(offset)` over the live window; `None` once rotated out |
| Backpressure | — | `WriteError::StandbyNotReady` if the writer outruns the Conductor |
| Best for | Audit logs, event sourcing, full replay history | Latency-sensitive journaling where roll jitter is unacceptable |

Rule of thumb: reach for `RotatingJournal` when a millisecond stall on segment
roll would hurt (e.g. order-entry journaling on the send path), and
`AppendOnlyJournal` when you need the entire history and can tolerate the
inline roll.

## AppendOnlyJournal

A linear log of typed records. The header type implements `RecordHeader` (or
`SeqHeader` for sequence-keyed reads); `FixHeader` is provided. Writes use a
claim API — reserve space, write in place, commit:

```rust
use nexus_journal::{AppendOnlyJournal, AppendOnlyJournalConfig, FixHeader, MapHints};

let cfg = AppendOnlyJournalConfig { segment_size: 64 << 20, hints: MapHints::default() };
let (mut writer, mut reader) = AppendOnlyJournal::<FixHeader>::open("/var/journal/orders", cfg)?;

// Claim space, write the payload directly into the mapping, commit.
let mut claim = writer.try_claim(FixHeader { seq: 1, timestamp: 0 }, msg.len())?;
claim.as_mut_slice().copy_from_slice(msg);
claim.commit();

// Read back by sequence range (or `reader.next_record()` to stream).
for rec in reader.read_range(1..=100)? {
    handle(rec.header(), rec.payload());
}
```

Segment rolls allocate and `mmap` a new file on the writing thread, so a roll
costs a one-off ~millisecond tail on that append. If that tail matters, use
`RotatingJournal`.

## RotatingJournal + Conductor

The hot path never touches `mmap`. A `Conductor` background thread provisions
(and recycles) segments ahead of time; `append` swaps to the next ready segment
with a pointer exchange and writes the payload. Opening a `Conductor` spawns the
thread; each `session()` is one journal under that conductor's directory.

```rust
use nexus_journal::Conductor;

let mut conductor = Conductor::open("/var/journal")?;   // spawns the background thread
let mut journal = conductor
    .session()
    .segment_size(4 << 20)
    .pretouch(true)                                     // fault pages on the Conductor, not the writer
    .open()?;

// Hot path: pointer-swap append. Returns the offset for later random reads.
let offset = journal.append(payload)?;                 // Err(WriteError::StandbyNotReady) under backpressure

// Random read; `None` once the offset has rotated out of the live window.
if let Some(frame) = journal.read(offset) {
    handle(frame.payload());
}
```

**Backpressure.** If the writer fills segments faster than the Conductor can
provision replacements, `append` returns `WriteError::StandbyNotReady` rather
than blocking or allocating — the caller decides whether to retry, drop, or slow
down. Tune the lookahead with `ConductorBuilder::clean_queue_depth`.

**Recovery & replay.** `read_start()` + `read_next(&mut pos)` stream the live
window in order; `read(offset)` seeks a specific `LogOffset` and returns `None`
once it has rotated out. The live window *is* the replay horizon — anything
older is gone (or archived), which bounds both memory and recovery cost. On
restart, an existing session under the directory is reopened and its write
position recovered.

**Archival.** With `ConductorBuilder::archive(true)`, evicted segments are
fsync'd and renamed into an archive directory before the slot is recycled —
preserving the exact on-disk frame format with no copy step. This gives you a
full durable trail for audit while keeping the live window (and replay) bounded.

## Examples & benchmarks

```bash
# Paced and unpaced latency distributions (HDR histograms):
cargo run -p nexus-journal --release --example rotating_latency
cargo run -p nexus-journal --release --example append_latency
cargo run -p nexus-journal --release --example rotating_stress
cargo run -p nexus-journal --release --example rotating_tail
cargo run -p nexus-journal --release --example mmap_fill_probe

# Criterion throughput bench:
cargo bench -p nexus-journal --bench append
```

The latency examples print p50/p90/p99/p999/max so you can see the difference
between the inline roll (`append_latency`) and the off-thread rotation
(`rotating_latency`) on your own hardware. Measure on the real target disk and
calibrate the TSC for accurate numbers.

## Platform

Unix (relies on `mmap` and OFD semantics via `nexus-platform`). Linux is the
primary target.
