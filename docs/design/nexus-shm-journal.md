# nexus-shm: ShmJournal — design notes (#391)

Append-only durable log over mmap'd segments. Builds on the #390 foundation
(`Segment`, `Mapping`, `Pod`, two-tier liveness). Primary caller: FIX message
journaling for resend (#411). Aeron Archive model.

Most of the design is already resolved in `nexus-shm.md` (commit ordering,
checksum policy, liveness tier). This pins the one open question — sequence
awareness — and specifies the record/commit/recovery/segment layout.

---

## Resolved already (from nexus-shm.md, for reference)

- **Commit ordering** is the correctness property: write body → release fence →
  publish commit marker. Recovery scans forward, stops at first uncommitted
  record. (Aeron sentinel + PAD frame model.)
- **Checksums** off by default; opt-in flag for the file-backed durability
  domain (torn page writeback, bit rot). The commit marker alone covers the
  crash case fully.
- **Liveness:** in-process journal (FIX same-process read+write) needs only
  Tier-1 atomic. Cross-process read-only attach uses Tier-2 OFD opt-in.
- **Segmented layout**, default 64 MB segment size.

---

## Open question resolved: sequence awareness → Path C (pluggable header)

`ShmJournal<H: RecordHeader>`. The journal frames `[frame_len][H][payload]` and
reads/writes `H` but never interprets it.

- FIX (#411) uses `H = FixHeader { seq: u64, timestamp: u64 }` and gets
  `read_range` by sequence.
- Non-FIX callers use `H = ()` — zero per-record overhead, position-only
  semantics identical to Path A.

Rationale: Path A forces a separate seq→position indexer for FIX resend (the
doc's own con); Path B bakes FIX semantics (seq+ts) into every record including
non-FIX callers. Path C is general without the waste — the header is the
caller's, the framing and recovery are ours.

`RecordHeader` is `Pod` (reuses the #390 trait) + a const size; `()` qualifies
trivially. No heap, fixed layout, valid for recovery scanning.

---

## Record layout

Each record, 8-byte aligned:

```
┌────────────┬──────────────┬───────────────┬─────────────┐
│ frame_len  │  header H    │   payload     │  padding    │
│  i32 (LE)  │  size_of::<H>│   len bytes   │  to 8-byte  │
└────────────┴──────────────┴───────────────┴─────────────┘
     ^committed marker
```

- `frame_len` is the **commit marker** (the sentinel field). Aligned `i32`,
  written **last**, behind a release fence.
  - `0` — uncommitted / end of log. Recovery stops here.
  - `> 0` — committed; value is the total frame size (header + payload +
    padding, excluding the length word itself). Reader advances by
    `4 + frame_len`.
  - `< 0` — PAD frame: `-frame_len` bytes of dead space recovery wrote over an
    uncommitted claim, or the writer wrote to skip a segment tail too small for
    a record. Reader skips, does not yield.
- Header and payload sizes are known from `H` and `frame_len`; no separate
  payload-length field needed (`payload_len = frame_len - size_of::<H>() -
  padding`, and padding is recomputable from alignment).

`i32` frame length caps a single record at 2 GiB — far below the 64 MB default
segment, and negative space is the PAD sentinel. A claim larger than the
configured segment size is rejected at `try_claim` (`RecordTooLarge`).

---

## Commit protocol (write path)

`try_claim(header, len) -> Option<WriteClaim>`:

1. Compute frame size, 8-byte aligned. If it doesn't fit the current segment's
   remaining space, write a PAD frame over the tail and roll to the next
   segment (see Segments). If it can't fit an empty segment → `RecordTooLarge`.
2. Reserve the region (advance the writer's local tail). The `frame_len` slot
   stays `0`.
3. Return `WriteClaim` exposing `header_mut()` and `as_mut_slice()` over the
   payload region.

`WriteClaim::commit(self)`:

1. Write header into its slot.
2. `fence(Release)`.
3. Store `frame_len` (positive) with `Ordering::Release` — the single aligned
   store that publishes the record.

Drop without commit leaves `frame_len == 0`; the space is reclaimed on recovery
as the stop point (or PAD-framed if a later claim already rolled past — but SPSC
single-writer means no later claim exists until commit, so an uncommitted claim
is always the tail). RAII commit mirrors nexus-logbuf's `WriteClaim`.

Hot path cost: one memcpy of the payload + two small stores + one fence. No
syscall, no allocation.

---

## Read path

`next_record() -> Option<ReadRecord<'_>>`:

1. Load `frame_len` at the reader cursor with `Ordering::Acquire`.
2. `0` → caught up, return `None`.
3. `< 0` → PAD, advance by `4 + (-frame_len)`, retry.
4. `> 0` → `fence(Acquire)` already covered by the acquire load; yield
   `ReadRecord { header: &H, payload: &[u8] }` borrowing the mapping. Advance
   cursor by `4 + frame_len` on next call.

`ReadRecord` borrows the segment mapping (`&'a`), zero-copy. Lifetime ties the
borrow to the reader so a segment can't be unmapped under a live record.

Cross-process readers open segments read-only (`Mapping::open`) and run the
same scan. `frame_len`'s acquire load + the writer's release store give the
happens-before edge across the process boundary.

---

## Recovery

On `open`, scan the **last** segment from its start:

1. Walk records by `frame_len` (skipping PAD frames) until the first
   `frame_len == 0` — that offset is the write tail.
2. Optionally verify the last committed record's checksum if the durability
   flag is on; on mismatch, treat as uncommitted (truncate to its start).
3. The writer resumes appending at the recovered tail.

No unwinding, no allocation — a forward pointer-walk. The sentinel guarantees
recovery never reads a committed-but-torn record (the marker is the last store).

---

## Segments

- Files named `{base}.{index}` (e.g. `journal.0`, `journal.1`), each a #390
  `Segment` of `segment_size` bytes.
- Writer rolls to `index + 1` when a record doesn't fit the current tail,
  PAD-framing the leftover. Segment roll is the only place a new file is
  created/mapped.
- Reader follows the same sequence, mapping the next segment when it exhausts
  the current one.
- `read_range` (FIX, when `H = FixHeader`): a thin layer over the position scan
  — locate the start segment, scan forward yielding records whose `seq` falls
  in range. O(1) recent-seq lookup via an optional fixed-size ring index is
  deferred (not needed for correctness; note it as future work).

> `read_range` lives behind an impl bound `where H: SeqHeader` so it's only
> available when the header actually carries a sequence. `()` callers never see
> it. Keeps FIX semantics off the general primitive while still living in one
> crate.

---

## API sketch

```rust
let cfg = JournalConfig { segment_size, checksum, .. };
let (mut writer, mut reader) = Journal::<FixHeader>::open(base_path, cfg)?;

// Write (hot path)
let mut claim = writer.try_claim(FixHeader { seq, timestamp }, payload.len())?;
claim.as_mut_slice().copy_from_slice(payload);
claim.commit();

// Sequential read
while let Some(rec) = reader.next_record() {
    process(rec.header(), rec.payload());
}

// FIX resend — only when H: SeqHeader
for rec in reader.read_range(start_seq..=end_seq)? {
    retransmit(rec.payload());
}
```

---

## Scope for the PR

- `Journal<H>` open/recovery, `WriteClaim` (commit protocol), `ReadRecord`,
  segment roll, `JournalConfig`, `()` and a `FixHeader` reference header.
- `read_range` behind `H: SeqHeader`.
- Tests: roundtrip, multi-segment roll, recovery (uncommitted tail, PAD skip,
  torn-with-checksum), cross-process read-only attach.
- Criterion bench for `try_claim`+`commit` (hot path) and `next_record`.

Out of scope: the O(1) ring index, MPSC (SPSC only per the doc), the durable
fsync policy (mmap-is-persistence; fsync is a caller concern, note it).

## Open questions for review

1. **`frame_len` as `i32`** (2 GiB record cap, negative = PAD) vs a separate
   explicit `marker` byte + `u32` len. The combined sign-as-sentinel is the
   Aeron model and saves a field; the explicit-marker variant is more readable
   at the cost of a byte. Lean Aeron.
2. **PAD on graceful drop** — since SPSC means an uncommitted claim is always
   the tail, do we ever need to PAD-over on drop, or is "leave it 0, recovery
   stops" sufficient? I believe the latter; flagging in case you want
   drop-time PAD for forward-scan tooling.
3. **`read_range` return** — borrowing iterator over the mapping (zero-copy,
   ties up the reader) vs collected positions. Lean iterator, matches
   `next_record`.
