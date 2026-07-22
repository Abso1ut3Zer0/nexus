# Unsafe audit open items

Items that could not be fully verified during the SAFETY comment pass.
Each entry has a crate, file, approximate line, and the specific question.

---

## nexus-shm

### 1. Post-Release payload writes in `ShmSlotWriter::create` and `ShmRingWriter::create`

**File:** `nexus-shm/src/slot.rs` (`ShmSlotReader::attach`, line ~135)
**File:** `nexus-shm/src/ring.rs` (`read_capacity` / `read_elem_size`, lines ~26-31)

**Issue:** `ShmSlotWriter::create` and `ShmRingWriter::create` both write
`elem_size` (and `capacity` in the ring case) to the payload *after*
`Segment::create_file` returns. `Segment::create_file` stores `status=ALIVE`
with `Ordering::Release` inside `ControlBlock::write_header`. Because the
payload writes happen after that Release, a reader that Acquire-loads
`status=ALIVE` in `Segment::attach` is not formally guaranteed to observe
those payload writes under the C11 memory model.

**In practice:** On x86 (TSO), stores are globally visible in program order.
On ARM/POWER, the page-cache coherency mechanism and the fact that the reader
typically opens the file only after the writer process has finished `create()`
provide de-facto ordering. However, this relies on OS-level happens-before
(filesystem open/close), not the Rust/C11 memory model.

**Fix:** Move the `elem_size`/`capacity` writes to before the Release store
of `status=ALIVE`, i.e., initialize the payload header inside `Segment::create`
(or via a callback) before `write_header` is called. This would make the
Acquire/Release pair formally sufficient.

**Risk level:** Low in practice (x86 Linux), but not formally sound.
