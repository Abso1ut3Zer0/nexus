# Changelog

All notable changes to nexus-platform are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Changed (breaking)

- `Mapping::as_ptr` now returns `*const u8` instead of `*mut u8`. Use the new
  `Mapping::as_mut_ptr(&mut self) -> *mut u8` at sites that write through the
  pointer.
- `Mapping::write_at` now takes `&mut self`. `MappedFile` and `SharedMemory`
  gain `DerefMut` so that `write_at` is reachable through them with a `mut`
  binding.
- `MappedFile` and `SharedMemory` now implement `DerefMut<Target = Mapping>`.
  Existing code that calls `write_at` on a non-mut binding will not compile;
  add `mut` to the binding.

### Added

- `FileLock` — RAII exclusive file lock for mutual exclusion (blocking
  and non-blocking). Extracted from nexus-shm.
- `ProcessLease` — kernel-mediated process liveness detection via OFD
  byte-range locks. Extracted from nexus-shm.
- `Liveness` enum (`Alive`, `Dead`, `Unknown`) for lease probe results.
- Linux backend using OFD locks (`F_OFD_SETLK` / `F_OFD_GETLK`).
