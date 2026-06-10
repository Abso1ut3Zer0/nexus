# nexus-journal — performance catalogue

Latency measurements for the `RotatingJournal` append path. Numbers are a
record of a representative run, not a contract — reproduce locally with the
tools below before relying on them.

## Methodology

- **Timing:** [`examples/rotating_tail.rs`] — fenced rdtsc (`lfence; rdtsc` /
  `rdtscp; lfence`), measured per `append()`, captured in HDR histograms. The
  harness calibrates the TSC against a wall-clock interval and prints the rate.
- **Units:** TSC **cycles** (the invariant TSC ticks at a constant nominal rate,
  not the variable core clock). `ns = cycles / TSC_GHz`. The box below reports
  `tsc = 2.688 GHz`.
- **Isolation:** pinned with `taskset -c 0,2` (two physical cores — one tends to
  the writer, one the conductor), turbo disabled, **disk-backed ext4 on nvme**
  (the journal's real target; `/tmp` is often tmpfs and not representative).
- **Classification:** each append is bucketed `normal` / `page-crossing` (the
  frame spans a 4 KiB page) / `rotation` (epoch advanced), plus a combined
  **ALL** histogram. `StandbyNotReady` is timed retry-to-success and folded into
  ALL (no coordinated omission).
- **Platform:** x86_64 only (rdtsc). The crate itself is Linux-only.

## RotatingJournal — append latency

**Default config:** 4 MiB segments, `qdepth = 4`, `pretouch = true`, 64 B
payload, **unpaced** (max rate), 5,000,000 appends.

### ALL appends — what the caller sees

| quantile | cycles | ns      |
|----------|-------:|--------:|
| p50      |     86 |    ~32  |
| p99      |    144 |    ~54  |
| p99.9    |    288 |   ~107  |
| p99.99   |  5,447 |  ~2,030 |
| max      |122,000 | ~45,000 |

Half of all appends are \~32 ns; 99.9 % are under ~110 ns; 99.99 % under \~2 µs.
The single worst of 5 M (\~45 µs) is a page-crossing append that hit kernel
dirty-page machinery, or a thread preemption (non-isolated core).

### Breakdown (same run)

| class      |      n     | p50 | p99   | p99.9  | note                          |
|------------|-----------:|----:|------:|-------:|-------------------------------|
| normal     | 4,921,809  |  86 |   142 |    212 | 98.5 % of appends; no syscall |
| page-cross |    78,106  | 122 | 4,983 | 17,103 | ~1.5 %; carries the µs tail   |
| rotation   |        85  |8,775| 25,519| 25,519 | the rotate bookkeeping + wake |
| stall      |         0  |  —  |   —   |    —   | conductor keeps up at 4 MiB   |

Smaller segments tighten the page-cross tail sharply (the writer fills a slot
before the kernel's writeback catches up):

| segment | page-cross p99 | page-cross p99.9 |
|---------|---------------:|-----------------:|
| 256 KiB |          ~200  |           ~6,000 |
| 4 MiB   |         ~5,000 |          ~17,000 |

## Where the tail comes from

The hot path (`append`) touches the kernel in **zero** places — every
`msync`/`munmap`/file-create/`mmap` lives on the background conductor thread.
So the only writer-side costs are cache misses, the per-rotation wake, page
faults, and rotation backpressure.

The **page-crossing tail is the kernel managing a large, sustained volume of
dirty file-backed pages** — some mix of writeback, page re-protection, ext4
delayed allocation, and jbd2 journal commits — occasionally blocking the writer
on a page-crossing store. It is **inherent to file-backed `MAP_SHARED`
journaling under load** (the same tax Aeron / Chronicle / mmap-Kafka pay), not a
flaw in this design.

It is **governed by write volume and segment size, not by reuse**.
[`examples/mmap_fill_probe.rs`] confirms this on a single *fresh* mapping (no
rotation, no reuse):

| fresh fill | page-cross p99 | p99.9 | max       |
|------------|---------------:|------:|----------:|
| 64 MiB     |           210  |   646 |     1,388 |
| 2 GiB      |           612  | 5,639 | 2,729,983 |

A 64 MiB fresh fill is clean; the tail emerges only once enough volume is
written to keep the kernel's writeback machinery busy.

The conductor **prefaults every segment it publishes** (write-touches all pages)
so the `page_mkwrite` faults are paid on the conductor, off the writer's hot
path. This cut the deep page-cross tail ~4× (p99.9 ~26 µs → ~6 µs). It cannot
fully win at saturation on large segments, because the kernel re-protects pages
faster than a slowly-traversed large segment is filled.

## Sizing guidance

- **Size segments so a slot fills faster than the kernel writes it back.** At
  256 KiB the page-cross tail is negligible; at 4 MiB a small p99.99 tail
  appears under sustained max-rate writing.
- The default 4 MiB trades that for fewer rotations (less conductor work, fewer
  wake events). Pick smaller segments when tail latency dominates capacity.
- Pacing does **not** help — a slower writer loses more ground to background
  writeback. The good numbers are the unpaced ones.

## Reproduce

```bash
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo   # turbo off
cargo build --release -p nexus-journal --examples

# disk-backed temp dir (avoid tmpfs)
export TMPDIR="$PWD/target/tailbench"; mkdir -p "$TMPDIR"

# default config, combined + breakdown
SEG=4194304 PAYLOAD=64 WRITES=5000000 PRETOUCH=1 QDEPTH=4 \
  taskset -c 0,2 ./target/release/examples/rotating_tail

# tighter tail with smaller segments
SEG=262144 taskset -c 0,2 ./target/release/examples/rotating_tail

# isolate the write-volume effect (fresh fill, no reuse)
SIZE=$((2*1024*1024*1024)) taskset -c 0,2 ./target/release/examples/mmap_fill_probe

echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo   # turbo back on
```

## Tools

- [`examples/rotating_tail.rs`] — tail harness; classifies appends and reports a
  combined ALL distribution. Knobs: `SEG PAYLOAD WRITES PRETOUCH QDEPTH PACE_NS`.
- [`examples/mmap_fill_probe.rs`] — single fresh sequential mmap fill; isolates
  the write-volume / writeback effect from the rotation machinery.
- [`benches/append.rs`] — criterion microbench for the append-only journal.

[`examples/rotating_tail.rs`]: examples/rotating_tail.rs
[`examples/mmap_fill_probe.rs`]: examples/mmap_fill_probe.rs
[`benches/append.rs`]: benches/append.rs
