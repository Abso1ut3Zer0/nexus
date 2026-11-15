# Benchmarking in Nexus

Read this before running your first benchmark. Latency measurement is
full of traps — an uncontrolled run will give you numbers that are
wrong in ways that look right, and you'll chase ghosts for hours.

---

## 1. Methodology: Cycles, Not Nanoseconds

Nexus primitives are measured in **CPU cycles**, not nanoseconds.

- Cycles are what the CPU actually does. They are invariant to turbo
  boost, thermal throttling, and frequency scaling.
- Nanoseconds depend on the current clock speed, which changes mid
  run. A 500ns measurement at 3.0 GHz and a 500ns measurement at
  4.5 GHz represent very different amounts of work.
- We report p50, p99, p999, p9999, max in cycles. Throughput
  (msg/sec) is reported separately when that's the useful number.

Conversion (handy but imprecise): on a 3 GHz core, 1 ns ≈ 3 cycles.
Use this only for back-of-envelope — never publish a nanosecond
number as a latency result.

---

## 2. Controlled Conditions

Every benchmark that lands in a `BENCHMARKS.md` or a crate's performance page must be
run under controlled conditions. Anything else is a research number,
not a result.

### Disable turbo boost

```bash
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

Turbo boost lets the CPU run above base clock opportunistically. It
adds variance (thermal headroom fluctuates), and it makes runs
non-reproducible between machines. **Off for every benchmark.**

### Pin to physical cores

Find the topology first:

```bash
lscpu -e
```

Look at the `CORE` column. Two logical CPUs with the same `CORE` are
hyperthreading siblings of the same physical core — **do not use
both**. Pick one logical CPU per physical core for anything that
matters.

```bash
# Example: pin to physical cores 0 and 2
sudo taskset -c 0,2 ./target/release/deps/your_bench-HASH
```

For criterion:

```bash
sudo taskset -c 0,2 cargo bench -p nexus-stats
```

### Re-enable turbo when you're done

```bash
echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

Your laptop will thank you.

### Other controls worth knowing

- **Stop background processes.** Browsers, sync daemons, Slack, VSCode
  rust-analyzer. Anything that wakes up and steals cycles.
- **Disable frequency scaling** (governor=performance) for kernels
  that need it:
  ```bash
  sudo cpupower frequency-set -g performance
  ```
- **irqbalance off** and **isolate cores** for serious runs. Not
  required for crate-level perf work, but required for end-to-end
  trading-system numbers.
- **AC power** on laptops. Battery triggers aggressive throttling.

---

## 3. Benchmark Types in the Workspace

Two flavors coexist. They answer different questions.

### Criterion benches (`cargo bench`)

Location: `<crate>/benches/`. Driver: [criterion.rs](https://github.com/bheisler/criterion.rs).

**Good for:** statistical measurement of small operations. Criterion
handles warmup, iteration count, and confidence intervals for you.
Output: ns/op with mean + variance.

```bash
sudo taskset -c 0,2 cargo bench -p nexus-stats --bench update_bench
```

**Not good for:** tail latency (p99.9+). Criterion reports means and
medians by default. For tail work, use the cycle examples.

### Cycle examples (`examples/perf_*.rs`)

Location: `<crate>/examples/`. Driver: hand-rolled `rdtsc` loops
that write samples into an HDR histogram or sorted array.

**Good for:** p50 / p99 / p999 / p9999 / max on a hot path. You own
the measurement loop so you control warmup, batching, and exactly
what's timed.

```bash
cargo build --release --example perf_isolated -p nexus-slab
sudo taskset -c 0,2 ./target/release/examples/perf_isolated slot
```

**Not good for:** statistical summaries across runs. One example run
is one sample.

### Which to use when

| Question | Use |
|----------|-----|
| "Did this patch regress the mean?" | Criterion |
| "What is the p999 of this hot path?" | Cycle example |
| "Is my optimization actually faster?" | Criterion, A/B |
| "How bad are the tails under load?" | Cycle example |
| "Does this allocate on the hot path?" | Cycle example + `dhat` or `perf stat` for page faults |

---

## 4. Reading the Output

When you see `p50 / p99 / p999 / p9999 / max`, here is what each
tells you:

- **p50 (median).** Typical case. If this regresses, you probably
  did something wrong at the instruction level — extra branch, lost
  inline, cache miss in the common path.
- **p99.** 1-in-100 samples are worse than this. This is the number
  you publish for "latency" in a marketing doc. It captures normal
  variance without being dominated by outliers.
- **p999.** 1-in-1000. This is where GC pauses, TLB misses, context
  switches, and other "rare but real" events start showing up. For
  a trading system, **this is the number you actually care about.**
- **p9999.** 1-in-10,000. Tail. Page faults, NUMA migration, IRQs.
  Real production systems have to survive this regularly.
- **max.** One sample. Mostly useful as a sanity check — "did
  anything catastrophic happen?" Don't compare maxes between runs.

**Mean** is not on this list deliberately. A junior engineer using
mean latency to characterize a trading system is a correctness bug,
not a style issue. Fat-tailed distributions have means dominated by
outliers — you'll draw the wrong conclusion.

---

## 5. A/B Comparing Branches

When you want to know "did this patch change perf?", run each side
under the same conditions, back to back, same core pinning, same
turbo state. Do not compare a run from yesterday to a run from today.

Rough procedure:

```bash
# 1. Set the box up once
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo

# 2. Baseline
git checkout main
cargo bench -p nexus-stats --bench update_bench -- --save-baseline main

# 3. Your branch
git checkout my-feature
cargo bench -p nexus-stats --bench update_bench -- --baseline main

# 4. Tear down
echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

Criterion will report percent change and confidence intervals. If the
change overlaps zero, **you did not prove anything.**

For cycle examples, run each side 5 times and take the best p999.
"Best" is right because the noise floor is physical — context
switches and IRQs can only make things worse. The fastest run is
closest to what the hardware actually does.

---

## 6. Common Pitfalls

### Coordinated omission

If your measurement loop stalls, you stop taking samples during the
stall — so the stall doesn't show up in your histogram. The result
looks clean but lies about tail latency.

Fix: use a rate-controlled submission pattern where the expected
arrival time is fixed and you measure `(now - expected_arrival)`
regardless of when you actually got to measure. `hdrhistogram` has
coordinated-omission-corrected recording.

### No warmup

First run of a benchmark pays for: page faults, TLB misses,
instruction cache cold start, JIT of the closure, allocator cold
paths. If you include those samples, your p50 is garbage.

Fix: run 1000+ iterations and discard them before starting to record.
Criterion does this automatically. Cycle examples must do it manually.

### Measuring the wrong thing

Classic: you wrap a hot path in `Instant::now() / elapsed()` and
publish a "10 ns per op" number. `Instant::now()` itself is often
20–30 ns on Linux. You measured the clock, not the code.

Fix: batch. Time 1000 operations as a block, divide. Or use `rdtsc`
directly for single-op timing.

### Allocator interference

Running a benchmark in the same process as a warm-up phase leaves
the allocator in a state you didn't intend. Freelists are populated,
arenas are hot. Your "hot path" is measuring something the production
system will never see.

Fix: isolate hot path code so allocation cannot happen in the window
you're measuring. `#[global_allocator]` counting (via `dhat`) is a
cheap sanity check.

### JIT / cold code

LLVM may hoist, inline, or eliminate code when the compiler can
prove the result is unused. Your bench thinks it measured something;
the binary skipped it entirely.

Fix: `std::hint::black_box` the input **and** the output. Check
`cargo asm` for the inner loop if a result looks too good.

### Hyperthreading siblings

Pinning to both logical CPUs of the same core halves your execution
resources. You get a measurement that is consistent with itself and
wrong.

Fix: `lscpu -e`, pick one logical CPU per physical core.

---

## 7. Reference Benchmarks in the Workspace

Most crates ship their own perf docs. When you change a crate, check
its numbers against the committed reference.

| Crate | Perf doc | Runner |
|-------|----------|--------|
| `nexus-queue` | `README.md` results section | criterion + examples |
| `nexus-channel` | `README.md` | criterion + examples |
| `nexus-slot` | `README.md` | criterion |
| `nexus-slab` | `BENCHMARKS.md` (via `examples/bench_isolated.rs`) | cycle example |
| `nexus-pool` | `README.md` | criterion + examples |
| `nexus-logbuf` | `README.md` | criterion |
| `nexus-stats` | `docs/reference/performance.md` | cycle example (`perf_stats`) + criterion (`update_bench`) |
| `nexus-rate` | `README.md` | criterion |
| `nexus-net` | `README.md` | criterion + TCP loopback harness |
| `nexus-async-web` | `README.md` | criterion + TCP loopback |
| `nexus-async-rt` | `BENCHMARKS.md` | criterion + examples |
| `nexus-rt` | `nexus-rt/docs/` | criterion |

When you update a number, update the doc in the same PR. An unchanged
BENCHMARKS.md with a regressed primitive is a bug.

---

## 8. Sanity Checklist (before publishing a number)

- [ ] Turbo off
- [ ] Pinned to physical cores only
- [ ] Background processes stopped
- [ ] Governor = performance
- [ ] Warmup confirmed (look at the first 100 samples vs the last)
- [ ] Same binary, same flags for A and B
- [ ] Reported p50 **and** p999, not just mean
- [ ] Checked `cargo asm` if the result surprised you
- [ ] Turbo re-enabled when you walked away from the machine
