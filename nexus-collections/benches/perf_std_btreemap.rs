//! std::collections::BTreeMap benchmark: cycle-accurate latency measurement.
//!
//! Same methodology as perf_btree.rs / perf_rbtree.rs for direct comparison.
//! Uses batched seq! unrolling to amortize rdtsc overhead.
//!
//! Run with:
//!   cargo build --release --example perf_std_btreemap -p nexus-collections
//!   taskset -c 0 ./target/release/examples/perf_std_btreemap

use seq_macro::seq;
use std::collections::BTreeMap;
use std::hint::black_box;

const SAMPLES: usize = 50_000;
const WARMUP: usize = 5_000;
const BATCH_READ: usize = 100;
const STEADY_SIZE: usize = 10_000;
const SMALL_SIZE: usize = 100;

#[inline(always)]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsics; benchmark is x86_64-only.
    unsafe {
        std::arch::x86_64::_mm_lfence();
        std::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsics; benchmark is x86_64-only.
    unsafe {
        let mut aux: u32 = 0;
        let tsc = std::arch::x86_64::__rdtscp(&raw mut aux);
        std::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_row(label: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "  {:<32} p50={:>5}  p90={:>5}  p99={:>6}  p999={:>7}  max={:>8}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
}

struct Xorshift {
    state: u64,
}

impl Xorshift {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }
    fn next(&mut self) -> u64 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        self.state
    }
}

#[allow(clippy::collection_is_never_read, clippy::unnecessary_semicolon)]
fn main() {
    let mut rng = Xorshift::new(0xDEAD_BEEF_CAFE_BABEu64);

    println!("STD BTREEMAP OPERATION LATENCY (cycles/op) — steady state populations");
    println!("Samples: {SAMPLES}, Warmup: {WARMUP}");
    println!("====================================================================\n");

    // ── GET ───────────────────────────────────────────────────────────
    println!("GET (read-only, {BATCH_READ} unrolled ops/sample)");
    println!("---");

    // get (small @100)
    {
        let mut map = BTreeMap::new();
        let keys: Vec<u64> = (0..SMALL_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let lookup: [u64; BATCH_READ] = std::array::from_fn(|i| keys[i % keys.len()]);
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { black_box(map.get(&lookup[I])); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { black_box(map.get(&lookup[I])); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
        }
        print_row(&format!("get (hit, @{SMALL_SIZE})"), &mut samples);
    }

    // get (steady @10k)
    {
        let mut map = BTreeMap::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let lookup: [u64; BATCH_READ] = std::array::from_fn(|i| keys[i % keys.len()]);
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { black_box(map.get(&lookup[I])); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { black_box(map.get(&lookup[I])); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
        }
        print_row(&format!("get (hit, @{STEADY_SIZE})"), &mut samples);

        // get miss
        let miss_keys: [u64; BATCH_READ] = {
            let mut mk = [0u64; BATCH_READ];
            let mut i = 0;
            while i < BATCH_READ {
                let k = rng.next();
                if !map.contains_key(&k) {
                    mk[i] = k;
                    i += 1;
                }
            }
            mk
        };
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { black_box(map.get(&miss_keys[I])); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { black_box(map.get(&miss_keys[I])); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
        }
        print_row(&format!("get (miss, @{STEADY_SIZE})"), &mut samples);
    }

    // get (cold random access @10k)
    {
        let mut map = BTreeMap::new();
        let mut keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        for i in (1..keys.len()).rev() {
            let j = rng.next() as usize % (i + 1);
            keys.swap(i, j);
        }
        let num_keys = keys.len();
        let mut samples = Vec::with_capacity(SAMPLES);
        let mut offset = 0usize;
        for _ in 0..WARMUP {
            let mut total = 0u64;
            for j in 0..BATCH_READ {
                total = total.wrapping_add(*map.get(&keys[(offset + j) % num_keys]).unwrap());
            }
            black_box(total);
            offset = (offset + BATCH_READ) % num_keys;
        }
        for _ in 0..SAMPLES {
            let mut total = 0u64;
            let s = rdtsc_start();
            for j in 0..BATCH_READ {
                total = total.wrapping_add(*map.get(&keys[(offset + j) % num_keys]).unwrap());
            }
            let e = rdtsc_end();
            black_box(total);
            samples.push((e - s) / BATCH_READ as u64);
            offset = (offset + BATCH_READ) % num_keys;
        }
        print_row(&format!("get (cold rand, @{STEADY_SIZE})"), &mut samples);
    }

    // contains_key
    {
        let mut map = BTreeMap::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let lookup: [u64; BATCH_READ] = std::array::from_fn(|i| keys[i % keys.len()]);
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { black_box(map.contains_key(&lookup[I])); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { black_box(map.contains_key(&lookup[I])); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
        }
        print_row(&format!("contains_key (hit, @{STEADY_SIZE})"), &mut samples);
    }

    println!();

    // ── INSERT / REMOVE ──────────────────────────────────────────────
    println!("INSERT / REMOVE (100 unrolled ops/sample)");
    println!("---");

    // insert (growing, per-op)
    {
        let mut map = BTreeMap::new();
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            map.insert(rng.next(), 0u64);
        }
        map.clear();
        for _ in 0..SAMPLES {
            let k = rng.next();
            let s = rdtsc_start();
            black_box(map.insert(k, 0));
            let e = rdtsc_end();
            samples.push(e - s);
        }
        print_row("insert (growing, per-op)", &mut samples);
    }

    // insert (steady @10k) — batched
    {
        let mut map = BTreeMap::new();
        let steady_keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &steady_keys {
            map.insert(k, k);
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            let batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            seq!(I in 0..100 { map.insert(batch[I], 0); });
            seq!(I in 0..100 { map.remove(&batch[I]); });
        }
        for _ in 0..SAMPLES {
            let batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            let s = rdtsc_start();
            seq!(I in 0..100 { map.insert(batch[I], 0); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            seq!(I in 0..100 { map.remove(&batch[I]); });
        }
        print_row(&format!("insert (steady @{STEADY_SIZE})"), &mut samples);
    }

    // remove (steady @10k) — batched
    {
        let mut map = BTreeMap::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        let mut offset = 0usize;
        for _ in 0..WARMUP {
            let base = offset % STEADY_SIZE;
            let batch: [u64; BATCH_READ] = std::array::from_fn(|i| keys[(base + i) % STEADY_SIZE]);
            seq!(I in 0..100 { map.remove(&batch[I]); });
            seq!(I in 0..100 { map.insert(batch[I], batch[I]); });
            offset += BATCH_READ;
        }
        offset = 0;
        for _ in 0..SAMPLES {
            let base = offset % STEADY_SIZE;
            let batch: [u64; BATCH_READ] = std::array::from_fn(|i| keys[(base + i) % STEADY_SIZE]);
            let s = rdtsc_start();
            seq!(I in 0..100 { map.remove(&batch[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            seq!(I in 0..100 { map.insert(batch[I], batch[I]); });
            offset += BATCH_READ;
        }
        print_row(&format!("remove (steady @{STEADY_SIZE})"), &mut samples);
    }

    // insert dup — batched
    {
        let mut map = BTreeMap::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let lookup: [u64; BATCH_READ] = std::array::from_fn(|i| keys[i % keys.len()]);
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { black_box(map.insert(lookup[I], 999)); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { black_box(map.insert(lookup[I], 999)); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
        }
        print_row(&format!("insert dup (steady @{STEADY_SIZE})"), &mut samples);
    }

    println!();

    // ── ENTRY API ────────────────────────────────────────────────────
    println!("ENTRY API (100 unrolled ops/sample)");
    println!("---");

    // entry occupied — batched
    {
        let mut map = BTreeMap::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let lookup: [u64; BATCH_READ] = std::array::from_fn(|i| keys[i % keys.len()]);
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 {
                if let std::collections::btree_map::Entry::Occupied(mut o) = map.entry(lookup[I]) {
                    *o.get_mut() += 1;
                }
            });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 {
                if let std::collections::btree_map::Entry::Occupied(mut o) = map.entry(lookup[I]) {
                    *o.get_mut() += 1;
                }
            });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
        }
        print_row(&format!("entry occupied (@{STEADY_SIZE})"), &mut samples);
    }

    // entry vacant — batched
    {
        let mut map = BTreeMap::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            let batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            seq!(I in 0..100 { map.entry(batch[I]).or_insert(0); });
            seq!(I in 0..100 { map.remove(&batch[I]); });
        }
        for _ in 0..SAMPLES {
            let batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            let s = rdtsc_start();
            seq!(I in 0..100 { map.entry(batch[I]).or_insert(0); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            seq!(I in 0..100 { map.remove(&batch[I]); });
        }
        print_row(
            &format!("entry vacant+insert (@{STEADY_SIZE})"),
            &mut samples,
        );
    }

    println!();

    // ── POP ──────────────────────────────────────────────────────────
    println!("POP (100 unrolled ops/sample)");
    println!("---");

    // pop_first — batched
    {
        let mut map = BTreeMap::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            let mut buf = [(0u64, 0u64); BATCH_READ];
            seq!(I in 0..100 { buf[I] = map.pop_first().unwrap(); });
            for &(k, v) in &buf {
                map.insert(k, v);
            }
        }
        for _ in 0..SAMPLES {
            let mut buf = [(0u64, 0u64); BATCH_READ];
            let s = rdtsc_start();
            seq!(I in 0..100 { buf[I] = map.pop_first().unwrap(); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            for &(k, v) in &buf {
                map.insert(k, v);
            }
        }
        print_row(&format!("pop_first (@{STEADY_SIZE})"), &mut samples);
    }

    // pop_last — batched
    {
        let mut map = BTreeMap::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            let mut buf = [(0u64, 0u64); BATCH_READ];
            seq!(I in 0..100 { buf[I] = map.pop_last().unwrap(); });
            for &(k, v) in &buf {
                map.insert(k, v);
            }
        }
        for _ in 0..SAMPLES {
            let mut buf = [(0u64, 0u64); BATCH_READ];
            let s = rdtsc_start();
            seq!(I in 0..100 { buf[I] = map.pop_last().unwrap(); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            for &(k, v) in &buf {
                map.insert(k, v);
            }
        }
        print_row(&format!("pop_last (@{STEADY_SIZE})"), &mut samples);
    }

    println!();

    // ── CHURN ────────────────────────────────────────────────────────
    println!("CHURN (remove+insert pair, {BATCH_READ} unrolled ops/sample)");
    println!("---");
    {
        let mut map = BTreeMap::new();
        let mut keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.insert(k, k);
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        let mut offset = 0usize;
        for _ in 0..WARMUP {
            let base = offset % STEADY_SIZE;
            let old_batch: [u64; BATCH_READ] =
                std::array::from_fn(|i| keys[(base + i) % STEADY_SIZE]);
            let new_batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            seq!(I in 0..100 {
                map.remove(&old_batch[I]);
                map.insert(new_batch[I], new_batch[I]);
            });
            for i in 0..BATCH_READ {
                keys[(base + i) % STEADY_SIZE] = new_batch[i];
            }
            offset += BATCH_READ;
        }
        offset = 0;
        for _ in 0..SAMPLES {
            let base = offset % STEADY_SIZE;
            let old_batch: [u64; BATCH_READ] =
                std::array::from_fn(|i| keys[(base + i) % STEADY_SIZE]);
            let new_batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            let s = rdtsc_start();
            seq!(I in 0..100 {
                map.remove(&old_batch[I]);
                map.insert(new_batch[I], new_batch[I]);
            });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            for i in 0..BATCH_READ {
                keys[(base + i) % STEADY_SIZE] = new_batch[i];
            }
            offset += BATCH_READ;
        }
        print_row(&format!("churn (@{STEADY_SIZE})"), &mut samples);
    }
}
