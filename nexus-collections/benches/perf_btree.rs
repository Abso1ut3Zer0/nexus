#![allow(clippy::unnecessary_semicolon)]
//! B-tree benchmark: cycle-accurate latency measurement.
//!
//! Measures insert, remove, get, entry, pop_first, pop_last at various
//! population sizes. Same methodology as perf_rbtree for direct comparison.
//!
//! Run with:
//!   cargo build --release --example perf_btree -p nexus-collections
//!   taskset -c 0 ./target/release/examples/perf_btree

use seq_macro::seq;
use std::hint::black_box;

use nexus_collections::slab::btree::{BTree, BTreeNode, Entry};

const B: usize = 8;
const CAPACITY: usize = 200_000;
const SAMPLES: usize = 50_000;
const WARMUP: usize = 5_000;
const BATCH_READ: usize = 100;
const STEADY_SIZE: usize = 10_000;
const SMALL_SIZE: usize = 100;

#[inline(always)]
fn rdtsc_start() -> u64 {
    unsafe {
        std::arch::x86_64::_mm_lfence();
        std::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
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

fn main() {
    let slab =
        unsafe { nexus_slab::bounded::Slab::<BTreeNode<u64, u64, B>>::with_capacity(CAPACITY) };

    let mut rng = Xorshift::new(0xDEAD_BEEF_CAFE_BABEu64);

    println!("B-TREE OPERATION LATENCY (cycles/op) — steady state populations");
    println!("Samples: {SAMPLES}, Warmup: {WARMUP}, B={B}");
    println!("====================================================================\n");

    // ── GET (batched, read-only — seq_macro unrolled) ───────────────
    println!("GET (read-only, {BATCH_READ} unrolled ops/sample)");
    println!("---");

    // get (small @100)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let keys: Vec<u64> = (0..SMALL_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
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
        map.clear(&slab);
    }

    // get (steady @10k)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
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

        // get miss (random keys not in tree)
        let miss_keys: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
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
        map.clear(&slab);
    }

    // get (cold random access @10k)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let mut keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
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
        map.clear(&slab);
    }

    // contains_key (steady @10k)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
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
        map.clear(&slab);
    }

    println!();

    // ── INSERT / REMOVE ─────────────────────────────────────────────
    println!("INSERT / REMOVE ({BATCH_READ} unrolled ops/sample)");
    println!("---");

    // insert (into empty, growing — per-op, tree size varies)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            map.try_insert(&slab, rng.next(), 0).unwrap();
        }
        map.clear(&slab);
        for _ in 0..SAMPLES {
            let k = rng.next();
            let s = rdtsc_start();
            let _ = black_box(map.try_insert(&slab, k, 0));
            let e = rdtsc_end();
            samples.push(e - s);
        }
        print_row("insert (growing, per-op)", &mut samples);
        map.clear(&slab);
    }

    // insert (steady @10k, batched)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let steady_keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &steady_keys {
            map.try_insert(&slab, k, k).unwrap();
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            let batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            seq!(I in 0..100 { let _ = black_box(map.try_insert(&slab, batch[I], 0)); });
            for &k in &batch {
                map.remove(&slab, &k);
            }
        }
        for _ in 0..SAMPLES {
            let batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            let s = rdtsc_start();
            seq!(I in 0..100 { let _ = black_box(map.try_insert(&slab, batch[I], 0)); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            for &k in &batch {
                map.remove(&slab, &k);
            }
        }
        print_row(&format!("insert (steady @{STEADY_SIZE})"), &mut samples);
        map.clear(&slab);
    }

    // remove (steady @10k, batched)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        let mut offset = 0usize;
        for _ in 0..WARMUP {
            let base = offset % keys.len();
            let batch: [u64; BATCH_READ] = std::array::from_fn(|i| keys[(base + i) % keys.len()]);
            seq!(I in 0..100 { black_box(map.remove(&slab, &batch[I])); });
            for &k in &batch {
                map.try_insert(&slab, k, k).unwrap();
            }
            offset += BATCH_READ;
        }
        offset = 0;
        for _ in 0..SAMPLES {
            let base = offset % keys.len();
            let batch: [u64; BATCH_READ] = std::array::from_fn(|i| keys[(base + i) % keys.len()]);
            let s = rdtsc_start();
            seq!(I in 0..100 { black_box(map.remove(&slab, &batch[I])); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            for &k in &batch {
                map.try_insert(&slab, k, k).unwrap();
            }
            offset += BATCH_READ;
        }
        print_row(&format!("remove (steady @{STEADY_SIZE})"), &mut samples);
        map.clear(&slab);
    }

    // insert duplicate key (batched, update in place)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
        }
        let lookup: [u64; BATCH_READ] = std::array::from_fn(|i| keys[i % keys.len()]);
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { let _ = black_box(map.try_insert(&slab, lookup[I], 999)); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { let _ = black_box(map.try_insert(&slab, lookup[I], 999)); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
        }
        print_row(&format!("insert dup (steady @{STEADY_SIZE})"), &mut samples);
        map.clear(&slab);
    }

    println!();

    // ── ENTRY API ────────────────────────────────────────────────────
    println!("ENTRY API (per-op, cycles)");
    println!("---");

    // entry (occupied, batched)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
        }
        let lookup: [u64; BATCH_READ] = std::array::from_fn(|i| keys[i % keys.len()]);
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { black_box(map.entry(&slab, lookup[I]).and_modify(|v| *v += 1)); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { black_box(map.entry(&slab, lookup[I]).and_modify(|v| *v += 1)); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
        }
        print_row(&format!("entry occupied (@{STEADY_SIZE})"), &mut samples);
        map.clear(&slab);
    }

    // entry (vacant — insert, batched)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            let batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            seq!(I in 0..100 {
                match map.entry(&slab, batch[I]) {
                    Entry::Vacant(v) => { let _ = black_box(v.try_insert(0)); }
                    Entry::Occupied(_) => {}
                }
            });
            for &k in &batch {
                map.remove(&slab, &k);
            }
        }
        for _ in 0..SAMPLES {
            let batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            let s = rdtsc_start();
            seq!(I in 0..100 {
                match map.entry(&slab, batch[I]) {
                    Entry::Vacant(v) => { let _ = black_box(v.try_insert(0)); }
                    Entry::Occupied(_) => {}
                }
            });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            for &k in &batch {
                map.remove(&slab, &k);
            }
        }
        print_row(
            &format!("entry vacant+insert (@{STEADY_SIZE})"),
            &mut samples,
        );
        map.clear(&slab);
    }

    println!();

    // ── POP ──────────────────────────────────────────────────────────
    println!("POP ({BATCH_READ} unrolled ops/sample)");
    println!("---");

    // pop_first (steady @10k, batched)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
        }
        let mut popped = [(0u64, 0u64); BATCH_READ];
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            for p in &mut popped {
                *p = map.pop_first(&slab).unwrap();
            }
            for &(k, v) in &popped {
                map.try_insert(&slab, k, v).unwrap();
            }
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = map.pop_first(&slab).unwrap(); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            for &(k, v) in &popped {
                map.try_insert(&slab, k, v).unwrap();
            }
        }
        print_row(&format!("pop_first (@{STEADY_SIZE})"), &mut samples);
        map.clear(&slab);
    }

    // pop_last (steady @10k, batched)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
        }
        let mut popped = [(0u64, 0u64); BATCH_READ];
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            for p in &mut popped {
                *p = map.pop_last(&slab).unwrap();
            }
            for &(k, v) in &popped {
                map.try_insert(&slab, k, v).unwrap();
            }
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = map.pop_last(&slab).unwrap(); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            for &(k, v) in &popped {
                map.try_insert(&slab, k, v).unwrap();
            }
        }
        print_row(&format!("pop_last (@{STEADY_SIZE})"), &mut samples);
        map.clear(&slab);
    }

    // first_key_value (batched, read-only)
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        for i in 0..STEADY_SIZE {
            map.try_insert(&slab, i as u64, 0).unwrap();
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(_ in 0..100 { black_box(map.first_key_value()); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(_ in 0..100 { black_box(map.first_key_value()); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
        }
        print_row(&format!("first_key_value (@{STEADY_SIZE})"), &mut samples);
        map.clear(&slab);
    }

    println!();

    // ── CHURN ─────────────────────────────────────────────────────────
    println!("CHURN (remove+insert pair, {BATCH_READ} unrolled ops/sample)");
    println!("---");
    {
        let mut map: BTree<u64, u64, B> = BTree::new();
        let mut keys: Vec<u64> = (0..STEADY_SIZE).map(|_| rng.next()).collect();
        for &k in &keys {
            map.try_insert(&slab, k, k).unwrap();
        }
        let mut samples = Vec::with_capacity(SAMPLES);
        let mut offset = 0usize;
        for _ in 0..WARMUP {
            let base = offset % keys.len();
            let old_batch: [u64; BATCH_READ] =
                std::array::from_fn(|i| keys[(base + i) % keys.len()]);
            let new_batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            seq!(I in 0..100 {
                map.remove(&slab, &old_batch[I]);
                map.try_insert(&slab, new_batch[I], new_batch[I]).unwrap();
            });
            for i in 0..BATCH_READ {
                keys[(base + i) % STEADY_SIZE] = new_batch[i];
            }
            offset += BATCH_READ;
        }
        offset = 0;
        for _ in 0..SAMPLES {
            let base = offset % keys.len();
            let old_batch: [u64; BATCH_READ] =
                std::array::from_fn(|i| keys[(base + i) % keys.len()]);
            let new_batch: [u64; BATCH_READ] = std::array::from_fn(|_| rng.next());
            let s = rdtsc_start();
            seq!(I in 0..100 {
                map.remove(&slab, &old_batch[I]);
                map.try_insert(&slab, new_batch[I], new_batch[I]).unwrap();
            });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH_READ as u64);
            for i in 0..BATCH_READ {
                keys[(base + i) % STEADY_SIZE] = new_batch[i];
            }
            offset += BATCH_READ;
        }
        print_row(&format!("churn (@{STEADY_SIZE})"), &mut samples);
        map.clear(&slab);
    }
}
