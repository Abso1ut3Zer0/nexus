//! Fetch dispatch prototype benchmark.
//!
//! Measures the cost of fetching component references via different strategies
//! to inform the Components container design. All strategies perform the same
//! work: fetch two "components", mutate one using the other, return a value.
//!
//! Run with:
//! ```bash
//! taskset -c 0 cargo run --release -p nexus-rt --example perf_fetch
//! ```

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::hint::black_box;

// =============================================================================
// Bench infrastructure (inline — no shared utils crate yet)
// =============================================================================

const ITERATIONS: usize = 100_000;
const WARMUP: usize = 10_000;
const BATCH: u64 = 100;

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe {
        let mut aux = 0u32;
        let tsc = core::arch::x86_64::__rdtscp(&raw mut aux);
        core::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn bench_batched<F: FnMut() -> u64>(name: &str, mut f: F) -> (u64, u64, u64) {
    for _ in 0..WARMUP {
        black_box(f());
    }
    let mut samples = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            black_box(f());
        }
        let end = rdtsc_end();
        samples.push(end.wrapping_sub(start) / BATCH);
    }
    samples.sort_unstable();
    let p50 = percentile(&samples, 50.0);
    let p99 = percentile(&samples, 99.0);
    let p999 = percentile(&samples, 99.9);
    println!("{:<44} {:>8} {:>8} {:>8}", name, p50, p99, p999);
    (p50, p99, p999)
}

fn print_header(title: &str) {
    println!("=== {} ===\n", title);
    println!(
        "{:<44} {:>8} {:>8} {:>8}",
        "Operation", "p50", "p99", "p999"
    );
    println!("{}", "-".repeat(72));
}

// =============================================================================
// Component types (realistic cache footprint)
// =============================================================================

/// 64 bytes — one cache line. Simulates a small component like a price cache
/// entry or a set of counters.
#[repr(align(64))]
struct PriceCache {
    values: [u64; 8],
}

/// 64 bytes — one cache line. Simulates read-only config/state.
#[repr(align(64))]
struct VenueState {
    values: [u64; 8],
}

/// Padding component to make the container realistic (not just 2 slots).
#[derive(Default)]
#[repr(align(64))]
struct Padding {
    _data: [u64; 8],
}

impl Default for PriceCache {
    fn default() -> Self {
        Self { values: [1; 8] }
    }
}

impl Default for VenueState {
    fn default() -> Self {
        Self { values: [2; 8] }
    }
}

// =============================================================================
// Strategy 1: Direct struct field access (Path 3 baseline)
// =============================================================================

struct DirectWorld {
    prices: PriceCache,
    _pad1: Padding,
    _pad2: Padding,
    _pad3: Padding,
    venues: VenueState,
    _pad4: Padding,
    _pad5: Padding,
    _pad6: Padding,
}

#[inline(never)]
fn system_direct(world: &mut DirectWorld) -> u64 {
    world.prices.values[0] = world.prices.values[0].wrapping_add(world.venues.values[0]);
    world.prices.values[0]
}

// =============================================================================
// Strategy 2: Vec<Box<T>> indexed by pre-resolved ComponentId
// =============================================================================

struct VecContainer {
    slots: Vec<Box<dyn std::any::Any>>,
}

impl VecContainer {
    fn new() -> Self {
        let slots: Vec<Box<dyn std::any::Any>> = vec![
            Box::new(PriceCache::default()), // 0
            Box::new(Padding::default()),    // 1
            Box::new(Padding::default()),    // 2
            Box::new(Padding::default()),    // 3
            Box::new(VenueState::default()), // 4
            Box::new(Padding::default()),    // 5
            Box::new(Padding::default()),    // 6
            Box::new(Padding::default()),    // 7
        ];
        Self { slots }
    }
}

#[inline(never)]
fn system_vec_downcast(container: &mut VecContainer) -> u64 {
    // Runtime downcast — what a naive Fetch impl would do
    let prices_ptr = container.slots[0].downcast_mut::<PriceCache>().unwrap() as *mut PriceCache;
    let venues_ptr = container.slots[4].downcast_ref::<VenueState>().unwrap() as *const VenueState;
    // SAFETY: pointers come from successful downcast_mut/downcast_ref on non-overlapping slots.
    let prices = unsafe { &mut *prices_ptr };
    // SAFETY: same as above.
    let venues = unsafe { &*venues_ptr };
    prices.values[0] = prices.values[0].wrapping_add(venues.values[0]);
    prices.values[0]
}

// =============================================================================
// Strategy 3: Vec<*mut u8> with pre-resolved indices (no downcast)
// =============================================================================

struct ErasedContainer {
    /// Type-erased pointers to Box-allocated components.
    /// Indices are assigned at registration, resolved at system init.
    ptrs: Vec<*mut u8>,
    /// Keep boxes alive.
    _storage: Vec<Box<dyn std::any::Any>>,
}

impl ErasedContainer {
    fn new() -> Self {
        let mut storage: Vec<Box<dyn std::any::Any>> = vec![
            Box::new(PriceCache::default()),
            Box::new(Padding::default()),
            Box::new(Padding::default()),
            Box::new(Padding::default()),
            Box::new(VenueState::default()),
            Box::new(Padding::default()),
            Box::new(Padding::default()),
            Box::new(Padding::default()),
        ];

        let ptrs = storage
            .iter_mut()
            .map(|b| &mut **b as *mut dyn std::any::Any as *mut u8)
            .collect();

        Self {
            ptrs,
            _storage: storage,
        }
    }
}

#[inline(never)]
fn system_vec_erased(ptrs: &[*mut u8], price_id: usize, venue_id: usize) -> u64 {
    // SAFETY: pointers in ptrs were initialized from valid Box allocations; price_id != venue_id.
    let prices = unsafe { &mut *(ptrs[price_id] as *mut PriceCache) };
    // SAFETY: same as above.
    let venues = unsafe { &*(ptrs[venue_id] as *const VenueState) };
    prices.values[0] = prices.values[0].wrapping_add(venues.values[0]);
    prices.values[0]
}

// =============================================================================
// Strategy 3b: Vec<*mut u8> with get_unchecked (no bounds check)
//
// Same as Strategy 3 but indices are validated at build time, so dispatch
// skips bounds checks entirely.
// =============================================================================

#[inline(never)]
fn system_vec_unchecked(ptrs: &[*mut u8], price_id: usize, venue_id: usize) -> u64 {
    // SAFETY: indices validated at build time; pointers are valid Box allocations; price_id != venue_id.
    unsafe {
        let prices = &mut *(*ptrs.get_unchecked(price_id) as *mut PriceCache);
        let venues = &*(*ptrs.get_unchecked(venue_id) as *const VenueState);
        prices.values[0] = prices.values[0].wrapping_add(venues.values[0]);
        prices.values[0]
    }
}

// =============================================================================
// Strategy 4: Cached raw pointers (resolved once at build time)
// =============================================================================

struct CachedFetch {
    prices: *mut PriceCache,
    venues: *const VenueState,
}

#[inline(never)]
fn system_cached(cached: &CachedFetch) -> u64 {
    // SAFETY: prices and venues are valid non-null pointers from Box allocations; non-overlapping.
    let prices = unsafe { &mut *cached.prices };
    // SAFETY: same as above.
    let venues = unsafe { &*cached.venues };
    prices.values[0] = prices.values[0].wrapping_add(venues.values[0]);
    prices.values[0]
}

// =============================================================================
// Strategy 5: Cached pointers behind Box (stable address, one extra deref)
// =============================================================================

struct BoxedCachedFetch {
    inner: Box<CachedFetch>,
}

#[inline(never)]
fn system_boxed_cached(cached: &BoxedCachedFetch) -> u64 {
    // SAFETY: prices and venues are valid non-null pointers from Box allocations; non-overlapping.
    let prices = unsafe { &mut *cached.inner.prices };
    // SAFETY: same as above.
    let venues = unsafe { &*cached.inner.venues };
    prices.values[0] = prices.values[0].wrapping_add(venues.values[0]);
    prices.values[0]
}

// =============================================================================
// Strategy 6a: HashMap<TypeId, *mut u8> + trait object dispatch
//
// Components registered into a HashMap keyed by TypeId. At build() time,
// each system resolves its pointers via TypeId lookup and caches them.
// Dispatch goes through Box<dyn System> vtable.
// =============================================================================

struct HashTypeMap {
    ptrs: HashMap<TypeId, *mut u8>,
    storage: Vec<Box<dyn Any>>,
}

impl HashTypeMap {
    fn new() -> Self {
        Self {
            ptrs: HashMap::new(),
            storage: Vec::new(),
        }
    }

    fn insert<T: 'static>(&mut self, value: T) {
        let mut boxed = Box::new(value);
        let ptr = &raw mut *boxed as *mut u8;
        self.ptrs.insert(TypeId::of::<T>(), ptr);
        self.storage.push(boxed);
    }

    fn get<T: 'static>(&self) -> *mut u8 {
        *self.ptrs.get(&TypeId::of::<T>()).unwrap()
    }
}

// =============================================================================
// Strategy 6b: Vec<*mut u8> with dense ComponentId + trait object dispatch
//
// Components registered sequentially, assigned dense indices (0, 1, 2, ...).
// At build() time, systems resolve by index. Same dispatch as 6a.
// =============================================================================

struct DenseTypeMap {
    ptrs: Vec<*mut u8>,
    storage: Vec<Box<dyn Any>>,
}

impl DenseTypeMap {
    fn new() -> Self {
        Self {
            ptrs: Vec::new(),
            storage: Vec::new(),
        }
    }

    /// Returns the assigned ComponentId (index).
    fn insert<T: 'static>(&mut self, value: T) -> usize {
        let mut boxed = Box::new(value);
        let ptr = &raw mut *boxed as *mut u8;
        let id = self.ptrs.len();
        self.ptrs.push(ptr);
        self.storage.push(boxed);
        id
    }
}

// Common trait — the framework dispatches through this vtable.
trait System {
    fn run(&mut self) -> u64;
}

// 6a: system caches erased ptrs resolved from HashMap<TypeId>
struct HashResolvedSystem {
    prices: *mut u8,
    venues: *mut u8,
}

impl HashResolvedSystem {
    fn build(map: &HashTypeMap) -> Self {
        Self {
            prices: map.get::<PriceCache>(),
            venues: map.get::<VenueState>(),
        }
    }
}

impl System for HashResolvedSystem {
    #[inline(never)]
    fn run(&mut self) -> u64 {
        // SAFETY: pointers resolved from valid Box allocations at build time; non-overlapping.
        let prices = unsafe { &mut *(self.prices as *mut PriceCache) };
        // SAFETY: same as above.
        let venues = unsafe { &*(self.venues as *const VenueState) };
        prices.values[0] = prices.values[0].wrapping_add(venues.values[0]);
        prices.values[0]
    }
}

// 6b: system caches erased ptrs resolved from Vec by dense index (pre-pointer-ResourceId)
struct DenseResolvedSystem {
    prices: *mut u8,
    venues: *mut u8,
}

impl DenseResolvedSystem {
    fn build(map: &DenseTypeMap, price_id: usize, venue_id: usize) -> Self {
        Self {
            prices: map.ptrs[price_id],
            venues: map.ptrs[venue_id],
        }
    }
}

impl System for DenseResolvedSystem {
    #[inline(never)]
    fn run(&mut self) -> u64 {
        // SAFETY: pointers resolved from valid Box allocations at build time; non-overlapping.
        let prices = unsafe { &mut *(self.prices as *mut PriceCache) };
        // SAFETY: same as above.
        let venues = unsafe { &*(self.venues as *const VenueState) };
        prices.values[0] = prices.values[0].wrapping_add(venues.values[0]);
        prices.values[0]
    }
}

// =============================================================================

fn main() {
    println!("FETCH DISPATCH PROTOTYPE BENCHMARK");
    println!("==================================\n");
    println!("Iterations: {ITERATIONS}, Warmup: {WARMUP}, Batch: {BATCH}");
    println!("All times in CPU cycles\n");

    // ---- Strategy 1: Direct ----
    print_header("DIRECT STRUCT FIELD ACCESS (Path 3 baseline)");
    let mut world = DirectWorld {
        prices: PriceCache::default(),
        _pad1: Padding::default(),
        _pad2: Padding::default(),
        _pad3: Padding::default(),
        venues: VenueState::default(),
        _pad4: Padding::default(),
        _pad5: Padding::default(),
        _pad6: Padding::default(),
    };
    bench_batched("direct field access", || {
        system_direct(black_box(&mut world))
    });

    // ---- Strategy 2: Vec<Box<dyn Any>> with downcast ----
    println!();
    print_header("VEC<BOX<DYN ANY>> + DOWNCAST");
    let mut vec_container = VecContainer::new();
    bench_batched("downcast_mut + downcast_ref", || {
        system_vec_downcast(black_box(&mut vec_container))
    });

    // ---- Strategy 3: Vec<*mut u8> pre-resolved index ----
    println!();
    print_header("VEC<*MUT U8> PRE-RESOLVED INDEX");
    let erased = ErasedContainer::new();
    let price_id = 0usize;
    let venue_id = 4usize;
    bench_batched("erased ptr + index (bounds checked)", || {
        system_vec_erased(
            black_box(&erased.ptrs),
            black_box(price_id),
            black_box(venue_id),
        )
    });

    // ---- Strategy 3b: Vec<*mut u8> with get_unchecked ----
    println!();
    print_header("VEC<*MUT U8> UNCHECKED (validated at build)");
    bench_batched("erased ptr + index (unchecked)", || {
        system_vec_unchecked(
            black_box(&erased.ptrs),
            black_box(price_id),
            black_box(venue_id),
        )
    });

    // ---- Strategy 4: Cached raw pointers ----
    println!();
    print_header("CACHED RAW POINTERS (resolved at build)");
    // Resolve pointers from the erased container (simulating build-time resolution)
    let cached = CachedFetch {
        prices: erased.ptrs[0] as *mut PriceCache,
        venues: erased.ptrs[4] as *const VenueState,
    };
    bench_batched("cached ptr fetch", || system_cached(black_box(&cached)));

    // ---- Strategy 5: Boxed cached pointers ----
    println!();
    print_header("BOXED CACHED POINTERS");
    let boxed_cached = BoxedCachedFetch {
        inner: Box::new(CachedFetch {
            prices: erased.ptrs[0] as *mut PriceCache,
            venues: erased.ptrs[4] as *const VenueState,
        }),
    };
    bench_batched("boxed cached ptr fetch", || {
        system_boxed_cached(black_box(&boxed_cached))
    });

    // ---- Strategy 6a: HashMap<TypeId> resolve + trait dispatch ----
    println!();
    print_header("HASHMAP<TYPEID> + TRAIT DISPATCH");
    let mut hash_map = HashTypeMap::new();
    hash_map.insert(PriceCache::default());
    hash_map.insert(Padding::default());
    hash_map.insert(VenueState::default());
    let mut system_6a: Box<dyn System> = Box::new(HashResolvedSystem::build(&hash_map));
    bench_batched("typeid hashmap + trait dispatch", || {
        black_box(system_6a.run())
    });

    // ---- Strategy 6b: Dense Vec resolve + trait dispatch ----
    println!();
    print_header("DENSE VEC + TRAIT DISPATCH");
    let mut dense_map = DenseTypeMap::new();
    let dense_price_id = dense_map.insert(PriceCache::default());
    let _dense_pad_id = dense_map.insert(Padding::default());
    let dense_venue_id = dense_map.insert(VenueState::default());
    let mut system_6b: Box<dyn System> = Box::new(DenseResolvedSystem::build(
        &dense_map,
        dense_price_id,
        dense_venue_id,
    ));
    bench_batched("dense vec + trait dispatch", || black_box(system_6b.run()));

    println!();
}
