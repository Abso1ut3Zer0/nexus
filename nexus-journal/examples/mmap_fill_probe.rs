//! Probe: does the page-cross tail appear on a FRESH sequential fill, or only
//! under sustained write volume?
//!
//! Isolates the effect from the journal's reuse/rotation machinery: create one
//! fresh file-backed `MAP_SHARED` mapping, optionally prefault it (as the
//! conductor does), then sequentially write fixed-size records down it exactly
//! once. Sweeping `SIZE` shows the tail is governed by total write volume (the
//! kernel's dirty-page / writeback / block-allocation machinery), not by reuse.
//!
//! Env: `SIZE`(67108864) `PREFAULT`(1) `REC`(72)
//! Put it on real disk: `TMPDIR=<ext4 dir> taskset -c 0,2 ./mmap_fill_probe`
//!
//! x86_64 only: the cycle timing uses `rdtsc`/`rdtscp`.

#[cfg(target_arch = "x86_64")]
fn main() {
    imp::run();
}

#[cfg(not(target_arch = "x86_64"))]
fn main() {
    eprintln!("mmap_fill_probe requires x86_64 (rdtsc cycle timing)");
}

#[cfg(target_arch = "x86_64")]
mod imp {
    use std::num::NonZeroUsize;

    use hdrhistogram::Histogram;
    use nexus_platform::MappedFile;

    const PAGE: usize = 4096;

    #[inline(always)]
    fn rdtsc_start() -> u64 {
        // SAFETY: module is x86_64-gated; these intrinsics always exist here.
        unsafe {
            core::arch::x86_64::_mm_lfence();
            core::arch::x86_64::_rdtsc()
        }
    }

    #[inline(always)]
    fn rdtsc_end() -> u64 {
        // SAFETY: module is x86_64-gated; these intrinsics always exist here.
        unsafe {
            let mut aux = 0u32;
            let t = core::arch::x86_64::__rdtscp(&raw mut aux);
            core::arch::x86_64::_mm_lfence();
            t
        }
    }

    fn env_usize(key: &str, default: usize) -> usize {
        std::env::var(key)
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(default)
    }

    fn report(name: &str, h: &Histogram<u64>) {
        if h.is_empty() {
            println!("  {name:<12} (no samples)");
            return;
        }
        println!(
            "  {name:<12} n={:<9} p50={:<5} p90={:<5} p99={:<7} p99.9={:<8} p99.99={:<9} max={}",
            h.len(),
            h.value_at_quantile(0.50),
            h.value_at_quantile(0.90),
            h.value_at_quantile(0.99),
            h.value_at_quantile(0.999),
            h.value_at_quantile(0.9999),
            h.max(),
        );
    }

    pub fn run() {
        let size = env_usize("SIZE", 64 * 1024 * 1024);
        let prefault = env_usize("PREFAULT", 1) != 0;
        let rec = env_usize("REC", 72);

        let dir = std::env::temp_dir();
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join(format!("nexus-mmap-probe-{}", std::process::id()));
        let _ = std::fs::remove_file(&path);

        let mf = MappedFile::create(&path, NonZeroUsize::new(size).unwrap()).unwrap();
        let base = mf.as_ptr();

        if prefault {
            // Simulate the conductor prefault: write-touch every page up front.
            // SAFETY: base covers `size` writable bytes, sole owner.
            unsafe { std::ptr::write_bytes(base, 0, size) };
        }

        let payload = vec![0xABu8; rec];
        let mut h_normal = Histogram::<u64>::new(3).unwrap();
        let mut h_page = Histogram::<u64>::new(3).unwrap();

        let mut off = 0usize;
        while off + rec <= size {
            let cross = off / PAGE != (off + rec - 1) / PAGE;
            let start = rdtsc_start();
            // SAFETY: off + rec <= size; both buffers valid and non-overlapping.
            unsafe {
                std::ptr::copy_nonoverlapping(payload.as_ptr(), base.add(off), rec);
            }
            let end = rdtsc_end();
            let cyc = end.wrapping_sub(start);
            if cross {
                h_page.record(cyc).ok();
            } else {
                h_normal.record(cyc).ok();
            }
            off += rec;
        }

        println!("--- fresh sequential mmap fill (cycles) ---");
        println!(
            "  size={size}B rec={rec}B prefault={prefault} pages={}",
            size / PAGE
        );
        report("normal", &h_normal);
        report("page-cross", &h_page);

        drop(mf);
        let _ = std::fs::remove_file(&path);
    }
}
