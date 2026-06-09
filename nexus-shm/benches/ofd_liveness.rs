//! Cost of a Tier-2 liveness query (`F_OFD_GETLK`) against a live owner.
//!
//! Pin to a physical core with turbo disabled for stable numbers:
//!
//! ```bash
//! echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! taskset -c 2 cargo bench -p nexus-shm --bench ofd_liveness
//! ```

use std::hint::black_box;

use criterion::{Criterion, criterion_group, criterion_main};
use nexus_shm::{Liveness, MapHints, Segment};

fn bench_peer_liveness(c: &mut Criterion) {
    let path = std::env::temp_dir().join(format!("nexus-shm-bench-{}", std::process::id()));
    let _ = std::fs::remove_file(&path);

    let owner = Segment::create(&path, 4096, MapHints::default()).unwrap();
    let peer = Segment::attach(&path, MapHints::default()).unwrap();
    assert_eq!(peer.peer_liveness(), Liveness::Alive);

    c.benchmark_group("ofd_liveness")
        .bench_function("peer_liveness_getlk", |b| {
            b.iter(|| black_box(black_box(&peer).peer_liveness()));
        });

    drop(owner);
    drop(peer);
    let _ = std::fs::remove_file(&path);
}

criterion_group!(benches, bench_peer_liveness);
criterion_main!(benches);
