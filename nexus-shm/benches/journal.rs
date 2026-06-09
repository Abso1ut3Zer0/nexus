use std::hint::black_box;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use nexus_shm::{FixHeader, Journal, JournalConfig, MapHints};

fn cfg(segment_size: usize) -> JournalConfig {
    JournalConfig {
        segment_size,
        hints: MapHints::default(),
    }
}

fn cleanup(base: &std::path::Path) {
    for i in 0..64u64 {
        let mut p = base.as_os_str().to_owned();
        p.push(format!(".{i}"));
        let _ = std::fs::remove_file(std::path::PathBuf::from(p));
    }
}

fn bench_write(c: &mut Criterion) {
    let base = std::env::temp_dir().join(format!("nexus-journal-bench-w-{}", std::process::id()));
    cleanup(&base);

    let (mut w, _r) = Journal::<FixHeader>::open(&base, cfg(1 << 31)).unwrap();
    let payload = [0u8; 32];
    let mut seq = 0u64;

    c.benchmark_group("journal")
        .bench_function("try_claim_commit", |b| {
            b.iter(|| {
                seq += 1;
                let mut claim = w
                    .try_claim(
                        FixHeader {
                            seq,
                            timestamp: seq,
                        },
                        payload.len(),
                    )
                    .unwrap();
                claim.as_mut_slice().copy_from_slice(&payload);
                claim.commit();
            });
        });

    drop((w, _r));
    cleanup(&base);
}

fn bench_read(c: &mut Criterion) {
    let base = std::env::temp_dir().join(format!("nexus-journal-bench-r-{}", std::process::id()));
    cleanup(&base);

    const N: u64 = 1000;
    {
        let (mut w, _r) = Journal::<FixHeader>::open(&base, cfg(1 << 20)).unwrap();
        let payload = [0u8; 32];
        for seq in 1..=N {
            let mut claim = w
                .try_claim(
                    FixHeader {
                        seq,
                        timestamp: seq,
                    },
                    payload.len(),
                )
                .unwrap();
            claim.as_mut_slice().copy_from_slice(&payload);
            claim.commit();
        }
    }

    let mut group = c.benchmark_group("journal");
    group.throughput(Throughput::Elements(N));
    group.bench_function("next_record_drain", |b| {
        b.iter_batched(
            || Journal::<FixHeader>::open(&base, cfg(1 << 20)).unwrap(),
            |(w, mut r)| {
                while let Some(rec) = r.next_record().unwrap() {
                    black_box(rec.payload());
                }
                drop((w, r));
            },
            BatchSize::PerIteration,
        );
    });
    group.finish();

    cleanup(&base);
}

criterion_group!(benches, bench_write, bench_read);
criterion_main!(benches);
