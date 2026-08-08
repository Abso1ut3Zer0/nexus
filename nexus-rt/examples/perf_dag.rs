//! DAG pipeline dispatch latency benchmark.
//!
//! Run asm inspection:
//! ```bash
//! cargo asm -p nexus-rt --example perf_dag perf_dag::probe_dag_linear_3
//! cargo asm -p nexus-rt --example perf_dag perf_dag::probe_dag_diamond
//! ```
//!
//! Run benchmark:
//! ```bash
//! taskset -c 0 cargo run --release -p nexus-rt --example perf_dag
//! ```

use std::hint::black_box;

use nexus_rt::dag::DagBuilder;
use nexus_rt::{Handler, PipelineBuilder, Res, ResMut, WorldBuilder, new_resource};

new_resource!(ResU32(u32));

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

fn bench_batched<F: FnMut()>(name: &str, mut f: F) -> (u64, u64, u64) {
    for _ in 0..WARMUP {
        f();
    }
    let mut samples = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            f();
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
// DAG node functions — trivial work to isolate dispatch overhead
// =============================================================================

fn root_mul2(x: u32) -> u32 {
    x.wrapping_mul(2)
}

#[allow(clippy::trivially_copy_pass_by_ref)]
fn add_one(val: &u32) -> u32 {
    val.wrapping_add(1)
}

#[allow(clippy::trivially_copy_pass_by_ref)]
fn mul3(val: &u32) -> u32 {
    val.wrapping_mul(3)
}

#[allow(clippy::needless_pass_by_value, clippy::trivially_copy_pass_by_ref)]
fn sink_store(mut out: ResMut<ResU32>, val: &u32) {
    out.0 = *val;
}

#[allow(clippy::needless_pass_by_value, clippy::trivially_copy_pass_by_ref)]
fn sink_add(mut out: ResMut<ResU32>, val: &u32) {
    out.0 = out.0.wrapping_add(*val);
}

#[allow(clippy::trivially_copy_pass_by_ref)]
fn merge2_add(a: &u32, b: &u32) -> u32 {
    a.wrapping_add(*b)
}

#[allow(clippy::needless_pass_by_value, clippy::trivially_copy_pass_by_ref)]
fn merge2_add_sink(mut out: ResMut<ResU32>, a: &u32, b: &u32) {
    out.0 = a.wrapping_add(*b);
}

// Pipeline comparison steps (by value)
fn pipe_mul2(x: u32) -> u32 {
    x.wrapping_mul(2)
}

fn pipe_add1(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[allow(clippy::needless_pass_by_value)]
fn pipe_sink(mut out: ResMut<ResU32>, x: u32) {
    out.0 = x;
}

// World-accessing DAG node
#[allow(clippy::needless_pass_by_value, clippy::trivially_copy_pass_by_ref)]
fn scale_by_res(factor: Res<ResU32>, val: &u32) -> u32 {
    val.wrapping_mul(factor.0)
}

// =============================================================================
// Codegen probes
// =============================================================================

/// DAG linear 3 — monomorphized, zero vtable.
#[inline(never)]
pub fn probe_dag_linear_3(p: &mut impl Handler<u32>, world: &mut nexus_rt::World, input: u32) {
    p.run(world, input);
}

/// DAG diamond — monomorphized, zero vtable.
#[inline(never)]
pub fn probe_dag_diamond(p: &mut impl Handler<u32>, world: &mut nexus_rt::World, input: u32) {
    p.run(world, input);
}

/// Equivalent linear Pipeline (monomorphized, zero vtable).
#[inline(never)]
pub fn probe_pipeline_linear_3(
    p: &mut nexus_rt::PipelineChain<u32, (), impl nexus_rt::ChainCall<u32, Out = ()>>,
    world: &mut nexus_rt::World,
    input: u32,
) {
    p.run(world, input);
}

// =============================================================================
// DAG topology builders
// =============================================================================

/// DAG linear 3: root → add_one → sink.
fn build_linear_3(
    reg: &nexus_rt::Registry,
) -> nexus_rt::Dag<impl nexus_rt::ChainCall<u32, Out = ()> + Send + use<>> {
    DagBuilder::<u32>::new()
        .root(root_mul2, reg)
        .then(add_one, reg)
        .then(sink_store, reg)
        .build()
}

/// DAG linear 5: root → add_one × 3 → sink.
fn build_linear_5(
    reg: &nexus_rt::Registry,
) -> nexus_rt::Dag<impl nexus_rt::ChainCall<u32, Out = ()> + Send + use<>> {
    DagBuilder::<u32>::new()
        .root(root_mul2, reg)
        .then(add_one, reg)
        .then(add_one, reg)
        .then(add_one, reg)
        .then(sink_store, reg)
        .build()
}

/// DAG diamond-2: root → [a, b] → merge → sink.
fn build_diamond_2(
    reg: &nexus_rt::Registry,
) -> nexus_rt::Dag<impl nexus_rt::ChainCall<u32, Out = ()> + Send + use<>> {
    DagBuilder::<u32>::new()
        .root(root_mul2, reg)
        .fork()
        .arm(|a| a.then(add_one, reg))
        .arm(|b| b.then(mul3, reg))
        .merge(merge2_add, reg)
        .then(sink_store, reg)
        .build()
}

/// DAG fan-out 2: root → [sink, sink].
fn build_fan_out_2(
    reg: &nexus_rt::Registry,
) -> nexus_rt::Dag<impl nexus_rt::ChainCall<u32, Out = ()> + Send + use<>> {
    DagBuilder::<u32>::new()
        .root(root_mul2, reg)
        .fork()
        .arm(|a| a.then(sink_store, reg))
        .arm(|b| b.then(sink_add, reg))
        .join()
        .build()
}

/// DAG complex: root → [a: add_one → add_one, b: mul3] → merge → sink.
fn build_complex(
    reg: &nexus_rt::Registry,
) -> nexus_rt::Dag<impl nexus_rt::ChainCall<u32, Out = ()> + Send + use<>> {
    DagBuilder::<u32>::new()
        .root(root_mul2, reg)
        .fork()
        .arm(|a| a.then(add_one, reg).then(add_one, reg))
        .arm(|b| b.then(mul3, reg))
        .merge(merge2_add, reg)
        .then(sink_store, reg)
        .build()
}

/// DAG complex+Res: root → scale → [a, b] → merge → sink.
fn build_complex_res(
    reg: &nexus_rt::Registry,
) -> nexus_rt::Dag<impl nexus_rt::ChainCall<u32, Out = ()> + Send + use<>> {
    DagBuilder::<u32>::new()
        .root(root_mul2, reg)
        .then(scale_by_res, reg)
        .fork()
        .arm(|a| a.then(add_one, reg))
        .arm(|b| b.then(mul3, reg))
        .merge(merge2_add_sink, reg)
        .build()
}

// =============================================================================
// Main — benchmark
// =============================================================================

fn main() {
    println!("DAG PIPELINE DISPATCH LATENCY BENCHMARK");
    println!("=======================================\n");
    println!("Iterations: {ITERATIONS}, Warmup: {WARMUP}, Batch: {BATCH}");
    println!("All times in CPU cycles\n");

    let mut wb = WorldBuilder::new();
    wb.register(ResU32(0));
    let mut world = wb.build();

    // -- Build all DAGs and pipelines upfront (reg borrows world immutably) --

    let reg = world.registry();

    let mut dag_lin3 = build_linear_3(reg);
    let mut dag_lin5 = build_linear_5(reg);
    let mut dag_dia2 = build_diamond_2(reg);
    let mut dag_fan2 = build_fan_out_2(reg);
    let mut dag_complex = build_complex(reg);
    let mut dag_complex_res = build_complex_res(reg);

    let mut dag_dyn_lin3: Box<dyn Handler<u32>> = Box::new(build_linear_3(reg));
    let mut dag_dyn_dia2: Box<dyn Handler<u32>> = Box::new(build_diamond_2(reg));

    let mut pipe3 = PipelineBuilder::<u32>::new()
        .then(pipe_mul2, reg)
        .then(pipe_add1, reg)
        .then(pipe_sink, reg);

    let mut pipe5 = PipelineBuilder::<u32>::new()
        .then(pipe_mul2, reg)
        .then(pipe_add1, reg)
        .then(pipe_add1, reg)
        .then(pipe_add1, reg)
        .then(pipe_sink, reg);

    let mut pipe3_boxed = PipelineBuilder::<u32>::new()
        .then(pipe_mul2, reg)
        .then(pipe_add1, reg)
        .then(pipe_sink, reg)
        .build();

    // Probe DAGs (for cargo-asm, built separately)
    let mut probe_lin3 = build_linear_3(reg);
    let mut probe_dia2 = build_diamond_2(reg);
    let mut probe_pipe = PipelineBuilder::<u32>::new()
        .then(pipe_mul2, reg)
        .then(pipe_add1, reg)
        .then(pipe_sink, reg);

    // reg goes dead here — world can be borrowed mutably below.

    // -- Benchmarks --

    let mut input = 1u32;

    print_header("DAG (monomorphized, zero vtable)");

    bench_batched("linear 3 stages", || {
        input = input.wrapping_add(1);
        dag_lin3.run(&mut world, black_box(input));
    });
    bench_batched("linear 5 stages", || {
        input = input.wrapping_add(1);
        dag_lin5.run(&mut world, black_box(input));
    });
    bench_batched("diamond fan=2 (5 stages)", || {
        input = input.wrapping_add(1);
        dag_dia2.run(&mut world, black_box(input));
    });
    bench_batched("fan-out 2 (join)", || {
        input = input.wrapping_add(1);
        dag_fan2.run(&mut world, black_box(input));
    });
    bench_batched("complex (fan+linear+merge)", || {
        input = input.wrapping_add(1);
        dag_complex.run(&mut world, black_box(input));
    });
    bench_batched("complex+Res<T> (Param fetch)", || {
        input = input.wrapping_add(1);
        dag_complex_res.run(&mut world, black_box(input));
    });

    println!();
    print_header("Dyn Dispatch (Box<dyn Handler<u32>>)");

    bench_batched("linear 3 via Box<dyn Handler>", || {
        input = input.wrapping_add(1);
        dag_dyn_lin3.run(&mut world, black_box(input));
    });
    bench_batched("diamond-2 via Box<dyn Handler>", || {
        input = input.wrapping_add(1);
        dag_dyn_dia2.run(&mut world, black_box(input));
    });

    println!();
    print_header("Pipeline Comparison (monomorphized baseline)");

    bench_batched("pipeline 3-stage (monomorphized)", || {
        input = input.wrapping_add(1);
        pipe3.run(&mut world, black_box(input));
    });
    bench_batched("pipeline 5-stage (monomorphized)", || {
        input = input.wrapping_add(1);
        pipe5.run(&mut world, black_box(input));
    });
    bench_batched("pipeline 3-stage (boxed dyn)", || {
        input = input.wrapping_add(1);
        pipe3_boxed.run(&mut world, black_box(input));
    });

    // -- Codegen probes (exercised, not timed) --

    probe_dag_linear_3(&mut probe_lin3, &mut world, black_box(42));
    probe_dag_diamond(&mut probe_dia2, &mut world, black_box(42));
    probe_pipeline_linear_3(&mut probe_pipe, &mut world, black_box(42));

    println!();
}
