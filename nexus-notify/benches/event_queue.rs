use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use nexus_notify::{Events, Token, event_channel, event_queue};

// ============================================================================
// Notify
// ============================================================================

fn bench_notify(c: &mut Criterion) {
    let mut group = c.benchmark_group("notify");
    group.throughput(Throughput::Elements(1));

    group.bench_function("new", |b| {
        let (notifier, poller) = event_queue(4096);
        let token = Token::new(0);
        let mut events = Events::with_capacity(4096);
        b.iter(|| {
            poller.poll(&mut events);
            events.drain().for_each(drop);
            notifier.notify(token).ok();
        });
    });

    group.bench_function("conflated", |b| {
        let (notifier, _poller) = event_queue(4096);
        let token = Token::new(0);
        notifier.notify(token).ok();
        b.iter(|| {
            notifier.notify(token).ok();
        });
    });

    group.finish();
}

// ============================================================================
// Poll
// ============================================================================

fn shuffled_tokens(n: usize, cap: usize) -> Vec<Token> {
    let stride = cap / n;
    let mut tokens: Vec<Token> = (0..n).map(|i| Token::new(i * stride)).collect();
    let mut rng = 12345u64;
    for i in (1..tokens.len()).rev() {
        rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        let j = (rng as usize) % (i + 1);
        tokens.swap(i, j);
    }
    tokens
}

fn bench_poll(c: &mut Criterion) {
    let mut group = c.benchmark_group("poll");

    group.bench_function("empty", |b| {
        let (_, poller) = event_queue(4096);
        let mut events = Events::with_capacity(4096);
        b.iter(|| {
            poller.poll(&mut events);
        });
    });

    for n in [1, 8, 32, 128, 256] {
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::new("N", n), &n, |b, &n| {
            let (notifier, poller) = event_queue(4096);
            let tokens = shuffled_tokens(n, 4096);
            let mut events = Events::with_capacity(4096);
            b.iter(|| {
                for t in &tokens {
                    notifier.notify(*t).ok();
                }
                poller.poll(&mut events);
                events.clear();
            });
        });
    }

    group.finish();
}

// ============================================================================
// Poll limit
// ============================================================================

fn bench_poll_limit(c: &mut Criterion) {
    let mut group = c.benchmark_group("poll_limit");

    for limit in [32, 64, 128, 256] {
        group.throughput(Throughput::Elements(limit as u64));
        group.bench_with_input(BenchmarkId::new("limit", limit), &limit, |b, &limit| {
            let (notifier, poller) = event_queue(4096);
            let tokens: Vec<Token> = (0..4096).map(Token::new).collect();
            let mut events = Events::with_capacity(4096);
            b.iter(|| {
                for t in &tokens {
                    notifier.notify(*t).ok();
                }
                poller.poll_limit(&mut events, limit);
                events.clear();
                // Drain rest
                poller.poll(&mut events);
                events.clear();
            });
        });
    }

    group.finish();
}

// ============================================================================
// Channel recv wakeup latency
// ============================================================================

fn bench_channel_recv_wake(c: &mut Criterion) {
    let mut group = c.benchmark_group("channel");
    group.throughput(Throughput::Elements(1));

    // Measure non-blocking path (data already queued)
    group.bench_function("recv_immediate", |b| {
        let (sender, receiver) = event_channel(64);
        let token = Token::new(0);
        let mut events = Events::with_capacity(64);
        b.iter(|| {
            sender.notify(token).ok();
            receiver.recv(&mut events);
            events.drain().for_each(drop);
        });
    });

    // Measure try_recv (non-blocking poll through channel)
    group.bench_function("try_recv", |b| {
        let (sender, receiver) = event_channel(64);
        let token = Token::new(0);
        let mut events = Events::with_capacity(64);
        b.iter(|| {
            sender.notify(token).ok();
            receiver.try_recv(&mut events);
            events.drain().for_each(drop);
        });
    });

    group.finish();
}

// ============================================================================
// Main
// ============================================================================

criterion_group!(
    benches,
    bench_notify,
    bench_poll,
    bench_poll_limit,
    bench_channel_recv_wake
);
criterion_main!(benches);
