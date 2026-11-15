# Patterns

## Producer-consumer pair

The simplest usage — one thread produces, one consumes, the channel
applies backpressure.

```rust
use std::thread;
use nexus_channel::channel;

#[derive(Clone, Copy)]
struct MarketEvent { ts: u64, px: f64, qty: f64 }

let (tx, rx) = channel::<MarketEvent>(4096);

let producer = thread::spawn(move || {
    for i in 0..1_000_000u64 {
        let evt = MarketEvent { ts: i, px: 100.0, qty: 1.0 };
        if tx.send(evt).is_err() {
            break;  // consumer dropped
        }
    }
});

let consumer = thread::spawn(move || {
    while let Ok(evt) = rx.recv() {
        process(evt);
    }
});

producer.join().unwrap();
consumer.join().unwrap();
# fn process(_: MarketEvent) {}
```

When the consumer falls behind, the ring buffer fills, the producer
blocks in `send`, and natural backpressure keeps memory bounded.

## Pipeline stage

Stages communicate via chained channels. Each stage is `recv → process →
send`. Backpressure propagates from the slowest stage all the way to the
source.

```rust
use std::thread;
use nexus_channel::channel;

let (raw_tx, raw_rx) = channel::<Vec<u8>>(1024);
let (parsed_tx, parsed_rx) = channel::<ParsedEvent>(1024);
let (decorated_tx, decorated_rx) = channel::<DecoratedEvent>(1024);
# struct ParsedEvent; struct DecoratedEvent;
# fn parse(_: Vec<u8>) -> ParsedEvent { ParsedEvent }
# fn decorate(_: ParsedEvent) -> DecoratedEvent { DecoratedEvent }
# fn write(_: DecoratedEvent) {}

thread::spawn(move || {
    while let Ok(bytes) = raw_rx.recv() {
        let _ = parsed_tx.send(parse(bytes));
    }
});

thread::spawn(move || {
    while let Ok(evt) = parsed_rx.recv() {
        let _ = decorated_tx.send(decorate(evt));
    }
});

thread::spawn(move || {
    while let Ok(evt) = decorated_rx.recv() {
        write(evt);
    }
});
```

Pick capacities for each stage proportional to the expected burst size
and the stage's processing latency. Bigger queues hide jitter; smaller
queues apply backpressure sooner.

## Event-loop handoff

A blocking IO thread hands events to a polling event loop. The IO thread
can block in `send` on burst (that's fine, it has nothing else to do),
and the event loop uses `try_recv` to drain without blocking its main
tick.

```rust
use nexus_channel::{channel, TryRecvError};

let (tx, rx) = channel::<Event>(8192);
# #[derive(Clone, Copy)] struct Event;
# fn handle(_: Event) {}

// IO thread — blocks in send when the event loop is busy
std::thread::spawn(move || {
    loop {
        let evt = read_from_socket();
        if tx.send(evt).is_err() { break; }
    }
});

// Event loop — drains without blocking
fn tick(rx: &nexus_channel::Receiver<Event>) {
    // Drain up to some budget to keep tail latency bounded
    for _ in 0..256 {
        match rx.try_recv() {
            Ok(evt) => handle(evt),
            Err(TryRecvError::Empty) => break,
            Err(TryRecvError::Disconnected) => return,
        }
    }
}
# fn read_from_socket() -> Event { Event }
```

## Timed worker with shutdown

A worker polls for work with a deadline, handling both "do some work" and
"time to exit" cleanly.

```rust
use std::time::Duration;
use nexus_channel::{channel, RecvTimeoutError};

let (tx, rx) = channel::<WorkItem>(256);
# #[derive(Clone, Copy)] struct WorkItem;
# fn run(_: WorkItem) {}
# fn periodic() {}

std::thread::spawn(move || {
    loop {
        match rx.recv_timeout(Duration::from_millis(100)) {
            Ok(item) => run(item),
            Err(RecvTimeoutError::Timeout) => periodic(),
            Err(RecvTimeoutError::Disconnected) => break,  // clean shutdown
        }
    }
});

// Later, main thread:
drop(tx);  // worker finishes its current item and exits
```

Dropping the sender is the shutdown signal. Workers naturally drain and
exit without any shutdown-flag bookkeeping.

## High-throughput configuration

For a pipeline where latency matters more than CPU:

```rust
use nexus_channel::channel_with_config;

// Burn CPU on the backoff before parking — lower tail latency
let (tx, rx) = channel_with_config::<Event>(4096, 64);
# #[derive(Clone, Copy)] struct Event;
```

Pair with CPU pinning (e.g. `taskset -c 0,2`) and hyperthreading disabled
on the critical cores. See [`docs/benchmarking.md`](../../docs/benchmarking.md)
for the full benchmarking setup.
