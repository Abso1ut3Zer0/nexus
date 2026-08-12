# Overview

A timer wheel is a data structure for scheduling large numbers of timers
that mostly get cancelled before they fire. This is the dominant pattern in
network software (request timeouts, keepalives, retransmits) and trading
systems (order TTLs, heartbeats, stale-data deadlines).

## When to use a timer wheel

Use `nexus-timer` when:

- You schedule thousands of timers per second.
- Most timers are cancelled before firing (TCP retransmit is the canonical
  example — typically cancelled by the ACK).
- You want O(1) insert and cancel.
- You don't need precise firing time — "within one tick of the deadline"
  is fine.

Use a binary heap (e.g. `nexus_collections::Heap`) when:

- You have tens, not thousands, of timers.
- You want the next-deadline query to be O(1) rather than O(active slots).
- You need exact ordering by deadline.

Use `std::thread::sleep` or `tokio::time::sleep` when:

- You're scheduling a handful of one-shot delays.
- Timer overhead is not in your flame graph.

## The collect / rebalance design

A hierarchical wheel places a timer in a slot sized to how far away its
deadline is: coarse slots (wide time ranges) for distant deadlines, fine
slots (one tick) for near ones. The question is what to do as a timer's
deadline approaches and it no longer belongs in its coarse slot.

`nexus-timer` **rebalances**. As a timer nears its deadline it is moved down
to finer levels, so by the time it is ready it sits in a small, exact
fine-level slot. `poll` then simply **collects** the ready timers from those
fine slots — it never has to walk a fat coarse slot checking deadlines one at
a time:

```text
poll(now):        // collect
    for each active level:
        for each active slot whose earliest deadline <= now:
            collect entries with deadline <= now

rebalance(now):   // maintenance — separately, or folded into the poll
    for each coarse slot nearing its deadline:
        move its entries down to the finer level they now belong in
```

This is what keeps poll flat under load. The alternative — leave every entry
in its original coarse slot and check `deadline <= now` per entry on every
poll — makes poll proportional to how many entries share a due coarse slot,
i.e. roughly the population, not the number actually firing. That
O(population) tail is exactly what rebalancing removes.

Rebalancing is exposed three ways, so you choose where the maintenance runs:

- **`poll_and_rebalance`** folds collect + rebalance into one call — the simple
  default.
- **`max_rebalances_per_poll`** bounds how much rebalancing a single poll does,
  spreading a burst across polls (it never delays a fire).
- **`rebalance`** runs the maintenance on its own, so a latency-sensitive loop
  can `poll` cheaply on the hot path and `rebalance` during slack (for example,
  only when a poll comes back empty).

Timers always fire at their exact tick — rebalancing changes only *where* the
work happens, never *when* a timer fires.

## Default configuration

`Wheel::unbounded(chunk_capacity, now)` gives you the Linux-kernel default:

- 1 ms tick
- 64 slots per level
- 8× multiplier per level (`clk_shift = 3`)
- 7 levels
- Total range: ~4.7 hours

Customize via `WheelBuilder` if you need sub-ms resolution or a longer
range. See [wheel.md](wheel.md).
