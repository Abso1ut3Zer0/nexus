use nexus_notify::{Events, Token, event_queue};
use std::thread;

#[test]
fn two_thread_no_lost_tokens() {
    let (notifier, poller) = event_queue(64);
    let mut events = Events::with_capacity(64);

    let tokens: Vec<Token> = (0..64).map(Token::new).collect();

    let handle = thread::spawn(move || {
        for t in &tokens {
            notifier.notify(*t).unwrap();
        }
    });

    handle.join().unwrap();
    poller.poll(&mut events);

    let mut indices: Vec<usize> = events.iter().map(Token::index).collect();
    indices.sort_unstable();
    let expected: Vec<usize> = (0..64).collect();
    assert_eq!(indices, expected);
}

#[test]
fn mpsc_two_producers() {
    let (notifier, poller) = event_queue(128);
    let mut events = Events::with_capacity(128);

    let evens: Vec<Token> = (0..64).map(|i| Token::new(i * 2)).collect();
    let odds: Vec<Token> = (0..64).map(|i| Token::new(i * 2 + 1)).collect();

    let n1 = notifier.clone();
    let n2 = notifier;

    let h1 = thread::spawn(move || {
        for t in &evens {
            n1.notify(*t).unwrap();
        }
    });

    let h2 = thread::spawn(move || {
        for t in &odds {
            n2.notify(*t).unwrap();
        }
    });

    h1.join().unwrap();
    h2.join().unwrap();

    poller.poll(&mut events);

    let mut indices: Vec<usize> = events.iter().map(Token::index).collect();
    indices.sort_unstable();
    let expected: Vec<usize> = (0..128).collect();
    assert_eq!(indices, expected);
}

#[test]
fn mpsc_same_token_conflation() {
    let (notifier, poller) = event_queue(64);
    let mut events = Events::with_capacity(64);
    let t = Token::new(0);

    let n1 = notifier.clone();
    let n2 = notifier;

    let h1 = thread::spawn(move || {
        for _ in 0..1000 {
            n1.notify(t).unwrap();
        }
    });

    let h2 = thread::spawn(move || {
        for _ in 0..1000 {
            n2.notify(t).unwrap();
        }
    });

    h1.join().unwrap();
    h2.join().unwrap();

    poller.poll(&mut events);
    assert_eq!(events.len(), 1);
    assert_eq!(events.iter().next().unwrap().index(), 0);
}

#[test]
fn stress_no_lost_tokens() {
    const ROUNDS: usize = if cfg!(miri) { 100 } else { 10_000 };
    let (notifier, poller) = event_queue(64);
    let mut events = Events::with_capacity(64);

    let tokens: Vec<Token> = (0..8).map(Token::new).collect();

    let handle = thread::spawn(move || {
        for _ in 0..ROUNDS {
            for t in &tokens {
                notifier.notify(*t).unwrap();
            }
        }
    });

    let mut seen = [false; 8];

    while !handle.is_finished() {
        poller.poll(&mut events);
        for t in events.drain() {
            seen[t.index()] = true;
        }
    }

    handle.join().unwrap();

    poller.poll(&mut events);
    for t in events.drain() {
        seen[t.index()] = true;
    }

    assert!(seen.iter().all(|&s| s), "missed tokens: {:?}", seen);
}

#[test]
fn stress_poll_limit_fifo() {
    let (notifier, poller) = event_queue(64);
    let mut events = Events::with_capacity(64);

    for i in 0..20 {
        notifier.notify(Token::new(i)).unwrap();
    }

    let mut all_indices = Vec::new();
    for _ in 0..4 {
        poller.poll_limit(&mut events, 5);
        let chunk: Vec<usize> = events.drain().map(Token::index).collect();
        assert_eq!(chunk.len(), 5);
        all_indices.extend(chunk);
    }

    let expected: Vec<usize> = (0..20).collect();
    assert_eq!(all_indices, expected);
}

#[test]
fn large_capacity() {
    let (notifier, poller) = event_queue(4096);
    let mut events = Events::with_capacity(4096);

    for i in 0..4096 {
        notifier.notify(Token::new(i)).unwrap();
    }

    poller.poll(&mut events);

    let mut indices: Vec<usize> = events.iter().map(Token::index).collect();
    indices.sort_unstable();
    let expected: Vec<usize> = (0..4096).collect();
    assert_eq!(indices, expected);
}

#[test]
fn roundtrip_smoke() {
    let (n_fwd, p_fwd) = event_queue(64);
    let (n_rev, p_rev) = event_queue(64);
    let t_fwd = Token::new(0);
    let t_rev = Token::new(0);

    let worker = thread::spawn(move || {
        let mut events = Events::with_capacity(64);
        for _ in 0..100 {
            loop {
                p_fwd.poll(&mut events);
                if !events.is_empty() {
                    break;
                }
                std::hint::spin_loop();
            }
            events.drain().for_each(drop);
            n_rev.notify(t_rev).unwrap();
        }
    });

    let mut events = Events::with_capacity(64);
    for _ in 0..100 {
        n_fwd.notify(t_fwd).unwrap();
        loop {
            p_rev.poll(&mut events);
            if !events.is_empty() {
                break;
            }
            std::hint::spin_loop();
        }
        events.drain().for_each(drop);
    }

    worker.join().unwrap();
}
