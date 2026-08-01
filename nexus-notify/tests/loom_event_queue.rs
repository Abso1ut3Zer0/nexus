#![cfg(loom)]

use loom::thread;
use nexus_notify::{Events, Token, event_queue};

#[test]
fn notify_poll_roundtrip() {
    loom::model(|| {
        let (notifier, poller) = event_queue(4);
        let mut events = Events::with_capacity(4);

        let handle = thread::spawn(move || {
            notifier.notify(Token::new(1)).unwrap();
        });

        handle.join().unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.as_slice()[0].index(), 1);
    });
}

#[test]
fn conflation() {
    loom::model(|| {
        let (notifier, poller) = event_queue(4);
        let mut events = Events::with_capacity(4);

        let n2 = notifier.clone();
        let handle = thread::spawn(move || {
            n2.notify(Token::new(0)).unwrap();
        });

        notifier.notify(Token::new(0)).unwrap();
        handle.join().unwrap();

        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.as_slice()[0].index(), 0);
    });
}

#[test]
fn multi_producer_different_tokens() {
    loom::model(|| {
        let (notifier, poller) = event_queue(4);
        let mut events = Events::with_capacity(4);

        let n2 = notifier.clone();
        let h1 = thread::spawn(move || {
            notifier.notify(Token::new(0)).unwrap();
        });
        let h2 = thread::spawn(move || {
            n2.notify(Token::new(1)).unwrap();
        });

        h1.join().unwrap();
        h2.join().unwrap();

        poller.poll(&mut events);
        assert_eq!(events.len(), 2);

        let mut indices: Vec<usize> = events.iter().map(|t| t.index()).collect();
        indices.sort();
        assert_eq!(indices, vec![0, 1]);
    });
}

#[test]
fn re_notification_after_poll() {
    loom::model(|| {
        let (notifier, poller) = event_queue(4);
        let mut events = Events::with_capacity(4);

        notifier.notify(Token::new(2)).unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        events.drain().for_each(drop);

        let handle = thread::spawn(move || {
            notifier.notify(Token::new(2)).unwrap();
        });

        handle.join().unwrap();
        poller.poll(&mut events);
        assert_eq!(events.len(), 1);
        assert_eq!(events.as_slice()[0].index(), 2);
    });
}

#[test]
fn concurrent_notify_and_poll() {
    loom::model(|| {
        let (notifier, poller) = event_queue(4);

        let handle = thread::spawn(move || {
            notifier.notify(Token::new(0)).unwrap();
            notifier.notify(Token::new(1)).unwrap();
        });

        let mut events = Events::with_capacity(4);
        poller.poll(&mut events);
        let first_poll = events.len();
        events.drain().for_each(drop);

        handle.join().unwrap();

        poller.poll(&mut events);
        let second_poll = events.len();

        assert_eq!(first_poll + second_poll, 2);
    });
}
