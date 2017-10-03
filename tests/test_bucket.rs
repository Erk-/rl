extern crate hikari;

use hikari::{Bucket, Holder};
use std::time::{Duration, Instant};

fn bucket() -> Bucket<i32> {
    Bucket::new(Duration::from_secs(2), 1)
}

#[test]
fn test_generate() {
    let mut bucket = bucket();
    assert!(!bucket.has(&1));

    bucket.generate(1);
    assert!(bucket.has(&1));
}

#[test]
fn test_has() {
    let mut bucket = bucket();
    assert!(!bucket.has(&1));

    bucket.generate(1);
    assert!(bucket.has(&1));

    bucket.remove(&1);
    assert!(!bucket.has(&1));
}

#[test]
fn test_insert() {
    let mut bucket = bucket();
    assert!(!bucket.has(&1));
    bucket.insert(1, Holder::default());
    assert!(bucket.has(&1));
    bucket.take(1);

    let value = bucket.insert(1, Holder::default());
    assert_eq!(value.unwrap().tickets_taken, 1);
}

#[test]
fn test_remaining() {
    let mut bucket = bucket();
    assert!(bucket.remaining(&1).is_none());
    bucket.generate(1);
    assert_eq!(bucket.remaining(&1), Some(1));

    bucket.take(1);
    assert_eq!(bucket.remaining(&1), Some(0));
}

#[test]
fn test_remove() {
    let mut bucket = bucket();
    assert!(bucket.remove(&1).is_none());
    bucket.generate(1);
    assert!(bucket.has(&1));
    assert!(bucket.remove(&1).is_some());
    assert!(!bucket.has(&1));
}

#[test]
fn test_set_tickets() {
    let mut bucket = bucket();
    bucket.generate(1);
    assert_eq!(bucket.remaining(&1), Some(1));
    bucket.take(1);
    bucket.set_tickets(3);
    assert_eq!(bucket.remaining(&1), Some(2));
}

#[test]
fn test_take() {
    let mut bucket = bucket();
    bucket.take(1);
    assert_eq!(bucket.remaining(&1), Some(0));
}

#[test]
fn test_take_nonblocking() {
    let mut bucket = bucket();
    assert!(bucket.take_nonblocking(1).is_none());
    assert!(bucket.take_nonblocking(1).is_some());
}

#[test]
fn test_behaviour_blocking() {
    let mut bucket = bucket();
    bucket.take(1);

    let before = Instant::now();
    bucket.take(1);
    assert!(before.elapsed() > Duration::from_secs(1));
    assert!(before.elapsed() < Duration::from_secs(3));
}

#[test]
fn test_nonblocking_duration() {
    let mut bucket = bucket();
    bucket.take(1);
    let duration = bucket.take_nonblocking(1).expect("holder ticketed?");
    assert!(duration < Duration::from_secs(2));
    assert!(duration > Duration::from_secs(1));
}
