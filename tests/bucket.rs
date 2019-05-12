extern crate rl;

use rl::{
    backend::InMemoryBackend,
    Bucket,
};
use std::time::{Duration, Instant};

fn bucket() -> Bucket<i32, (), InMemoryBackend<i32, ()>> {
    Bucket::new(Duration::from_secs(2), 1)
}

#[ignore]
#[test]
fn test_behaviour_blocking() {
    let mut bucket = bucket();
    bucket.take(1).unwrap();

    let before = Instant::now();
    bucket.take(1).unwrap();
    assert!(before.elapsed() > Duration::from_secs(1));
    assert!(before.elapsed() < Duration::from_secs(3));
}
