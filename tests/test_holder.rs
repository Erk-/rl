extern crate hikari;

use hikari::Holder;
use std::time::Duration;
use std::thread;

#[test]
fn test_remaining() {
    let mut holder = Holder::default();
    let duration = Duration::from_secs(1);
    assert_eq!(holder.remaining(&1, &duration), 1);

    holder.take(&1, &duration);
    assert_eq!(holder.remaining(&1, &duration), 0);
    holder.take(&1, &duration);
    assert_eq!(holder.remaining(&1, &duration), 0);
}

#[test]
fn test_take() {
    let mut holder = Holder::default();
    let duration = Duration::from_secs(1);
    let result = holder.take(&1, &duration);
    assert!(result.is_none());
    let result = holder.take(&1, &duration).expect("holder tickets not maxed");
    assert!(result <= Duration::from_secs(1));
}

#[test]
fn test_behaviour_refresh() {
    let mut holder = Holder::default();
    let duration = Duration::from_secs(1);
    holder.take(&1, &duration);
    assert_eq!(holder.remaining(&1, &duration), 0);
    thread::sleep(holder.take(&1, &duration).unwrap());
    assert_eq!(holder.remaining(&1, &duration), 1);
}
