extern crate rl;

use rl::Holder;
use std::{
    thread,
    time::Duration,
};

#[ignore]
#[test]
fn test_behaviour_refresh() {
    let mut holder = Holder::new(None, 0, ());
    let duration = Duration::from_secs(1);
    holder.take(1u32, &duration);
    assert_eq!(holder.remaining(1, &duration), 0);
    thread::sleep(holder.take(1, &duration).unwrap());
    assert_eq!(holder.remaining(1, &duration), 1);
}
