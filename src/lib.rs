//! [![ci-badge][]][ci] [![license-badge][]][license] [![docs-badge][]][docs] [![rust badge]][rust link]
//!
//! A simple-to-use ratelimit bucket, containing unique holders associated to
//! the bucket's settings for use with multiple unique clients.
//!
//! # Installation
//!
//! This library requires at least Rust 1.15.0.
//!
//! Add the following to your `Cargo.toml` file:
//!
//! ```toml
//! [dependencies]
//! rl = "~0.1"
//! ```
//!
//! # Examples
//!
//! Using the default in-memory backend, create a new [`Bucket`] with a refresh
//! time of 1000 milliseconds and 2 tickets allotted to each [`Holder`] and
//! _attempt_ to take 3 tickets from a holder, determining if the action would
//! have blocked the thread:
//!
//! ```rust
//! # extern crate rl;
//! #
//! # use std::error::Error;
//! #
//! # fn try_main() -> Result<(), Box<Error>> {
//! #
//! use rl::Bucket;
//! use std::time::Duration;
//!
//! // This is simply the identifier used for holder keys.
//! let id = 77u64;
//!
//! let mut bucket = Bucket::new(Duration::from_millis(1000), 2);
//!
//! // At this point, the bucket does not contain a holder for the ID, so
//! // attempting to retrieve the remaining amount will return None:
//! assert!(bucket.remaining(&id)?.is_none());
//!
//! // First, take a single ticket. This will create the holder due to it not
//! // existing, and then take a ticket. Since the limit is 2, the holder now
//! // has 1 ticket remaining.
//! bucket.take(id);
//! assert_eq!(bucket.remaining(&id)?, Some(1));
//!
//! // Take another, leaving it with 0 since 1000ms has not passed yet and the
//! // holder would not replenish yet.
//! bucket.take(id);
//! assert_eq!(bucket.remaining(&id)?, Some(0));
//!
//! // Try to take another ticket in a nonblocking fashion, asserting that the
//! // current thread _would_ block if we didn't explicitly use a nonblocking
//! // method.
//! assert!(bucket.take_nb(id)?.is_some());
//! #     Ok(())
//! # }
//! #
//! # fn main() {
//! #     try_main().unwrap();
//! # }
//! ```
//!
//! [`Bucket`]: struct.Bucket.html
//! [`Holder`]: struct.Holder.html
//! [ci]: https://travis-ci.org/rusty-crates/rl.rs
//! [ci-badge]: https://img.shields.io/travis/rusty-crates/rl.svg?style=flat-square
//! [docs]: https://docs.rs/rl
//! [docs-badge]: https://img.shields.io/badge/docs-online-5023dd.svg?style=flat-square
//! [license]: https://opensource.org/licenses/ISC
//! [license-badge]: https://img.shields.io/badge/license-ISC-blue.svg?style=flat-square
//! [rust badge]: https://img.shields.io/badge/rust-1.15+-93450a.svg?style=flat-square
//! [rust link]: https://blog.rust-lang.org/2017/02/02/Rust-1.15.html
#![deny(missing_docs)]

#[cfg(feature = "futures")]
extern crate futures;
#[cfg(feature = "futures-timer")]
extern crate futures_timer;

pub mod backend;

mod bucket;
mod holder;

pub use bucket::Bucket;
pub use holder::Holder;
