//! Trait and provided implementations defining a "backend" for a [`Bucket`].
//!
//! Backends define how a bucket stores [`Holder`]s and other information, such
//! as the refresh time.
//!
//! By default a single implementation is provided, [`InMemoryBackend`], which
//! stores buckets in in-process memory.
//!
//! # Examples
//!
//! Say that you want to store your bucket in redis. You can create a struct
//! containing your redis connection, and then implement [`Backend`]'s trait
//! methods on it: [`refresh_time`] to retrieve the current refresh time,
//! [`set_tickets`] to update the number of tickets assigned to each holder,
//! [`has`] to check if a bucket has a holder by ID, etc. All of these
//! synchronous methods must be defined.
//!
//! If you have the `futures` feature flag enabled, then methods suffixed with
//! `f` are also present. By default, these are default implementations that
//! wrap their synchronous equivalents in leaf futures.
//!
//! [`Backend`]: trait.Backend.html
//! [`Bucket`]: ../struct.Bucket.html
//! [`Holder`]: ../struct.Holder.html
//! [`InMemoryBackend`]: in_memory/index.html
//! [`has`]: trait.Backend.html#tymethod.has
//! [`refresh_time`]: trait.Backend.html#tymethod.refresh_time
//! [`set_tickets`]: trait.Backend.html#tymethod.set_tickets

pub mod in_memory;

pub use self::in_memory::InMemoryBackend;

use crate::Holder;
use std::{
    fmt::Debug,
    hash::Hash,
    time::Duration,
};

#[cfg(feature = "futures")]
use futures::{Future, future};

/// Backend trait which can be implemented and given to [`Bucket::stateful`].
///
/// Refer to the [module-level documentation] for more information.
///
/// [`Bucket::stateful`]: ../struct.Bucket.html#method.stateful
/// [module-level documentation]: ./index.html
pub trait Backend<T: Eq + Hash, U: Clone + 'static = ()> {
    /// The error type for the backend in use.
    type Error: Debug + 'static;

    /// Method to retrieve the refresh time used for holders.
    ///
    /// Refer to [`Bucket::refresh_time`] for more information.
    ///
    /// [`Bucket::refresh_time`]: struct.Bucket.html#method.refresh_time
    fn refresh_time(&mut self) -> Result<Option<Duration>, Self::Error>;

    /// Method to asynchronously retrieve the refresh time used for holders.
    ///
    /// Refer to [`Bucket::refresh_timef`] for more information.
    ///
    /// [`Bucket::refresh_timef`]: struct.Bucket.html#method.refresh_timef
    #[cfg(feature = "futures")]
    #[inline]
    fn refresh_timef(&mut self) -> Box<Future<Item = Option<Duration>, Error = Self::Error>> {
        Box::new(future::result(self.refresh_time()))
    }

    /// Method to retrieve the number of tickets used for holders.
    ///
    /// Refer to [`Bucket::tickets`] for more information.
    ///
    /// [`Bucket::tickets`]: struct.Bucket.html#method.tickets
    fn tickets(&mut self) -> Result<Option<u32>, Self::Error>;

    /// Method to asynchronously retrieve the number of tickets used for holders.
    ///
    /// Refer to [`Bucket::ticketsf`] for more information.
    ///
    /// [`Bucket::ticketsf`]: struct.Bucket.html#method.ticketsf
    #[cfg(feature = "futures")]
    #[inline]
    fn ticketsf(&mut self) -> Box<Future<Item = Option<u32>, Error = Self::Error>> {
        Box::new(future::result(self.tickets()))
    }

    /// Method to set the refresh time to use for holders.
    ///
    /// Refer to [`Bucket::set_refresh_time`] for more information.
    ///
    /// [`Bucket::set_refresh_time`]: ../struct.Bucket.html#method.set_refresh_time
    fn set_refresh_time(
        &mut self,
        new_refresh_time: Duration,
    ) -> Result<Option<Duration>, Self::Error>;

    /// Method to asynchronously set the refresh time to use for holders.
    ///
    /// Refer to [`Bucket::set_refresh_timef`] for more information.
    ///
    /// [`Bucket::set_refresh_timef`]: ../struct.Bucket.html#method.set_refresh_timef
    #[cfg(feature = "futures")]
    #[inline]
    fn set_refresh_timef(
        &mut self,
        new_refresh_time: Duration,
    ) -> Box<Future<Item = Option<Duration>, Error = Self::Error>> {
        Box::new(future::result(self.set_refresh_time(new_refresh_time)))
    }

    /// Method to set the number of tickets to use for holders.
    ///
    /// Refer to [`Bucket::set_tickets`] for more information.
    ///
    /// [`Bucket::set_tickets`]: ../struct.Bucket.html#method.set_tickets
    fn set_tickets(&mut self, new_tickets: u32) -> Result<Option<u32>, Self::Error>;

    /// Method to asynchronously set the number of tickets to use for holders.
    ///
    /// Refer to [`Bucket::set_ticketsf`] for more information.
    ///
    /// [`Bucket::set_ticketsf`]: ../struct.Bucket.html#method.set_ticketsf
    #[cfg(feature = "futures")]
    #[inline]
    fn set_ticketsf(
        &mut self,
        new_tickets: u32,
    ) -> Box<Future<Item = Option<u32>, Error = Self::Error>> {
        Box::new(future::result(self.set_tickets(new_tickets)))
    }

    /// Method to generate a default state for a holder by ID.
    ///
    /// Refer to [`Bucket::generate`] for more information.
    ///
    /// [`Bucket::generate`]: ../struct.Bucket.html#method.generate
    fn generate(&mut self, holder_id: T, state: U) -> Result<Option<Holder<U>>, Self::Error>;

    /// Method to asynchronously generate a default state for a holder by ID.
    ///
    /// Refer to [`Bucket::generatef`] for more information.
    ///
    /// [`Bucket::generatef`]: ../struct.Bucket.html#method.generatef
    #[cfg(feature = "futures")]
    #[inline]
    fn generatef(
        &mut self,
        holder_id: T,
        state: U,
    ) -> Box<Future<Item = Option<Holder<U>>, Error = Self::Error>> {
        Box::new(future::result(self.generate(holder_id, state)))
    }

    /// Method to check if a holder exists by ID.
    ///
    /// Refer to [`Bucket::has`] for more information.
    ///
    /// [`Bucket::has`]: ../struct.Bucket.html#method.has
    fn has(&mut self, holder_id: &T) -> Result<bool, Self::Error>;

    /// Method to asynchronously check if a holder exists by ID.
    ///
    /// Refer to [`Bucket::hasf`] for more information.
    ///
    /// [`Bucket::hasf`]: ../struct.Bucket.html#method.hasf
    #[cfg(feature = "futures")]
    #[inline]
    fn hasf(
        &mut self,
        holder_id: &T,
    ) -> Box<Future<Item = bool, Error = Self::Error>> {
        Box::new(future::result(self.has(holder_id)))
    }

    /// Method to insert a holder by ID.
    ///
    /// Refer to [`Bucket::insert`] for more information.
    ///
    /// [`Bucket::insert`]: ../struct.Bucket.html#method.insert
    fn insert(&mut self, holder_id: T, holder: Holder<U>) -> Result<Option<Holder<U>>, Self::Error>;

    /// Method to asynchronously insert a holder by ID.
    ///
    /// Refer to [`Bucket::insertf`] for more information.
    ///
    /// [`Bucket::insertf`]: ../struct.Bucket.html#method.insertf
    #[cfg(feature = "futures")]
    #[inline]
    fn insertf(
        &mut self,
        holder_id: T,
        holder: Holder<U>,
    ) -> Box<Future<Item = Option<Holder<U>>, Error = Self::Error>> {
        Box::new(future::result(self.insert(holder_id, holder)))
    }

    /// Method to retrieve the number of remaining tickets for a holder by ID.
    ///
    /// Refer to [`Bucket::remaining`] for more information.
    ///
    /// [`Bucket::remaining`]: ../struct.Bucket.html#method.remaining
    fn remaining(&mut self, holder_id: &T) -> Result<Option<u32>, Self::Error>;

    /// Method to asynchronously retrieve the number of remaining tickets for a
    /// holder by ID.
    ///
    /// Refer to [`Bucket::remainingf`] for more information.
    ///
    /// [`Bucket::remainingf`]: ../struct.Bucket.html#method.remainingf
    #[cfg(feature = "futures")]
    #[inline]
    fn remainingf(
        &mut self,
        holder_id: &T,
    ) -> Box<Future<Item = Option<u32>, Error = Self::Error>> {
        Box::new(future::result(self.remaining(holder_id)))
    }

    /// Method to remove a holder by ID.
    ///
    /// Refer to [`Bucket::remove`] for more information.
    ///
    /// [`Bucket::remove`]: ../struct.Bucket.html#method.remove
    fn remove(&mut self, holder_id: &T) -> Result<Option<Holder<U>>, Self::Error>;

    /// Method to asynchronously remove a holder by ID.
    ///
    /// Refer to [`Bucket::removef`] for more information.
    ///
    /// [`Bucket::removef`]: ../struct.Bucket.html#method.removef
    #[cfg(feature = "futures")]
    #[inline]
    fn removef(
        &mut self,
        holder_id: &T,
    ) -> Box<Future<Item = Option<Holder<U>>, Error = Self::Error>> {
        Box::new(future::result(self.remove(holder_id)))
    }

    /// Method to take a ticket from a holder by ID, inserting the default state
    /// if it does not exist.
    ///
    /// Refer to [`Bucket::take`] for more information.
    ///
    /// [`Bucket::take`]: ../struct.Bucket.html#method.take
    fn take(&mut self, holder_id: T, state: &U) -> Result<Option<Duration>, Self::Error>;

    /// Method to asynchronously take a ticket from a holder by ID, inserting
    /// the default state if it does not exist.
    ///
    /// Refer to [`Bucket::takef`] for more information.
    ///
    /// [`Bucket::takef`]: ../struct.Bucket.html#method.takef
    #[cfg(feature = "futures")]
    #[inline]
    fn takef(
        &mut self,
        holder_id: T,
        state: &U,
    ) -> Box<Future<Item = Option<Duration>, Error = Self::Error>> {
        Box::new(future::result(self.take(holder_id, state)))
    }
}
