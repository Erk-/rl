use backend::{Backend, InMemoryBackend};
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::time::Duration;
use std::thread;
use Holder;

#[cfg(feature = "futures")]
use futures::future::{self, Future};
#[cfg(feature = "futures-timer")]
use futures_timer::Delay;

/// A synchronous instance defining the information for ticket holders, such as
/// the amount of time between a first ticket request and replenishment and the
/// number of tickets allocated to holders.
///
/// # Examples
///
/// Creating a bucket with a one second refresh time, 5 tickets each, and then
/// taking a ticket from two holders:
///
/// ```rust
/// # extern crate rl;
/// #
/// # use std::error::Error;
/// #
/// # fn try_main() -> Result<(), Box<Error>> {
/// #
/// use rl::Bucket;
/// use std::time::Duration;
///
/// let mut bucket = Bucket::new(Duration::from_secs(1), 5);
/// bucket.take(1)?; // `1` is the ID to take a ticket from
/// bucket.take(2)?;
/// #
/// #     Ok(())
/// # }
/// #
/// # fn main() {
/// #     try_main().unwrap();
/// # }
/// ```
///
/// [`Holder`]: struct.Holder.html
pub struct Bucket<T: Eq + Hash, U: Clone + 'static, V: Backend<T, U>> {
    backend: V,
    state: U,
    marker: PhantomData<T>,
    _nonexhaustive: (),
}

impl<T: Eq + Hash + 'static> Bucket<T, (), InMemoryBackend<T, ()>> {
    /// Creates a new instance of Bucket with the provided refresh time and
    /// ticket count.
    ///
    /// This produces holders with no state. If you need each holder to have
    /// some set of state (such as attached user data), use
    /// [`Bucket::stateful`].
    ///
    /// # Examples
    ///
    /// Creating a bucket with 10 tickets per holder, with a 5 second refresh
    /// time:
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(5), 10);
    ///
    /// // You can now, for example, take tickets from identifying holders.
    /// bucket.take("anything that implements Eq + Hash can be an id")?;
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    ///
    /// [`Bucket::stateful`]: #method.stateful
    pub fn new(refresh_time: Duration, tickets: u32) -> Self {
        Bucket {
            backend: InMemoryBackend::new(refresh_time, tickets),
            marker: PhantomData,
            state: (),
            _nonexhaustive: (),
        }
    }
}

impl<T: Eq + Hash, U: Clone + 'static, V: Backend<T, U>> Bucket<T, U, V> {
    /// Creates a new instance of Bucket with the provided refresh time, ticket
    /// count, and a default state for each [`Holder`].
    ///
    /// The provided state must implement the `Clone` trait, since new holders
    /// can be generated from the provided "default" state.
    ///
    /// # Examples
    ///
    /// Creating a bucket with 10 tickets per holder, with a 5 second refresh
    /// time, and a default State that can be later accessed:
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::backend::InMemoryBackend;
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// #[derive(Clone)]
    /// struct State {
    ///     bar: u64,
    /// }
    ///
    /// let backend = InMemoryBackend::new(Duration::from_secs(5), 10);
    /// let mut bucket = Bucket::stateful(backend, State {
    ///     bar: 1,
    /// });
    ///
    /// // Create a holder for a key and then get its state.
    /// bucket.take("foo")?;
    /// let holder = bucket.remove(&"foo")?.unwrap();
    /// assert_eq!(holder.state().bar, 1);
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    ///
    /// [`Holder`]: struct.Holder.html
    pub fn stateful(backend: V, state: U) -> Self {
        Bucket {
            backend,
            marker: PhantomData,
            state,
            _nonexhaustive: (),
        }
    }

    /// Returns the amount of time between holder refreshes.
    ///
    /// This is the amount of time in milliseconds between the first removal of
    /// a ticket for a holder and when the tickets available to the holder
    /// refreshes.
    ///
    /// **Note**: Due to the synchronous nature of this bucket, the value of the
    /// number of used tickets may not be accurate and will not automatically
    /// replenish in the future.
    ///
    /// # Examples
    ///
    /// Retrieve the refresh time that the backend has configured:
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let refresh_time = Duration::from_secs(2);
    /// let mut bucket: Bucket<i32, _, _> = Bucket::new(refresh_time, 1);
    ///
    /// assert_eq!(bucket.refresh_time()?, Some(refresh_time));
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `refresh_time` method of the backend
    /// implementation in use for why this can error.
    #[cfg_attr(feature = "futures", cold)]
    pub fn refresh_time(&mut self) -> Result<Option<Duration>, V::Error> {
        self.backend.refresh_time()
    }

    /// Returns a Future which resolves to the amount of time between holder
    /// refreshes.
    ///
    /// Refer to [`refresh_time`] for more information.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `refresh_timef` method of the backend
    /// implementation in use for why this can error.
    ///
    /// [`refresh_time`]: #method.refresh_time
    #[cfg(feature = "futures")]
    #[inline]
    pub fn refresh_timef(
        &mut self,
    ) -> Box<Future<Item = Option<Duration>, Error = V::Error>> {
        self.backend.refresh_timef()
    }

    /// Returns an immutable reference to the user-provided default state of
    /// each created holder.
    pub fn state(&self) -> &U {
        &self.state
    }

    /// Returns a mutable reference to the user-provided default state of each
    /// each created holder.
    ///
    /// Refer to [`state`] for more information.
    ///
    /// # Examples
    ///
    /// Modify the default state of newly created holders after creating the
    /// Bucket instance and an initial holder:
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::backend::InMemoryBackend;
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// #[derive(Clone)]
    /// struct State {
    ///     number: u64,
    /// }
    ///
    /// let id = 1u64;
    /// let second_id = 2u64;
    ///
    /// let backend = InMemoryBackend::new(Duration::from_secs(1), 2);
    /// let mut bucket = Bucket::stateful(backend, State {
    ///     number: 1,
    /// });
    ///
    /// // Take a ticket from ID 1.
    /// {
    ///     bucket.take(&id)?;
    /// }
    ///
    /// // Retrieve the Holder instance for the ticket and assert that the state
    /// // of the holder has a `number` of 1
    /// assert_eq!(bucket.holders()[&id].state().number, 1);
    ///
    /// // Now change the default state to have a number of 10:
    /// bucket.state_mut().number = 10;
    ///
    /// // Create a new Holder with ID 2 and assert that the state of the holder
    /// // has a number of 10
    /// bucket.take(&second_id)?;
    /// assert_eq!(bucket.holders()[&second_id].state().number, 10);
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    ///
    /// [`state`]: #method.state
    pub fn state_mut(&mut self) -> &mut U {
        &mut self.state
    }

    /// Returns an immutable reference to the maximum number of tickets allotted
    /// to each holder.
    #[cfg_attr(feature = "futures", cold)]
    #[inline]
    pub fn tickets(&mut self) -> Result<Option<u32>, V::Error> {
        self.backend.tickets()
    }

    /// Returns a Future which resolves to the maximum number of tickets
    /// allotted to each holder.
    ///
    /// Refer to [`tickets`] for more information.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `ticketsf` method of the backend
    /// implementation in use for why this can error.
    ///
    /// [`tickets`]: #method.tickets
    #[cfg(feature = "futures")]
    #[inline]
    pub fn ticketsf(
        &mut self,
    ) -> Box<Future<Item = Option<u32>, Error = V::Error>> {
        self.backend.ticketsf()
    }

    /// Inserts a default holder for an ID, returning the existing holder if one
    /// existed.
    ///
    /// Unlike [`take`], this does not mutate the holder (i.e. taking a ticket).
    ///
    /// # Examples
    ///
    /// Insert a default holder for the id `77`:
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 1);
    /// bucket.generate(77u64)?;
    ///
    /// assert!(bucket.has(&77u64)?);
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    ///
    /// [`take`]: #method.take
    #[cfg_attr(feature = "futures", cold)]
    #[inline]
    pub fn generate(
        &mut self,
        holder_id: T,
    ) -> Result<Option<Holder<U>>, V::Error> {
        let state = self.state.clone();

        self.backend.insert(holder_id, Holder::new(None, 0, state))
    }

    /// Returns a Future which inserts a default holder for an ID, resolving to
    /// the existing holder if one existed.
    ///
    /// Refer to [`generate`] for more information.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `generatef` method of the backend
    /// implementation in use for why this can error.
    ///
    /// [`generate`]: #method.generate
    #[cfg(feature = "futures")]
    #[inline]
    pub fn generatef(
        &mut self,
        holder_id: T,
    ) -> Box<Future<Item = Option<Holder<U>>, Error = V::Error>> {
        let state = self.state.clone();

        self.backend.insertf(holder_id, Holder::new(None, 0, state))
    }

    /// Whether the bucket contains an instance for the holder.
    ///
    /// # Examples
    ///
    /// Check that a fresh bucket does not originally have an instance for a
    /// holder until a ticket is taken:
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 1);
    /// assert!(!bucket.has(&"an id")?);
    ///
    /// // Take a ticket for the ID and then assert that it _does_ exist.
    /// bucket.take("an id")?;
    /// assert!(bucket.has(&"an id")?);
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// # }
    /// ```
    #[cfg_attr(feature = "futures", cold)]
    #[inline]
    pub fn has(&mut self, holder_id: &T) -> Result<bool, V::Error> {
        self.backend.has(holder_id)
    }

    /// Returns a Future which resolves to whether the backend has a holder with
    /// the given ID.
    ///
    /// Refer to [`has`] for more information.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `hasf` method of the backend
    /// implementation in use for why this can error.
    ///
    /// [`has`]: #method.has
    #[cfg(feature = "futures")]
    #[inline]
    pub fn hasf(
        &mut self,
        holder_id: &T,
    ) -> Box<Future<Item = bool, Error = V::Error>> {
        self.backend.hasf(holder_id)
    }

    /// Inserts an existing holder into the bucket.
    ///
    /// This is primarily useful for transferring holders between buckets.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::{Bucket, Holder};
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(5), 1);
    /// bucket.insert("an id", Holder::default())?;
    ///
    /// assert!(bucket.has(&"an id")?);
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    #[cfg_attr(feature = "futures", cold)]
    #[inline]
    pub fn insert(
        &mut self,
        holder_id: T,
        holder: Holder<U>,
    ) -> Result<Option<Holder<U>>, V::Error> {
        self.backend.insert(holder_id, holder)
    }

    /// Returns a Future which inserts an existing holder into the bucket and
    /// resolves to the existing holder, if it existed.
    ///
    /// Refer to [`insert`] for more information.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `insertf` method of the backend
    /// implementation in use for why this can error.
    ///
    /// [`insert`]: #method.insert
    #[cfg(feature = "futures")]
    #[inline]
    pub fn insertf(
        &mut self,
        holder_id: T,
        holder: Holder<U>,
    ) -> Box<Future<Item = Option<Holder<U>>, Error = V::Error>> {
        self.backend.insertf(holder_id, holder)
    }

    /// Calculates the number of remaining tickets in a holder.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let id = 77u64;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(5), 5);
    /// // Assert that retrieving the number of remaining tickets for a
    /// // nonexistent holder will return None.
    /// assert!(bucket.remaining(&id)?.is_none());
    ///
    /// // Assert that the bucket has 4 tickets remaining after taking a ticket.
    /// bucket.take(id)?;
    /// assert_eq!(bucket.remaining(&id).unwrap(), Some(4));
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    #[cfg_attr(feature = "futures", cold)]
    #[inline]
    pub fn remaining(
        &mut self,
        holder_id: &T,
    ) -> Result<Option<u32>, V::Error> {
        self.backend.remaining(holder_id)
    }

    /// Returns a Future which resolves to the number of remaining tickets for
    /// a holder, if it exists.
    ///
    /// Refer to [`remaining`] for more information.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `remainingf` method of the backend
    /// implementation in use for why this can error.
    ///
    /// [`remaining`]: #method.remaining
    #[cfg(feature = "futures")]
    #[inline]
    pub fn remainingf(
        &mut self,
        holder_id: &T,
    ) -> Box<Future<Item = Option<u32>, Error = V::Error>> {
        self.backend.remainingf(holder_id)
    }

    /// Attempts to remove a holder from the bucket, if one exists.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 5);
    ///
    /// // A holder identified by `"hello"` doesn't exist yet.
    /// assert!(bucket.remove(&"hello")?.is_none());
    ///
    /// // Make the previously mentioned bucket, then remove it.
    /// bucket.take("hello");
    /// assert!(bucket.remove(&"hello")?.is_some());
    ///
    /// // Verify it was removed:
    /// assert!(bucket.remove(&"hello")?.is_none());
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    #[cfg_attr(feature = "futures", cold)]
    #[inline]
    pub fn remove(
        &mut self,
        holder_id: &T,
    ) -> Result<Option<Holder<U>>, V::Error> {
        self.backend.remove(holder_id)
    }


    /// Returns a Future which attempts to remove a holder from the bucket, if
    /// one exists.
    ///
    /// Refer to [`remove`] for more information.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `remainingf` method of the backend
    /// implementation in use for why this can error.
    ///
    /// [`remove`]: #method.remove
    #[cfg(feature = "futures")]
    #[inline]
    pub fn removef(
        &mut self,
        holder_id: &T,
    ) -> Box<Future<Item = Option<Holder<U>>, Error = V::Error>> {
        self.backend.removef(holder_id)
    }

    /// Modifies the total number of tickets in the bucket.
    ///
    /// Holders will be aware of the change in ticket count.
    ///
    /// # Examples
    ///
    /// Creating a bucket with 5 tickets, taking 3 tickets from a holder, and
    /// then decreasing the ticket count to 2:
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 5);
    ///
    /// for _ in 0..3 {
    ///     bucket.take("hi")?;
    /// }
    ///
    /// assert_eq!(bucket.remaining(&"hi")?, Some(2));
    /// bucket.set_tickets(2)?;
    /// assert_eq!(bucket.remaining(&"hi")?, Some(0));
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    #[cfg_attr(feature = "futures", cold)]
    #[inline]
    pub fn set_tickets(
        &mut self,
        new_ticket_count: u32,
    ) -> Result<Option<u32>, V::Error> {
        self.backend.set_tickets(new_ticket_count)
    }


    /// Returns a Future which modifies the total number of tickets in the
    /// bucket.
    ///
    /// Refer to [`set_tickets`] for more information.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `remainingf` method of the backend
    /// implementation in use for why this can error.
    ///
    /// [`set_tickets`]: #method.set_tickets
    #[cfg(feature = "futures")]
    #[inline]
    pub fn set_ticketsf(
        &mut self,
        new_ticket_count: u32,
    ) -> Box<Future<Item = Option<u32>, Error = V::Error>> {
        self.backend.set_ticketsf(new_ticket_count)
    }

    /// Takes a ticket from a holder, creating the holder if it doesn't exist.
    ///
    /// # Examples
    ///
    /// Take a single ticket from a holder, asserting that a single ticket was
    /// removed:
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 2);
    /// bucket.take("test")?;
    ///
    /// assert_eq!(bucket.remaining(&"test")?, Some(1));
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    ///
    /// # Warnings
    ///
    /// If the holder has no tickets available, the thread will sleep until
    /// enough time has passed for the holder's tickets to refresh.
    ///
    /// To instead attempt to take a ticket (and failing) and obtain the
    /// duration that the thread would sleep, use [`take_nb`]. This can
    /// for example be wrapped in a Future.
    ///
    /// [`take_nb`]: #method.take_nb
    #[inline]
    pub fn take(&mut self, holder_id: T) -> Result<(), V::Error> {
        if let Some(duration) = self.take_nb(holder_id)? {
            thread::sleep(duration)
        }

        Ok(())
    }

    /// Attempts to take a ticket from a holder.
    ///
    /// Returns a leaf future if waiting is not required. Returns a future which
    /// sleeps if all tickets have been exhausted and have not yet been
    /// replenished.
    #[cfg(feature = "futures")]
    pub fn takef(
        &mut self,
        holder_id: T,
    ) -> Box<Future<Item = (), Error = ()>> {
        match self.take_nb(holder_id).unwrap() {
            Some(dur) => Box::new(Delay::new(dur).map_err(|_| ())),
            None => Box::new(future::ok(())),
        }
    }

    /// Attempts to take a ticket from a holder, returning the duration until
    /// the holder refreshes if all tickets have been used.
    ///
    /// # Examples
    ///
    /// Take a single ticket from a holder located in a bucket with a single
    /// ticket allocation, and assert that upon taking a second ticket some
    /// duration to wait is returned:
    ///
    /// ```rust
    /// # extern crate rl;
    /// #
    /// # use std::error::Error;
    /// #
    /// # fn try_main() -> Result<(), Box<Error>> {
    /// #
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(5), 1);
    /// bucket.take("test")?;
    ///
    /// // Assert that the holder's tickets are all used and that there is some
    /// // time until they replenish.
    /// assert!(bucket.take_nb("test")?.is_some());
    /// #
    /// #     Ok(())
    /// # }
    /// #
    /// # fn main() {
    /// #     try_main().unwrap();
    /// # }
    /// ```
    #[inline]
    pub fn take_nb(&mut self, holder_id: T) -> Result<Option<Duration>, V::Error> {
        self.backend.take(holder_id, &self.state)
    }

    /// Returns a Future which attempts to take a ticket from a holder,
    /// returning the duration until the holder refreshes if all tickets have
    /// been used.
    ///
    /// Refer to [`take_nb`] for more information.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for the `remainingf` method of the backend
    /// implementation in use for why this can error.
    ///
    /// [`take_nb`]: #method.take_nb
    #[cfg(feature = "futures")]
    pub fn take_nbf(
        &mut self,
        holder_id: T,
    ) -> Box<Future<Item = Option<Duration>, Error = V::Error>> {
        self.backend.takef(holder_id, &self.state)
    }
}

impl<T: Eq + Hash, U: Clone, V: Backend<T, U>> Deref for Bucket<T, U, V> {
    type Target = V;

    fn deref(&self) -> &Self::Target {
        &self.backend
    }
}

impl<T: Eq + Hash, U: Clone, V: Backend<T, U>> DerefMut for Bucket<T, U, V> {
    fn deref_mut(&mut self) -> &mut V {
        &mut self.backend
    }
}

#[cfg(test)]
mod test {
    use backend::InMemoryBackend;
    use std::time::Duration;
    use {Bucket, Holder};

    fn bucket() -> Bucket<i32, (), InMemoryBackend<i32, ()>> {
        Bucket::new(Duration::from_secs(2), 1)
    }

    #[test]
    fn test_generate() {
        let mut bucket = bucket();
        assert!(!bucket.has(&1).unwrap());

        bucket.generate(1).unwrap();
        assert!(bucket.has(&1).unwrap());
    }

    #[test]
    fn test_has() {
        let mut bucket = bucket();
        assert!(!bucket.has(&1).unwrap());

        bucket.generate(1).unwrap();
        assert!(bucket.has(&1).unwrap());

        bucket.remove(&1).unwrap();
        assert!(!bucket.has(&1).unwrap());
    }

    #[test]
    fn test_insert() {
        let mut bucket = bucket();
        assert!(!bucket.has(&1).unwrap());
        bucket.insert(1, Holder::default()).unwrap();
        assert!(bucket.has(&1).unwrap());
        bucket.take(1).unwrap();

        let value = bucket.insert(1, Holder::default());
        assert_eq!(*value.unwrap().unwrap().tickets_taken(), 1);
    }

    #[test]
    fn test_remaining() {
        let mut bucket = bucket();
        assert!(bucket.remaining(&1).unwrap().is_none());
        bucket.generate(1).unwrap();
        assert_eq!(bucket.remaining(&1).unwrap(), Some(1));

        bucket.take(1).unwrap();
        assert_eq!(bucket.remaining(&1).unwrap(), Some(0));
    }

    #[test]
    fn test_remove() {
        let mut bucket = bucket();
        assert!(bucket.remove(&1).unwrap().is_none());
        bucket.generate(1).unwrap();
        assert!(bucket.has(&1).unwrap());
        assert!(bucket.remove(&1).unwrap().is_some());
        assert!(!bucket.has(&1).unwrap());
    }

    #[test]
    fn test_set_tickets() {
        let mut bucket = bucket();
        bucket.generate(1).unwrap();
        assert_eq!(bucket.remaining(&1).unwrap(), Some(1));
        bucket.take(1).unwrap();
        bucket.set_tickets(3).unwrap();
        assert_eq!(bucket.remaining(&1).unwrap(), Some(2));
    }

    #[test]
    fn test_take() {
        let mut bucket = bucket();
        bucket.take(1).unwrap();
        assert_eq!(bucket.remaining(&1).unwrap(), Some(0));
    }

    #[test]
    fn test_take_nb() {
        let mut bucket = bucket();
        assert!(bucket.take_nb(1).unwrap().is_none());
        assert!(bucket.take_nb(1).unwrap().is_some());
    }

    #[test]
    fn test_nonblocking_duration() {
        let mut bucket = bucket();
        bucket.take(1).unwrap();
        let duration = bucket.take_nb(1).unwrap().expect("holder ticketed?");
        assert!(duration < Duration::from_secs(2));
        assert!(duration > Duration::from_secs(1));
    }

    #[test]
    fn test_no_state_holders() {
        let mut bucket = Bucket::new(Duration::from_secs(1), 2);
        bucket.take(0u64).unwrap();
        let holder = bucket.remove(&0).expect("no holder");
        assert_eq!(*holder.unwrap().state(), ());
    }

    #[test]
    fn test_stateful_holders() {
        #[derive(Clone)]
        struct State {
            bar: u64,
        }

        let mut bucket = Bucket::stateful(InMemoryBackend::new(Duration::from_secs(1), 2), State {
            bar: 0,
        });
        bucket.take(0u64).unwrap();
        let holder = bucket.remove(&0).expect("no holder");
        assert_eq!(holder.unwrap().state().bar, 0);
    }
}
