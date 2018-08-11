use std::collections::HashMap;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use std::time::Duration;
use std::thread;
use ::Holder;

#[cfg(feature = "futures")]
use futures::future::{self, Future};
#[cfg(feature = "tokio-timer")]
use tokio_timer::Timer;

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
/// use hikari::Bucket;
/// use std::time::Duration;
///
/// let mut bucket = Bucket::new(Duration::from_secs(1), 5);
/// bucket.take(1); // `1` is the ID to take a ticket from
/// bucket.take(2);
/// ```
///
/// [`Holder`]: struct.Holder.html
pub struct Bucket<T: Eq + Hash> {
    /// Holders are unique identifiers currently holding a ticket to the bucket
    /// instance.
    ///
    /// You _should not_ directly mutate this state and instead call methods to
    /// mutate it for you, but the option is there if you know what you're
    /// doing.
    ///
    /// **Note**: You should not access this map directly to take tickets, you
    /// should go through the [`take`] method.
    ///
    /// # Examples
    ///
    /// [`take`]: #method.take
    pub holders: HashMap<T, Holder>,
    /// The amount of time in milliseconds between the first removal of a ticket
    /// for a holder and when the tickets available to the holder refreshes.
    ///
    /// **Note**: Due to the synchronous nature of this bucket, the value of the
    /// number of used tickets may not be accurate and will not automatically
    /// replenish in the future.
    pub refresh_time: Duration,
    /// The maximum number of tickets allotted to each holder.
    pub tickets: u32,
    _nonexhaustive: (),
}

impl<T: Eq + Hash> Bucket<T> {
    /// Creates a new instance of Bucket with the provided refresh time and
    /// ticket count.
    ///
    /// # Examples
    ///
    /// Creating a bucket with 10 tickets per holder, with a 5 second refresh
    /// time:
    ///
    /// ```rust
    /// use hikari::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(5), 10);
    ///
    /// // You can now, for example, take tickets from identifying holders.
    /// bucket.take("anything that implements Eq + Hash can be an id");
    /// ```
    pub fn new(refresh_time: Duration, tickets: u32) -> Self {
        Bucket {
            holders: HashMap::new(),
            refresh_time: refresh_time,
            tickets: tickets,
            _nonexhaustive: (),
        }
    }

    /// Inserts a default holder for an ID, returning the existing holder if one
    /// exists.
    ///
    /// Unlike [`take`], this does not mutate the holder (i.e. taking a ticket).
    ///
    /// # Examples
    ///
    /// Insert a default holder for the id `77`:
    ///
    /// ```rust
    /// use hikari::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 1);
    /// bucket.generate(77u64);
    ///
    /// assert!(bucket.has(&77u64));
    /// ```
    ///
    /// [`take`]: #method.take
    #[inline]
    pub fn generate(&mut self, holder_id: T) -> Option<Holder> {
        self.insert(holder_id, Holder::default())
    }

    /// Whether the bucket contains an instance for the holder.
    ///
    /// # Examples
    ///
    /// Check that a fresh bucket does not originally have an instance for a
    /// holder until a ticket is taken:
    ///
    /// ```rust
    /// use hikari::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 1);
    /// assert!(!bucket.has(&"an id"));
    ///
    /// // Take a ticket for the ID and then assert that it _does_ exist.
    /// bucket.take("an id");
    /// assert!(bucket.has(&"an id"));
    /// ```
    #[inline]
    pub fn has(&mut self, holder_id: &T) -> bool {
        self.holders.contains_key(holder_id)
    }

    /// Inserts an existing holder into the bucket.
    ///
    /// This is primarily useful for transferring holders between buckets.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hikari::{Bucket, Holder};
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(5), 1);
    /// bucket.insert("an id", Holder::default());
    ///
    /// assert!(bucket.has(&"an id"));
    /// ```
    #[inline]
    pub fn insert(&mut self, holder_id: T, holder: Holder) -> Option<Holder> {
        self.holders.insert(holder_id, holder)
    }

    /// Calculates the number of remaining tickets in a holder.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hikari::Bucket;
    /// use std::time::Duration;
    ///
    /// let id = 77u64;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(5), 5);
    /// // Assert that retrieving the number of remaining tickets for a
    /// // nonexistent holder will return None.
    /// assert!(bucket.remaining(&id).is_none());
    ///
    /// // Assert that the bucket has 4 tickets remaining after taking a ticket.
    /// bucket.take(id);
    /// assert!(bucket.remaining(&id) == Some(4));
    /// ```
    #[inline]
    pub fn remaining(&mut self, holder_id: &T) -> Option<u32> {
        if self.has(holder_id) {
            let tickets = self.tickets;
            let refresh_time = self.refresh_time;

            self
                .holders
                .get_mut(holder_id)
                .map(|h| h.remaining(&tickets, &refresh_time))
        } else {
            None
        }
    }

    /// Attempts to remove a holder from the bucket, if one exists.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hikari::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 5);
    ///
    /// // A holder identified by `"hello"` doesn't exist yet.
    /// assert!(bucket.remove(&"hello").is_none());
    ///
    /// // Make the previously mentioned bucket, then remove it.
    /// bucket.take("hello");
    /// assert!(bucket.remove(&"hello").is_some());
    ///
    /// // Verify it was removed:
    /// assert!(bucket.remove(&"hello").is_none());
    /// ```
    #[inline]
    pub fn remove(&mut self, holder_id: &T) -> Option<Holder> {
        self.holders.remove(holder_id)
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
    /// use hikari::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 5);
    ///
    /// for _ in 0..3 {
    ///     bucket.take("hi");
    /// }
    ///
    /// assert!(bucket.remaining(&"hi") == Some(2));
    /// bucket.set_tickets(2);
    /// assert!(bucket.remaining(&"hi") == Some(0));
    /// ```
    #[inline]
    pub fn set_tickets(&mut self, new_ticket_count: u32) {
        self.tickets = new_ticket_count;
    }

    /// Takes a ticket from a holder, creating the holder if it doesn't exist.
    ///
    /// # Examples
    ///
    /// Take a single ticket from a holder, asserting that a single ticket was
    /// removed:
    ///
    /// ```rust
    /// use hikari::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 2);
    /// bucket.take("test");
    ///
    /// assert!(bucket.remaining(&"test") == Some(1));
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
    pub fn take(&mut self, holder_id: T) {
        if let Some(duration) = self.take_nb(holder_id) {
            thread::sleep(duration)
        }
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
        match self.take_nb(holder_id) {
            Some(dur) => {
                let done = Timer::default().sleep(dur)
                    .map_err(|_| ());

                Box::new(done)
            },
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
    /// use hikari::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(5), 1);
    /// bucket.take("test");
    ///
    /// // Assert that the holder's tickets are all used and that there is some
    /// // time until they replenish.
    /// assert!(bucket.take_nb("test").is_some());
    /// ```
    #[inline]
    pub fn take_nb(&mut self, holder_id: T) -> Option<Duration> {
        self.holders
            .entry(holder_id)
            .or_insert_with(Holder::default)
            .take(&self.tickets, &self.refresh_time)
    }
}

impl<T: Eq + Hash> Deref for Bucket<T> {
    type Target = HashMap<T, Holder>;

    fn deref(&self) -> &Self::Target {
        &self.holders
    }
}

impl<T: Eq + Hash> DerefMut for Bucket<T> {
    fn deref_mut(&mut self) -> &mut HashMap<T, Holder> {
        &mut self.holders
    }
}

#[cfg(test)]
mod test {
    use std::time::{Duration, Instant};
    use {Bucket, Holder};

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
    fn test_take_nb() {
        let mut bucket = bucket();
        assert!(bucket.take_nb(1).is_none());
        assert!(bucket.take_nb(1).is_some());
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
        let duration = bucket.take_nb(1).expect("holder ticketed?");
        assert!(duration < Duration::from_secs(2));
        assert!(duration > Duration::from_secs(1));
    }
}
