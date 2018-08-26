//! Implementation and error definitions for the in process memory backend.

use super::Backend;
use std::collections::HashMap;
use std::error::Error as StdError;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::hash::Hash;
use std::mem;
use std::time::Duration;
use Holder;

/// Error enum for [`InMemoryBackend`].
///
/// This error never occurs at the time of this writing, and is only here to
/// fulfill the type requirement. This also means that all Results returned by
/// this backend (and therefore the [`Bucket`]) can be `?`'d away without
/// consequence.
///
/// [`Bucket`]: ../../struct.Bucket.html
/// [`InMemoryBackend`]: struct.InMemoryBackend.html
#[derive(Debug)]
pub enum InMemoryError {
    #[doc(hidden)]
    _Nonexhaustive,
}

impl Display for InMemoryError {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        f.write_str(self.description())
    }
}

impl StdError for InMemoryError {
    fn description(&self) -> &str {
        "This error should never occur"
    }
}

/// Backend which keeps holders in the process memory.
///
/// Refer to [`Backend`] for how to effectively use this.
///
/// This also includes a few methods for directly working with the holders in
/// both mutable and immutable methods, but you should take care when using
/// them.
///
/// [`Backend`]: ../trait.Backend.html
pub struct InMemoryBackend<T: Eq + Hash, U: Clone + 'static = ()> {
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
    holders: HashMap<T, Holder<U>>,
    /// The amount of time in milliseconds between the first removal of a ticket
    /// for a holder and when the tickets available to the holder refreshes.
    ///
    /// **Note**: Due to the synchronous nature of this bucket, the value of the
    /// number of used tickets may not be accurate and will not automatically
    /// replenish in the future.
    refresh_time: Duration,
    /// The maximum number of tickets allotted to each holder.
    tickets: u32,
}

impl<T: Eq + Hash, U: Clone + 'static> InMemoryBackend<T, U> {
    /// Creates a new in memory backend with a provided refresh time and
    /// maximum number of holder tickets.
    pub fn new(refresh_time: Duration, tickets: u32) -> Self {
        Self {
            holders: HashMap::new(),
            refresh_time: refresh_time,
            tickets: tickets,
        }
    }

    /// Returns an immutable reference to the inner holders.
    ///
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
    /// [`take`]: #method.take
    pub fn holders(&self) -> &HashMap<T, Holder<U>> {
        &self.holders
    }

    /// Returns a mutable reference to the inner holders.
    ///
    /// Refer to [`holders_mut`] for more information.
    ///
    /// [`holders_mut`]: #method.holders_mut
    pub fn holders_mut(&mut self) -> &mut HashMap<T, Holder<U>> {
        &mut self.holders
    }

    /// Returns an immutable reference to a holder from the holders map by key,
    /// if one exists.
    ///
    /// This is a shortcut for going through the [`holders`] getter and
    /// then keying that.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rl::Bucket;
    /// use std::time::Duration;
    ///
    /// let mut bucket = Bucket::new(Duration::from_secs(1), 5);
    /// bucket.take(&1u64);
    ///
    /// assert!(bucket.holder(&&1).is_some());
    /// ```
    ///
    /// [`holders`]: #method.holders
    #[inline]
    pub fn holder(&self, holder_id: &T) -> Option<&Holder<U>> {
        self.holders.get(holder_id)
    }

    /// Returns a mutable reference to a holder from the holders map by key, if
    /// one exists.
    ///
    /// Refer to [`holder`] for more information.
    ///
    /// [`holder`]: #method.holder
    #[inline]
    pub fn holder_mut(&mut self, holder_id: &T) -> Option<&mut Holder<U>> {
        self.holders.get_mut(holder_id)
    }
}

impl<T: Eq + Hash, U: Clone + 'static> Backend<T, U> for InMemoryBackend<T, U> {
    type Error = InMemoryError;

    fn refresh_time(&mut self) -> Result<Option<Duration>, Self::Error> {
        Ok(Some(self.refresh_time))
    }

    fn tickets(&mut self) -> Result<Option<u32>, Self::Error> {
        Ok(Some(self.tickets))
    }

    fn set_refresh_time(
        &mut self,
        new_refresh_time: Duration,
    ) -> Result<Option<Duration>, Self::Error> {
        Ok(Some(mem::replace(&mut self.refresh_time, new_refresh_time)))
    }

    fn set_tickets(&mut self, new_tickets: u32) -> Result<Option<u32>, Self::Error> {
        Ok(Some(mem::replace(&mut self.tickets, new_tickets)))
    }

    fn generate(&mut self, holder_id: T, state: U) -> Result<Option<Holder<U>>, Self::Error> {
        self.insert(holder_id, Holder::new(None, 0, state))
    }

    fn has(&mut self, holder_id: &T) -> Result<bool, Self::Error> {
        Ok(self.holders.contains_key(holder_id))
    }

    fn insert(&mut self, holder_id: T, holder: Holder<U>) -> Result<Option<Holder<U>>, Self::Error> {
        Ok(self.holders.insert(holder_id, holder))
    }

    fn remaining(&mut self, holder_id: &T) -> Result<Option<u32>, Self::Error> {
        Ok(if self.has(holder_id)? {
            let tickets = self.tickets;
            let refresh_time = self.refresh_time;

            self
                .holders
                .get_mut(holder_id)
                .map(|h| h.remaining(tickets, &refresh_time))
        } else {
            None
        })
    }

    fn remove(&mut self, holder_id: &T) -> Result<Option<Holder<U>>, Self::Error> {
        Ok(self.holders.remove(holder_id))
    }

    fn take(&mut self, holder_id: T, state: &U) -> Result<Option<Duration>, Self::Error> {
        Ok(self.holders
            .entry(holder_id)
            .or_insert_with(|| {
                Holder::new(None, 0, state.clone())
            })
            .take(self.tickets, &self.refresh_time))
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;
    use super::InMemoryBackend;
    use super::super::Backend;
    use Holder;

    type Impl = InMemoryBackend<u64, ()>;

    fn backend() -> Impl {
        InMemoryBackend::new(Duration::from_secs(2), 5)
    }

    #[test]
    fn test_backend_methods() {
        let mut backend = backend();
        assert!(backend.holders().is_empty());

        backend.holders_mut().insert(1, Holder::new(None, 0, ()));
        assert_eq!(backend.holders().len(), 1);
    }

    #[test]
    fn test_take() {
        let mut backend = backend();
        assert!(backend.take(1, &()).unwrap().is_none());
    }
}
