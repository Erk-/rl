use std::time::{Duration, Instant};

/// Implementation around each holder value, containing the number of used
/// tickets and when the refreshment time began.
///
/// Holders themselves do not know the state of their parent [`Bucket`], and are
/// instead provided these values. Theoretically, holders can be traded between
/// buckets.
///
/// # Examples
///
/// Moving a holder from one bucket to another:
///
/// ```rust
/// use rl::Bucket;
/// use std::time::Duration;
///
/// let mut one = Bucket::new(Duration::from_secs(1), 1);
/// let mut two = Bucket::new(Duration::from_secs(2), 1);
///
/// one.generate("an id").unwrap();
///
/// if let Ok(Some(holder)) = one.remove(&"an id") {
///     two.insert("an id", holder).unwrap();
/// }
///
/// assert!(!one.has(&"an id").unwrap());
/// assert!(two.has(&"an id").unwrap());
/// ```
///
/// [`Bucket`]: struct.Bucket.html
#[derive(Clone, Debug, Default)]
pub struct Holder<T: Clone = ()> {
    tickets_taken: u32,
    started_at: Option<Instant>,
    state: T,
    _nonexhaustive: (),
}

impl<T: Clone + 'static> Holder<T> {
    /// Creates a new holder with no custom state.
    pub fn new(
        started_at: Option<Instant>,
        tickets_taken: u32,
        state: T,
    ) -> Holder<T> {
        Holder {
            started_at: started_at,
            state: state,
            tickets_taken: tickets_taken,
            _nonexhaustive: (),
        }
    }

    /// Returns an immutable reference to the time that the current ticket
    /// iteration started.
    ///
    /// When this instant - plus the duration of the associated bucket's refresh
    /// time - has passed, this will reset.
    pub fn started_at(&self) -> &Option<Instant> {
        &self.started_at
    }

    /// Returns a mutable reference to the time that the current ticket
    /// iteration started.
    ///
    /// Refer to [`started_at`] for more information.
    ///
    /// [`started_at`]: #method.started_at
    pub fn started_at_mut(&mut self) -> &mut Option<Instant> {
        &mut self.started_at
    }

    /// Returns an immutable reference to the user-provided default holder
    /// state, if any.
    ///
    /// This is available so additional stateful information about each holder
    /// can be attached and not held in a separate storage location (like a
    /// `HashMap` that maps to a [`Holder`]).
    ///
    /// [`Holder`]: struct.Holder.html
    pub fn state(&self) -> &T {
        &self.state
    }

    /// Returns a mutable reference to the user-provided default holder state,
    /// if any.
    ///
    /// Refer to [`state`] for more information.
    ///
    /// [`state`]: #method.state
    pub fn state_mut(&mut self) -> &mut T {
        &mut self.state
    }

    /// Returns an immutable reference to the number of tickets that have been
    /// taken from the holder.
    ///
    /// This will refresh when time is up, but only when a ticket is being taken
    /// or the [`refresh`] method is called.
    ///
    /// [`refresh`]: #method.refresh
    pub fn tickets_taken(&self) -> &u32 {
        &self.tickets_taken
    }

    /// Returns a mutable reference to the number of tickets that have been
    /// taken from the holder.
    ///
    /// Refer to [`tickets_taken`] for more information.
    ///
    /// [`tickets_taken`]: #method.tickets_taken
    pub fn tickets_taken_mut(&mut self) -> &mut u32 {
        &mut self.tickets_taken
    }

    /// Calculates the number of tickets that are remaining, saturating at the
    /// minimal `u64` bound if [`Holder::tickets_taken`] is greater than the
    /// provided `max_tickets`.
    ///
    /// Typically, you should be calling [`Bucket::remaining`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rl::Holder;
    /// use std::time::Duration;
    ///
    /// let max = 5u32;
    ///
    /// let mut holder: Holder<()> = Holder::default();
    /// let duration = Duration::from_secs(2);
    /// holder.take(max, &duration);
    ///
    /// assert!(holder.remaining(max, &duration) == 4);
    /// ```
    ///
    /// [`Bucket::remaining`]: struct.Bucket.html#method.remaining
    /// [`Holder::tickets_taken`]: #structfield.tickets_taken
    #[inline]
    pub fn remaining(
        &mut self,
        max_tickets: u32,
        refresh_time: &Duration,
    ) -> u32 {
        self.check_refresh(refresh_time);

        max_tickets.saturating_sub(self.tickets_taken)
    }

    /// Takes a single ticket from the holder, accepting the maximum number of
    /// tickets that the holder is allotted as well as the duration between
    /// ticket refreshments.
    ///
    /// If the number of tickets allotted to the holder have already been used,
    /// this will return the duration until its tickets can refresh.
    ///
    /// Typically, you should be calling [`Bucket::take`].
    ///
    /// # Examples
    ///
    /// Create a holder and take a single ticket from it:
    ///
    /// ```rust
    /// use rl::Holder;
    /// use std::time::Duration;
    ///
    /// // Maximum number of tickets allocated to this holder, and the duration
    /// // between refreshments.
    /// let max = 5u32;
    /// let duration = Duration::from_secs(2);
    ///
    /// let mut holder: Holder<()> = Holder::default();
    ///
    /// // Assert that no tickets have been taken.
    /// assert!(*holder.tickets_taken() == 0);
    ///
    /// holder.take(max, &duration);
    /// assert!(*holder.tickets_taken() == 1);
    /// ```
    ///
    /// [`Bucket::take`]: struct.Bucket.html#method.take
    pub fn take(
        &mut self,
        max: u32,
        refresh_time: &Duration,
    ) -> Option<Duration> {
        if self.tickets_taken == max {
            match self.time_remaining(refresh_time) {
                Some(duration) => Some(duration),
                None => {
                    self.started_at = Some(Instant::now());
                    self.tickets_taken = 1;

                    None
                }
            }
        } else {
            if self.started_at.is_none() {
                self.started_at = Some(Instant::now());
            }
            self.tickets_taken += 1;

            None
        }
    }

    // Checks if the refresh time has completely elapsed, if it ever started,
    // resetting the holder.
    //
    // By "resetting the holder", it is meant that [`started_at`] and
    // [`tickets_taken`] are set to `None and `0`, respectively.
    //
    // [`started_at`]: #structfield.started_at
    // [`tickets_taken`]: #structfield.tickets_taken
    fn check_refresh(&mut self, refresh_time: &Duration) {
        if let Some(started_at) = self.started_at {
            if started_at.elapsed() >= *refresh_time {
                self.started_at = None;
                self.tickets_taken = 0;
            }
        }
    }

    // Checks for the amount of time remaining until the holder can reset, if
    // any.
    fn time_remaining(&self, refresh_time: &Duration) -> Option<Duration> {
        let elapsed = match self.started_at {
            Some(started_at) => started_at.elapsed(),
            None => return None,
        };

        if elapsed < *refresh_time {
            Some(*refresh_time - elapsed)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::Holder;
    use std::time::Duration;

    #[test]
    fn test_remaining() {
        let mut holder = Holder::new(None, 0, ());
        let duration = Duration::from_secs(1);
        assert_eq!(holder.remaining(1u32, &duration), 1);

        holder.take(1, &duration);
        assert_eq!(holder.remaining(1, &duration), 0);
        holder.take(1, &duration);
        assert_eq!(holder.remaining(1, &duration), 0);
    }

    #[test]
    fn test_take() {
        let mut holder = Holder::new(None, 0, ());
        let duration = Duration::from_secs(1);
        let result = holder.take(1u32, &duration);
        assert!(result.is_none());
        let result = holder.take(1, &duration).expect("holder tickets not maxed");
        assert!(result <= Duration::from_secs(1));
    }
}
