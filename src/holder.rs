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
/// use hikari::Bucket;
/// use std::time::Duration;
///
/// let mut one = Bucket::new(Duration::from_secs(1), 1);
/// let mut two = Bucket::new(Duration::from_secs(2), 1);
///
/// one.generate("an id");
///
/// if let Some(holder) = one.remove(&"an id") {
///     two.insert("an id", holder);
/// }
///
/// assert!(!one.has(&"an id"));
/// assert!(two.has(&"an id"));
/// ```
///
/// [`Bucket`]: struct.Bucket.html
#[derive(Clone, Debug, Default)]
pub struct Holder {
    /// The number of tickets that have been taken from the holder.
    ///
    /// This will refresh when time is up, but only when a ticket is being taken
    /// or the [`refresh`] method is called.
    ///
    /// [`refresh`]: #method.refresh
    pub tickets_taken: u32,
    /// The time that the current ticket iteration started.
    ///
    /// When this instant - plus the duration of the associated bucket's refresh
    /// time - has passed, this will reset.
    pub started_at: Option<Instant>,
}

impl Holder {
    /// Calculates the number of tickets that are remaining, saturating at the
    /// minimal `u32` bound if [`Holder::tickets_taken`] is greater than the
    /// provided `max_tickets`.
    ///
    /// Typically, you should be calling [`Bucket::remaining`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hikari::Holder;
    /// use std::time::Duration;
    ///
    /// let max = 5u32;
    ///
    /// let mut holder = Holder::default();
    /// let duration = Duration::from_secs(2);
    /// holder.take(&max, &duration);
    ///
    /// assert!(holder.remaining(&max, &duration) == 4);
    /// ```
    ///
    /// [`Bucket::remaining`]: struct.Bucket.html#method.remaining
    /// [`Holder::tickets_taken`]: #structfield.tickets_taken
    #[inline]
    pub fn remaining(
        &mut self,
        max_tickets: &u32,
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
    /// use hikari::Holder;
    /// use std::time::Duration;
    ///
    /// // Maximum number of tickets allocated to this holder, and the duration
    /// // between refreshments.
    /// let max = 5u32;
    /// let duration = Duration::from_secs(2);
    ///
    /// let mut holder = Holder::default();
    ///
    /// // Assert that no tickets have been taken.
    /// assert!(holder.tickets_taken == 0);
    ///
    /// holder.take(&max, &duration);
    /// assert!(holder.tickets_taken == 1);
    /// ```
    ///
    /// [`Bucket::take`]: struct.Bucket.html#method.take
    pub fn take(
        &mut self,
        max: &u32,
        refresh_time: &Duration,
    ) -> Option<Duration> {
        if self.tickets_taken == *max {
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
}
