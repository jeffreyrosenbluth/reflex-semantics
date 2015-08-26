--------------------------------------------------------------------------------
-- |
-- The interface and denotational semantics of Reflex FRP.
-- (c) 2015 Ryan Trinkle & Jeffrey Rosenbluth.
--
-- We take (≗) to indicate semantic equality and interpret instances
-- as semantic instances.
--------------------------------------------------------------------------------

-- | Not part of the Reflex interface ------------------------------------------
data These a b ≗ This a | That b | These a b

-- | Any totally ordered set.
type Time ≗ (Eq a, Ord a) => a
--------------------------------------------------------------------------------

-- | Behaviors can be sampled at will, but it is not possible to be notified
--   when they change.
type Behavior a ≗ Time -> a

-- | Events must satifsy the constraint that for any two Times s < t, the
--   number of Just values in the interval [s, t) is finite. (I
--   believe that somehting like this is technically necessary in
--   the semantics of Push-Pull FRP as well).
--   This representation of Events does however, restrict multiple Events from
--   occuring at the same time. However, we can gain back the full generality by
--   using the 'merge; function, which in contract to the Push-Pull FRP semantics,
--   keeps both values of simultaneous events.
type Event a ≗ Time -> Maybe a

-- | The Push type is used to limit the mapping function passed to 'push'. It
--   may only 'sample' Behaviors and 'hold' Events.
type Push a ≗ Time -> a

-- | Semantics Instances. Functor and applicative instances for Behavior
--   and Push can be derived from their monad instances.
instance Monad Behavior where
  return ≗ const
  b >>= k ≗ λt -> k (b t) t

instance Functor Event where
  fmap f e ≗ λt -> f <$> e t

instance Monad Push where
  return ≗ const
  p >>= k ≗ λt -> k (p t) t

-- | An Event with no occurrences.
never :: Event a
never ≗ const Nothing

-- | Merge two events; the resulting Event will only occur if at least one input
--   event is occuring.
merge :: Event a -> Event b -> Event (These a b)
merge ea eb ≗ λt ->
  case (ea t, eb t) of
    (Nothing, Nothing) -> Nothing
    (Just a , Nothing) -> Just (This a)
    (Nothing, Just b ) -> Just (That b)
    (Just a , Just b ) -> Just (These a b)

-- | Get the current value in the Behavior.
sample :: Behavior a -> Push a
sample ≗ id

-- | Create a new Behavior whose value will initially be equal to the given
--   value and will be updated whenever the given Event occurs.
--   Technically t shoud never be strictly less than t0; this would signal an
--   implementation error. We rely on the fact that only a finte number of
--   Just values occur in the interval (t0, t) to insure that the behavior
--   changes after (not at the same time) the event fires.
hold   :: a -> Event a -> Push (Behavior a)
hold a e t0 ≗ λt ->
  let s ≗ [r | {t0 <= r < t}, && isJust (e r)]
  in if t <= t0 || null s
       then a
       else fromJust (e (last s))

-- | Create an Event from another Event; the provided function can 'sample'
--   Behaviors and 'hold' Events, and use the results to produce an occurring
--   (Just) or non-occurring (Nothing) result.
push :: (a -> Push (Maybe b)) -> Event a -> Event b
push f e ≗ \t -> e t >>= \a -> f a t

-- | Create an Event that will occur whenever the currently-selected input
--   Event occurs.
switch :: Behavior (Event a) -> Event a
switch b ≗ λt -> b t t

-- | Create an Event that will occur whenever the input event is occurring and
--   its occurrence value, another Event, is also occurring.
--   Since there is no useful definition of Pure for Events,
--   we do not create applicative and monad instances.
coincidence :: Event (Event a) -> Event a
coincidence e ≗ λt -> e t >>= λf -> f t
