------------------------------------------------------------------
-- Reflex FRP
------------------------------------------------------------------
-- The denotational semantics of Reflex FRP
-- We take (≗) to indicate semantic equality.
-- In other words, the left hand side of an equals sign is haskell
-- syntax and the right hand side is its mathematical meaning.
------------------------------------------------------------------

-- Not part of the Reflex interface ------------------------------
data Both a b ≗ First a | Second b | Both a b

-- Any totally ordered set.
type Time  ≗  (Eq a, Ord a) => a
------------------------------------------------------------------

type Behavior a ≗ Time -> a

-- We maintain the invariant that the range of any Event, contains
-- a countable number of Just values. No generality is lost by this
-- invariant, as the origingal denotation for Event a ≗ [(t, a)].
-- This choice does however, restrict two Events from occuring at
-- the same time, but we can achieve this using the merge function
-- which, unlike the origingal FRP semantics, keeps both values of
-- simultaneous events.
type Event a ≗ Time -> Maybe a

instance Functor Behavior where
  fmap f b ≗ λt -> f . b $ t

instance Applicative Behavior where
  pure a  ≗ const a
  f <*> x ≗ λt -> (f t) (x t)

instance Monad Behavior where
  return ≗ pure
  f >>= k ≗ λt -> k (f t) t

instance Functor Event where
  fmap f e ≗ λt -> f <$> e t

never :: Event a
never ≗ λt -> Nothing

-- XXX I think we should say a few words about push and how it
-- differs from the Push-Pull semantics.
push :: (a -> (Event b)) -> Event a -> Event b
push f e ≗ λt -> e t >>= λa -> f a t

merge :: Event a -> Event b -> Event (Both a b)
merge ea eb ≗ λt ->
  case (ea t, eb t) of
    (Nothing, Nothing) -> Nothing
    (Just a , Nothing) -> Just (First a)
    (Nothing, Just b ) -> Just (Second b)
    (Just a , Just b ) -> Just (Both a b)

switch :: Behavior (Event a) -> Event a
switch b ≗ λt -> b t t

-- There is no useful definition of Pure for Events,
-- hence we do not create Applicative or Monad instances.
coincidence :: Event (Event a) -> Event a
coincidence e ≗ λt -> e t >>= λf -> f t

-- XXX I needed to change this around a tad to avoid taking
-- the supremum of the empty set.
hold :: a -> Event a -> Time -> Behavior a
hold a e t0 ≗ λt ->
  let s ≗ {r : r < t && isJust (e r)}
  -- Technically t shoud never be strictly less than t0;
  -- this would signal an implementation error.
  in if t <= t0 || s == {} -- the empty set
       then a
       -- Here we rely on the invariant of a countable number
       -- of Just values in the range of the Event to insure
       -- that the behavior changes after (not at the same time)
       -- the event fires.
       else fromJust (e (sup s))

-- XXX Do you think we should include this?
-- Not really part of the denotational semantics as it is defined in
-- terms of hold.
switcher :: Behavior a -> Event (Behavior a) -> Time -> Behavior a
swithcer b eb t0 = λt -> hold b eb t0 t t
