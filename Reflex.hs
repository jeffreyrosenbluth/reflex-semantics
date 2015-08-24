------------------------------------------------------------------
-- Reflex FRP
------------------------------------------------------------------
-- The denotational semantics of Reflex FRP
-- We take (≗) to indicate semantic equality.
-- In other words, the left hand side of an equals sign is haskell
-- syntax and the right hand side is its mathematical meaning.
------------------------------------------------------------------

-- Not part of the Reflex interface ------------------------------
data These a b ≗ This a | That b | These a b

-- Any totally ordered set.
type Time  ≗  (Eq a, Ord a) => a
------------------------------------------------------------------

type Behavior a ≗ Time -> a

-- Events must satifsy the constraint that for any two Times s < t, the
-- number of Just values in the interval (s, t) is finite. I
-- believe that somehting like this is technically necessary in
-- the semantics of Push-Pull FRP as well.

-- This representation of Events does however, restrict two Events from
-- occuring at the same time. However, we can gain back the full generality by
-- this using the merge function which, unlike the Push-Pull FRP semantics,
-- keeps These values of simultaneous events.
type Event a ≗ Time -> Maybe a

instance Functor Behavior where
  fmap f b ≗ λt -> f . b $ t

instance Applicative Behavior where
  pure a  ≗ const a
  f <*> x ≗ λt -> f t (x t)

instance Monad Behavior where
  return ≗ pure
  f >>= k ≗ λt -> k (f t) t

instance Functor Event where
  fmap f e ≗ λt -> f <$> e t

never :: Event a
never ≗ λt -> Nothing

type Push a ≗ Time -> a

class EventMap m where
  sample :: Behavior a -> Time -> a
  hold   :: a -> Event a -> Time -> Behavior a

instance EventMap Push where
  sample ≗ id
  hold a e t0 ≗ λt ->
    let s ≗ [r | r > t0 && r < t && isJust (e r)]
    -- Technically t shoud never be strictly less than t0;
    -- this would signal an implementation error.
    in if t <= t0 || null s
         then a
         -- Here we rely on the fact that only a finte number
         -- of Just values occur in the interval (t0, t) to insure
         -- that the behavior changes after (not at the same time)
         -- the event fires.
         else fromJust (e (last s))

push :: (a -> Push (Maybe b)) -> Event a -> Event b
push f e ≗ \t -> e t >>= \a -> f a t

merge :: Event a -> Event b -> Event (These a b)
merge ea eb ≗ λt ->
  case (ea t, eb t) of
    (Nothing, Nothing) -> Nothing
    (Just a , Nothing) -> Just (This a)
    (Nothing, Just b ) -> Just (That b)
    (Just a , Just b ) -> Just (These a b)

switch :: Behavior (Event a) -> Event a
switch b ≗ λt -> b t t

-- There is no useful definition of Pure for Events,
-- hence we do not create Applicative or Monad instances.
coincidence :: Event (Event a) -> Event a
coincidence e ≗ λt -> e t >>= λf -> f t
