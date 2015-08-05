------------------------------------------------------------------
-- Reflex FRP
------------------------------------------------------------------
-- The denotational semantics of Reflex FRP
-- We take (=) to indicate semantic equality.
-- In other words, the left hand side of an equals sign is haskell
-- syntax and the right hand side is its mathematical meaning.
------------------------------------------------------------------

-- Not part of semantics -----------------------------------------
data Both a b = First a | Second b | Both a b

-- Any totally ordered set, should be abstract.
type Time  =  Double
------------------------------------------------------------------

type Behavior a = Time -> a
type Event a    = Time -> Maybe a

instance Functor Behavior where
  fmap f b = \t -> f . b $ t

instance Applicative Behavior where
  pure a  = const a
  f <*> x = \t -> (f t) (x t)

instance Monad Behavior where
  return = pure
  f >>= k = \t -> k (f t) t

instance Functor Event where
  fmap f e = \t -> f <$> e t

never :: Event a
never = \t -> Nothing

push :: (a -> (Event b)) -> Event a -> Event b
push f e = \t -> e t >>= \a -> f a t

merge :: Event a -> Event b -> Event (Both a b)
merge ea eb = \t ->
  case (ea t, eb t) of
    (Nothing, Nothing) -> Nothing
    (a      , Nothing) -> Just (First a)
    (Nothing, b      ) -> Just (Second b)
    (a      , b      ) -> Just (Both a b)

switch :: Behavior (Event a) -> Event a
switch b = \t -> b t t

coincidence :: Event (Event a) -> Event a
coincidence e = \t -> e t >>= \f -> f t

hold :: a -> Event a -> Time -> Behavior a
hold a e t0 = \t ->
  let s = {r : r < t && isJust (e r)}
  -- Technically t shoud never be strictly less than t0;
  -- this would signal an implementation error.
  in if t <= t0 || s == {}
       then a
       else fromJust (e (sup s))
