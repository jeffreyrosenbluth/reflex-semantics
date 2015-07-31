------------------------------------------------------------------
-- Reflex FRP
------------------------------------------------------------------
-- The denotational semantics of Reflex FRP
-- using notation similar to that in FRPNow,
-- http://www.cse.chalmers.se/~atze/papers/prprfrp.pdf, since
-- it is the closest thing I have seen to haskell.

-- We take (=) to indicate semantic equality.
-- In other words, the left hand side of an equals sign is haskell and
-- the right hand side is math.
------------------------------------------------------------------

import Data.These

type Time  =  Double  -- Any totally ordered set, should be abstract.

type Behavior a = Time -> a
type Event a    = Time -> Maybe a

instance Functor Behavior where
  fmap f b = \t -> f . b $ t

instance Applicative Behavior where
  pure a  = const a
  f <*> x = \t -> (f t) (x t)

instance Functor Event where
  fmap f e = \t -> f <$> e t

never :: Event a
never = \t -> Nothing

push :: (a -> (Event b)) -> Event a -> Event b
push f e = \t -> e t >>= \a -> f a t

merge :: Event a -> Event b -> Event (These a b)
merge ea eb = \t -> These (ea t) (eb t)

-- Is this part of the semantics or a convenience function?
fan :: Event (These a b) -> (Event a, Event b)
fan e = (\t -> justThis $ e t, \t -> justThat $ e t)

switch :: Behavior (Event a) -> Event a
switch b = \t -> b t t

-- According to footnote 7 in "prprfrp" (FRPNow) the join operator in Conal's
-- push-pull is inherently leaky. My intuition is that we are ok here, but we
-- shouuld check.
coincidence :: Event (Event a) -> Event a
coincidence e = \t -> e t >>= \f -> f t

-- switcher can be derived from hold.
hold :: a -> Event a -> Behavior (Behavior a)
hold a e = \t0 -> \t
  -- of course sup (supremum) is not haskell, but it is a valid denotation.
  -- I think < is right, but it could be <= ?
  let s = sup [r | r < t && isJust (e r)]
  in if t <= t0 then a else fromJust (e s)

-- or
hold :: a -> Event a -> Time -> Behavior a
hold a e t0 = \t ->
  let s = sup [r | r < t && isJust (e r)]
  in if t <= t0 then a else fromJust (e s)

-- What to do about sample?
sample :: Behavior a -> Behavior a
sample = id

sample :: Behavior a -> Time -> a
sample b t = b t
