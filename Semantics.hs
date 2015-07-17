-- Begin work on the denotational semantics of Reflex FRP.
-- 1. Write the denotational semantics of Conal's Push-Pull FRP
--    using notation similar to that in FRPNow,
--    http://www.cse.chalmers.se/~atze/papers/prprfrp.pdf, since
--    it is the closest thing I have seen to haskell.
-- 2. Use this notation to write down the denotational semantics of reflex.
-- 3. Compare the two, showing why reflex is a valid FRP and point out the
--    differences.

-- We take (=) to indicate semantic equality.
-- In other words, the left hand side of an equals sign is haskell and
-- the right hand side is math.

------------------------------------------------------------------
-- 1. Push-Pull Functional Reactive Programming
------------------------------------------------------------------

type T  =  TOS -- Totally ordered set.
type T+ = TOS+ -- TOS extended with infinity and -infinity.

time :: Behavior T
time = id

type Behavior a = T -> a
type Event a    = [(T+, a)]

-- lift1 in Fran.
instance  Functor Behavior where
  fmap f b = \t -> (f . b) t

-- lift0, and lift2..n in Fran.
instance Applicative Behavior where
  pure a  = const a
  f <*> x = \t -> (f t) (x t)

-- Fran's neverE and (.|.)
instance Monoid (Event a) where
  mempty  = []
  mappend = merge

merge :: Event a -> Event a -> Event a
merge [] vs = vs
merge us [] = us
merge as@((ta, a) : ps) bs@((tb, b) : qs)
  | ta < tb   = (ta, a) : merge ps bs
  | otherwise = (tb, b) : merge as qs

instance Functor Event where
  fmap f e = map (\(ta, a) -> (ta, f a)) e

instance Monad Event where
  return a = [(-infinity, a)]
  join ma = foldr merge [] (delay <$> ma)

delay :: (T+, Event a) -> Event a
delay (te, e) = [(max te ta, a) | (ta, a) <- e]

switcher :: Behavior a -> Event (Behavior a) -> Behavior a
switcher b e = \t -> last (b : before e t) t

before :: Event a -> T -> [a]
before e t = [a | (ta, a) <- e, ta < t]

stepper :: a -> Event a -> Behavior a
stepper a e = \t -> last (a : before e t)

------------------------------------------------------------------
-- 2. Reflex FRP
------------------------------------------------------------------

-- XXX Just a start, obviously this has lots of errors and is imcomplete

import Data.These

type T  =  TOS -- Totally ordered set.

type Behavior a = T -> a
type Event a    = T -> Maybe a

instance Functor Behavior where
  fmap f b = \t -> f . b $ t

instance Functor Event where
  famp f e = \t -> f <$> e t

never :: Event a
never = \t -> Nothing

constant :: a -> Behavior a
constant x = \t -> x

-- Not sure what to do about the whole push / pull thing.
-- On one hand, they semm like an implementation detail on the
-- other hand, they are a key part of Reflex ?
push :: (a -> Behavior b) -> Event a -> Event b
push f e = \t -> (f <$> e t) t

-- What to do with merge and fan, again DMap seems like an implementation
-- detail. Is tuple enough for semantic meaning ?
merge :: Event a -> Event b -> Event (These a b)
merge ea eb = \t -> These (ea t) (eb t)

fan :: Event (These a b) -> (Event a, Event b)
fan e = (\t -> this $ e t, \t -> that $ e t)

switch :: Behavior (Event a) -> Event a
switch b = \t -> b t t

coincidence :: Event (Event a) -> Event a
coincidence e = \t -> e t t

-- I don't think these are part of the denotational semantics.
sample :: Behavior a -> T -> a
sample b t = b t

hold :: a -> Event a -> Behavior a
hold a e = \t -> case e t of
                   Nothing -> a
                   Just b  -> b
