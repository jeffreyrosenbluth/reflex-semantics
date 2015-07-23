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

type Time = Double

time :: Behavior Time
time = id

type Behavior a = Time -> a
type Event a    = [(Time, a)] -- none-decreasing times
-- or
-- newtype Event a = Event (Behavior [a]) deriving (Monoid, Functor)

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

delay :: (Time, Event a) -> Event a
delay (te, e) = [(max te ta, a) | (ta, a) <- e]

switcher :: Behavior a -> Event (Behavior a) -> Behavior a
switcher b e = \t -> last (b : before e t) t

before :: Event a -> Time-> [a]
before e t = [a | (ta, a) <- e, ta < t]

stepper :: a -> Event a -> Behavior a
stepper a e = \t -> last (a : before e t)

------------------------------------------------------------------
-- 2. FRPNow
------------------------------------------------------------------

type Event a = (Time+,a)

never :: Event a
never = (∞, undefined)

instance Monad Event where
  return x = (-∞,x)
  (ta,a) >>= f = let (tb,b) = f a
                 in (max ta tb, b)

type Behavior a = Time -> a

instance Monad Behavior where
  return x = λt -> x
  m >>= f  = λt -> f (m t) t

instance MonadFix Behavior where
  mfix f = λt -> let x = f x t in x

switch :: Behavior a -> Event (Behavior a) -> Behavior a
switch b (ts,s) = λn ->
  if n < ts then b n else s n

whenJust :: Behavior (Maybe a) -> Behavior (Event a)
whenJust b = λt ->
  let w = minSet { t' | t' >= t && isJust (b t') }
  in  if w == ∞ then never
      else (w, fromJust (b w))

------------------------------------------------------------------
-- 3. Reflex FRP
------------------------------------------------------------------

import Data.These

type Time  =  Double  -- Any totally ordered set.

type Behavior a = Time -> a
type Event a    = Time -> Maybe a

instance Functor Behavior where
  fmap f b = \t -> f . b $ t

instance Applicative Behavior where
  pure a  = const a
  f <*> x = \t -> (f t) (x t)

instance Functor Event where
  famp f e = \t -> f <$> e t 

never :: Event a
never = \t -> Nothing

push :: (a -> (Event b)) -> Event a -> Event b
push f e = \t -> e t >>= \a -> f a t

merge :: Event a -> Event b -> Event (These a b)
merge ea eb = \t -> These (ea t) (eb t)

fan :: Event (These a b) -> (Event a, Event b)
fan e = (\t -> justThis $ e t, \t -> justThat $ e t)

switch :: Behavior (Event a) -> Event a
switch b = \t -> b t t

coincidence :: Event (Event a) -> Event a
coincidence e = \t -> e t t

hold :: a -> Event a -> Time -> Behavior a
hold a e t0 = \t ->
  -- of course sup (supremum) is not haskell, but it is a valid denotation.
  let s = sup [r | r <= t && isJust (e r)]
  in if t <= t0 then a else fromJust (e s)
