------------------------------------------------------------------
-- Push-Pull
------------------------------------------------------------------
-- The denotational semantics of Push-Pull FRP
-- using notation similar to that in FRPNow,
-- http://www.cse.chalmers.se/~atze/papers/prprfrp.pdf, since
-- it is the closest thing I have seen to haskell.

-- We take (=) to indicate semantic equality.
-- In other words, the left hand side of an equals sign is haskell and
-- the right hand side is math.
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
