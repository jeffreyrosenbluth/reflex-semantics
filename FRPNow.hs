------------------------------------------------------------------
-- FRPNow
------------------------------------------------------------------
-- The denotational semantics of FRNNow FRP
-- http://www.cse.chalmers.se/~atze/papers/prprfrp.pdf.

-- We take (=) to indicate semantic equality.
-- In other words, the left hand side of an equals sign is haskell and
-- the right hand side is math.
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
