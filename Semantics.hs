{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Reflex.Semantics where

import Data.Maybe (isJust, fromJust)
import Data.These
import Data.MemoTrie (memo)

type Time = Int

newtype Behavior a = Behavior {unBehavior :: Time -> a}
  deriving (Functor, Applicative, Monad)

newtype Event a = Event {unEvent :: Time -> Maybe a}
  deriving (Functor)

newtype Push a = Push {unPush :: Time -> a}
  deriving (Functor, Applicative, Monad)

never :: Event a
never = Event (const Nothing)

merge :: Event a -> Event b -> Event (These a b)
merge (Event ea) (Event eb) = Event $ \t ->
  case (ea t, eb t) of
    (Nothing, Nothing) -> Nothing
    (Just a , Nothing) -> Just (This a)
    (Nothing, Just b ) -> Just (That b)
    (Just a , Just b ) -> Just (These a b)

sample :: Behavior a -> Push a
sample (Behavior b) = Push b

hold   :: a -> Event a -> Push (Behavior a)
hold a (Event e) = Push $ \t0 -> Behavior . memo $ \t ->
  let s = [r | r <- [(t0+1)..(t-1)], isJust (e r)]
  in if t <= t0 || null s
       then a
       else fromJust (e (last s))

push :: (a -> Push (Maybe b)) -> Event a -> Event b
push f (Event e) = Event . memo $ \t -> e t >>= \a -> unPush (f a) t

switch :: Behavior (Event a) -> Event a
switch (Behavior b) = Event . memo $ \t -> unEvent (b t) t

coincidence :: Event (Event a) -> Event a
coincidence (Event e) = Event . memo $ \t -> e t >>= \f -> unEvent f t
