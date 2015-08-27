{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}

module Reflex.Model where

import           Control.Monad
import           Data.Functor.Misc
import           Data.Maybe         (fromJust, isJust)
import           Reflex.Class

import           Data.Dependent.Map (DMap, GCompare)
import qualified Data.Dependent.Map as DMap
import           Data.MemoTrie

data Model t

instance (Enum t, HasTrie t, Ord t) => Reflex (Model t) where
  newtype Behavior (Model t) a = Behavior { unBehavior :: t -> a }
  newtype Event (Model t) a    = Event { unEvent :: t -> Maybe a }

  type PushM (Model t) = (->) t
  type PullM (Model t) = (->) t

  never :: Event (Model t) a
  never = Event $ const Nothing

  constant :: a -> Behavior (Model t) a
  constant  = pure

  push :: (a -> PushM (Model t) (Maybe b)) -> Event (Model t) a -> Event (Model t) b
  push f e = Event . memo $ \t -> unEvent e t >>= \a -> f a t

  pull :: PullM (Model t) a -> Behavior (Model t) a
  pull = Behavior . memo

  merge :: GCompare k => DMap (WrapArg (Event (Model t)) k) -> Event (Model t) (DMap k)
  merge events = Event $ memo $ \t ->
    let currentOccurrences = unwrapDMapMaybe (($ t) . unEvent) events
    in if DMap.null currentOccurrences
       then Nothing
       else Just currentOccurrences

  fan :: GCompare k => Event (Model t) (DMap k) -> EventSelector (Model t) k
  fan e = EventSelector $ \k -> Event $ unEvent e >=> DMap.lookup k

  switch :: Behavior (Model t) (Event (Model t) a) -> Event (Model t) a
  switch b = Event $ memo $ \t -> unEvent (unBehavior b t) t

  coincidence :: Event (Model t) (Event (Model t) a) -> Event (Model t) a
  coincidence e = Event $ memo $ \t -> unEvent e t >>= \o -> unEvent o t

instance Ord t => MonadSample (Model t) ((->) t) where

  sample :: Behavior (Model t) a -> t -> a
  sample = unBehavior

instance (Enum t, HasTrie t, Ord t) => MonadHold (Model t) ((->) t) where

  hold   :: a -> Event (Model t) a -> t -> Behavior (Model t) a
  hold a (Event e) t0 = Behavior . memo $ \t ->
    let s = [r | r <- [t0..(pred t)], isJust (e r)]
    in if t <= t0 || null s
         then a
         else fromJust (e (last s))
