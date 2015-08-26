{- | This module provides a pure implementation of Reflex, which is intended
to serve as a reference for the semantics of the Reflex class.  All implementations
of Reflex should produce the same results as this implementation, although performance
and laziness/strictness may differ.
-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Reflex.Pure where

import           Data.Functor.Misc
import           Reflex.Class

import           Data.Dependent.Map (DMap, GCompare)
import qualified Data.Dependent.Map as DMap
import           Data.MemoTrie

import qualified Semantics          as S

instance Reflex Int where

  newtype Behavior Int a = Behavior { unBehavior :: Int -> a }
  newtype Event Int a    = Event { unEvent :: Int -> Maybe a }

  type PushM Int = (->) Int
  type PullM Int = (->) Int

  never :: Event Int a
  never = Event $ S.unEvent S.never

  constant :: a -> Behavior Int a
  constant x = Behavior $ S.unBehavior (pure x)

  push :: (a -> PushM Int (Maybe b)) -> Event Int a -> Event Int b
  push f e = Event $ S.unEvent (S.push f' e')
   where
     f' x = S.Push $ f x
     e'   = S.Event $ unEvent e

  pull :: PullM Int a -> Behavior Int a
  pull = Behavior . memo

  merge :: GCompare k => DMap (WrapArg (Event Int) k) -> Event Int (DMap k)
  merge events = Event $ memo $ \t ->
    let currentOccurrences = unwrapDMapMaybe (($ t) . unEvent) events
    in if DMap.null currentOccurrences
       then Nothing
       else Just currentOccurrences

  fan :: GCompare k => Event Int (DMap k) -> EventSelector Int k
  fan e = EventSelector $ \k -> Event $ \t -> unEvent e t >>= DMap.lookup k

  switch :: Behavior Int (Event Int a) -> Event Int a
  switch b = Event . S.unEvent $ S.switch b'
    where
      e  = S.Event $ \t -> (unEvent $ unBehavior b t) t
      b' = S.Behavior $ const e

  coincidence :: Event Int (Event Int a) -> Event Int a
  coincidence  ee = Event . S.unEvent . S.coincidence  $ S.Event (const (Just e))
    where
      e = S.Event $ \t -> (f $ unEvent ee t) t
      f = maybe (const Nothing) unEvent

instance MonadSample Int ((->) Int) where

  sample :: Behavior Int a -> Int -> a
  sample = unBehavior

instance MonadHold Int ((->) Int) where

  hold :: a -> Event Int a -> Int -> Behavior Int a
  hold initialValue e initialTime = Behavior . S.unBehavior $ b initialTime
    where
      b  = S.unPush $ S.hold initialValue e'
      e' = S.Event $ unEvent e
