{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Monad.UCHS.Classes where

import Data.Kind
import Data.HList

import Control.XMonad

import qualified Control.Monad.UCHS.Local as L
import qualified Control.Monad.UCHS.Sync as S

class Monad m => Print (m :: Type -> Type) where
  debugPrint :: String -> m ()

class Monad m => Rand (m :: Type -> Type) where
  rand :: m Bool

class Monad m => Throw (m :: Type -> Type) (e :: Type) | m -> e where
  throw :: e -> m a

class XMonad m => XThrow (m :: Bool -> Bool -> Type -> Type) (ex :: [(Type, Bool)]) | m -> ex where
  xthrow :: InList '(e, b) ex -> e -> m b b' a

-- $local

instance Print (L.Algo True ra ex) where
  debugPrint = L.Algo . S.debugPrint

instance Rand (L.Algo pr True ex) where
  rand = L.Algo S.rand

instance Throw (L.Algo pr ra e) e where
  throw = L.Algo . S.throw Here

-- $sync

instance Print (S.SyncAlgo ('S.SyncPars True ra ex up down) b b) where
  debugPrint = S.debugPrint

instance Rand (S.SyncAlgo ('S.SyncPars pr True ex up down) b b) where
  rand = S.rand

instance Throw (S.SyncAlgo ('S.SyncPars pr ra '[ '(ex, b)] up down) b b) ex where
  throw = S.throw Here

instance XThrow (S.SyncAlgo ('S.SyncPars pr ra ex up down)) ex where
  xthrow = S.throw

-- $async

