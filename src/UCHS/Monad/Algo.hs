{-# LANGUAGE DerivingVia #-}
-- {-# LANGUAGE ScopedTypeVariables #-}

module UCHS.Monad.Algo where

import Data.Kind (Type)
import Data.Void

import Data.HList

import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad

import UCHS.Monad.SyncAlgo
import UCHS.Monad.Class

-- type ZipConst :: forall f s. [f] -> s -> [(f, s)]
-- type family ZipConst fs s where
--   ZipConst '[] _ = '[]
--   ZipConst (h:rest) s = ('(h, s) : ZipConst rest s)

newtype Algo (pr :: Bool) (ra :: Bool) (ex :: Type) (a :: Type) =
  Algo { runAlgo :: SyncAlgo ('SyncPars pr ra '[ '(ex, True)] Nothing) True True a }

  deriving (Functor) via
    (SyncAlgo ('SyncPars pr ra '[ '(ex, True)] Nothing) True True)
  deriving (Applicative, Monad) via
    (SyncAlgo ('SyncPars pr ra '[ '(ex, True)] Nothing) True True)

-- Local

instance Print (Algo True ra ex) where
  debugPrint = Algo . debugPrint

instance Rand (Algo pr True ex) where
  rand = Algo rand

instance Throw (Algo pr ra e) e where
  throw = Algo . throw
