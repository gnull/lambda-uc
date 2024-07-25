{-# LANGUAGE DerivingVia #-}
-- {-# LANGUAGE ScopedTypeVariables #-}

module UCHS.Monad.Algo where

import Data.Kind (Type)
import Data.Void

import Data.HList

import Control.Monad.Free

-- import Control.XFreer.Join
-- import Control.XApplicative
-- import Control.XMonad

-- import UCHS.Monad.SyncAlgo
import UCHS.Monad.Class

-- |Non-interactive algorithm. May use the following side-effects:
--
-- - Print debug messages if `pr == True`,
-- - Sample random values if `ra == True`,
--
-- Use `Control.Monad.Except.ExceptT` if you want algorithms with exceptions.
newtype Algo (pr :: Bool) (ra :: Bool) (a :: Type) =
    Algo { fromAlgo :: Free (AlgoActions pr ra) a }
  deriving (Functor) via
    (Free (AlgoActions pr ra))
  deriving (Applicative, Monad) via
    (Free (AlgoActions pr ra))

data AlgoActions (pr :: Bool) (ra :: Bool) (a :: Type) where
  PrintAction :: String -> a -> AlgoActions True ra a
  RandAction :: (Bool -> a) -> AlgoActions pr True a

instance Functor (AlgoActions pr ra) where
  fmap f (PrintAction x r) = PrintAction x $ f r
  fmap f (RandAction cont) = RandAction $ f . cont

-- Local

instance Print (Algo True ra) where
  debugPrint s = Algo $ liftF $ PrintAction s ()

instance Rand (Algo pr True) where
  rand = Algo $ liftF $ RandAction id

-- instance Throw (Algo pr ra e) e where
--   throw = Algo . throw

-- instance Catch (Algo pr ra e) e (Algo pr ra e') where
--   catch x h = Algo $ catch (runAlgo x) (runAlgo . h)

-- $eval
