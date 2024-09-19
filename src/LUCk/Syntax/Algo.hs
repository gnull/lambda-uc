module LUCk.Syntax.Algo where

import Data.Kind (Type)

import Control.Monad.Free

import LUCk.Syntax.Class

-- |Non-interactive algorithm. May use the following side-effects:
--
-- - Print debug messages if `pr == True`,
-- - Sample random values if `ra == True`,
--
-- Use `Control.Monad.Except.ExceptT` if you want algorithms with exceptions.
newtype Algo (pr :: Bool) (ra :: Bool) (a :: Type) =
    Algo { runAlgo :: Free (AlgoActions pr ra) a }
  deriving (Functor)

instance Applicative (Algo pr ra) where
  pure = Algo . pure
  f <*> x = Algo $ runAlgo f <*> runAlgo x

instance Monad (Algo pr ra) where
  m >>= f = Algo $ runAlgo m >>= (runAlgo . f)

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
