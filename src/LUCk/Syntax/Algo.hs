module LUCk.Syntax.Algo where

import Data.Kind (Type)

import Control.Monad.Free

import Control.Monad
-- import Control.XMonad
import Control.XMonad.Trans
import qualified System.Random as Random
import qualified Control.Monad.Trans.Class as Trans

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

class Monad m => Print (m :: Type -> Type) where
  -- |Print debug info.
  --
  -- This has no effect on the algorithm definition, i.e. all `debugPrint`
  -- calls are ignored when your protocol is converted into a real-world
  -- implementation. But you may use print statements to illustrate your
  -- algorithms in toy executions.
  debugPrint :: String -> m ()

instance Print IO where
  debugPrint = putStrLn

instance (Trans.MonadTrans t, Print m) => Print (t m) where
  debugPrint = Trans.lift . debugPrint

instance (XMonadTrans t, Print m, bef ~ aft) => Print (t m bef aft) where
  debugPrint = xlift . debugPrint

class Monad m => Rand (m :: Type -> Type) where
  -- |Sample a random value.
  rand :: m Bool

instance (Trans.MonadTrans t, Rand m) => Rand (t m) where
  rand = Trans.lift $ rand

instance (XMonadTrans t, Rand m, bef ~ aft) => Rand (t m bef aft) where
  rand = xlift $ rand

instance Rand IO where
  rand = Random.randomIO

class UniformDist s where
  -- |Sample a uniformly random value from `s`
  uniformDist :: forall m. Rand m => m s

instance UniformDist Bool where
  uniformDist = rand

-- |Sample a random value from the given range of `Integer`
rangeDist :: Rand m => Integer -> Integer -> m Integer
rangeDist = \f t -> (f +) <$> rangeDist0 (t - f)
  where
    integerLog2Ceil x | x == 1 = 1
                      | x `mod` 2 == 0 = 1 + integerLog2Ceil (x `div` 2)
                      | otherwise = integerLog2Ceil $ x + 1

    fromBase2 l = sum $ zipWith (*) l $ map (2^) [0..]

    rangeDist0 n = do
      let p = integerLog2Ceil n
      nb <- fmap fromBase2 $ fmap (map $ toInteger . fromEnum) $ replicateM p $ uniformDist @Bool
      if nb < n then
        return nb
      else
        rangeDist0 n
