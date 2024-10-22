module LUCk.Syntax.PrAlgo where

import Data.Kind (Type)

import Control.Monad.Free
import Control.Monad.Writer

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
newtype PrAlgo a =
    PrAlgo { runAlgo :: Free AlgoActions a }
  deriving (Functor)

instance Applicative PrAlgo where
  pure = PrAlgo . pure
  f <*> x = PrAlgo $ runAlgo f <*> runAlgo x

instance Monad PrAlgo where
  m >>= f = PrAlgo $ runAlgo m >>= (runAlgo . f)

data AlgoActions (a :: Type) where
  RandAction :: (Bool -> a) -> AlgoActions a

instance Functor AlgoActions where
  fmap f (RandAction cont) = RandAction $ f . cont

-- |Calculate the probability of a random event
pr :: PrAlgo Bool -> Rational
pr a = case runAlgo a of
  Pure True -> 1
  Pure False -> 0
  Free (RandAction cont) -> (pr (PrAlgo $ cont False) + pr (PrAlgo $ cont True)) / 2

-- Local

instance MonadRand PrAlgo where
  rand = PrAlgo $ liftF $ RandAction id

class Monad m => MonadRand (m :: Type -> Type) where
  -- |Sample a random value.
  rand :: m Bool

instance (Trans.MonadTrans t, MonadRand m) => MonadRand (t m) where
  rand = Trans.lift $ rand

instance (XMonadTrans t, MonadRand m, bef ~ aft) => MonadRand (t m bef aft) where
  rand = xlift $ rand

instance MonadRand IO where
  rand = Random.randomIO

class UniformDist s where
  -- |Sample a uniformly random value from `s`
  uniformDist :: forall m. MonadRand m => m s

instance UniformDist Bool where
  uniformDist = rand

-- |Sample a random value from the given range of `Integer`
rangeDist :: MonadRand m => Integer -> Integer -> m Integer
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

toMonadRand :: MonadRand m
               => PrAlgo a
               -> m a
toMonadRand (PrAlgo (Pure v)) = pure v
toMonadRand (PrAlgo (Free v)) =
  case v of
    RandAction cont -> rand >>= (\b -> toMonadRand $ PrAlgo $ cont b)

toIO :: PrAlgo a -> IO a
toIO = toMonadRand

writerTtoIO :: WriterT [String] PrAlgo a
                      -> IO a
writerTtoIO m = do
  (a, w) <- toMonadRand $ runWriterT m
  putStrLn $ unlines w
  pure a
