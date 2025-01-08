module LUCk.Syntax.PrAlgo
  (
  -- * Syntax
  -- $syntax
    PrAlgo(..)
  , MonadRand(..)
  , AlgoActions(..)
  -- * Distributions
  -- $dists
  , UniformDist(..)
  , rangeDist
  -- * Interpretations
  -- The following two sections define interpretations of `PrAlgo`. The pure
  -- interpretations do not require `IO` and return back to pure functions `->`
  -- in one way or another. Impure implementations, on the other hand, run
  -- probabilistic computations in `IO` using your OS PRG.
  --
  -- ** Pure
  -- $pure
  , pr
  , withRandomBits
  , collectRandomBits
  -- ** Impure
  -- $monadic
  , toMonadRand
  , runIO
  -- , writerTtoIO
  )
where

import Data.Kind (Type)

import Control.Monad.Free
-- import Control.Monad.Writer

import Control.Monad
-- import Control.XMonad
import Control.XMonad.Trans
import qualified System.Random as Random
import qualified Control.Monad.Trans.Class as Trans

-- $syntax
--
-- This section defines the syntax of `PrAlgo` monad for probabilistic algorithms.

-- |Probabilistic algorithm. Allows only one action `rand` to sample a random
-- bit.
--
-- Use with `Control.Monad.Except.ExceptT`, `Control.Monad.Maybe.MaybeT`
-- or `Control.Monad.Writer.WriterT` if you want extra side-effects such
-- exceptions or writing debug messages.
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

-- Local

instance MonadRand PrAlgo where
  rand = PrAlgo $ liftF $ RandAction id

-- |Class of monads that allow sampling a random bit.
class Monad m => MonadRand (m :: Type -> Type) where
  -- |Sample a random value.
  rand :: m Bool

instance (Trans.MonadTrans t, MonadRand m) => MonadRand (t m) where
  rand = Trans.lift rand

instance (XMonadTrans t, MonadRand m, bef ~ aft) => MonadRand (t m bef aft) where
  rand = xlift rand

instance MonadRand IO where
  rand = Random.randomIO

-- $dists
--
-- Common probability distributions.

class UniformDist s where
  -- |Sample a uniformly random value from @s@
  uniformDist :: forall m. MonadRand m => m s

instance UniformDist Bool where
  uniformDist = rand

-- |Sample a random value from the given range of `Integer`
rangeDist :: MonadRand m => Integer -> Integer -> m Integer
rangeDist = \f t -> (f +) <$> rangeDist0 (t - f)
  where
    integerLog2Ceil x | x == 1 = 1
                      | even x = 1 + integerLog2Ceil (x `div` 2)
                      | otherwise = integerLog2Ceil $ x + 1

    fromBase2 l = sum $ zipWith (*) l $ map (2^) [0 :: Integer ..]

    rangeDist0 n = do
      let p = integerLog2Ceil n
      nb <- fmap (fromBase2 . map (toInteger . fromEnum)) (replicateM p $ uniformDist @Bool)
      if nb < n then
        return nb
      else
        rangeDist0 n

-- $pure
--
-- These are the pure interpretations of `PrAlgo`, i.e. those that do not
-- require `IO`.

-- |Calculate the probability of a random event.
--
-- You can see this as a pure interpretation (not using `IO`) of `PrAlgo`.
pr :: PrAlgo Bool -> Rational
pr a = case runAlgo a of
  Pure True -> 1
  Pure False -> 0
  Free (RandAction cont) -> (pr (PrAlgo $ cont False) + pr (PrAlgo $ cont True)) / 2

-- |Run a probabilistic algorithm supplying the given stream of bits.
--
-- If the number of supplied bits was sufficient for all the `rand` requests
-- that algorithm made until it terminated, evaluates to `Right` of the
-- result. If the bits were exhausted before the algorithm was ready to
-- terminate, return `Left` of the continuation with remaining computations.
withRandomBits :: [Bool] -> PrAlgo a -> Either (Bool -> PrAlgo a) a
withRandomBits bs m = case runAlgo m of
  Pure x -> Right x
  Free (RandAction cont) -> case bs of
    [] -> Left $ PrAlgo . cont
    (x:xs) -> withRandomBits xs $ PrAlgo $ cont x

-- |Run a probabilistic algorithm, collecting the random bits it samples.
--
-- This is, in some sense, dual to `withRandomBits`: collected randomBits can
-- be fed back to an algorithm to repeat its execution.
collectRandomBits :: PrAlgo a -> PrAlgo (a, [Bool])
collectRandomBits m = case runAlgo m of
  Pure x -> pure (x, [])
  Free (RandAction cont) -> do
    x <- rand
    (a, xs) <- collectRandomBits $ PrAlgo $ cont x
    pure (a, x:xs)

-- $monadic
--
-- The following are interpretations of `PrAlgo` in `IO`.

-- |Convert an `PrAlgo` to any monad that implements `MonadRand`.
toMonadRand :: MonadRand m
            => PrAlgo a
            -> m a
toMonadRand (PrAlgo (Pure v)) = pure v
toMonadRand (PrAlgo (Free (RandAction cont))) =
  rand >>= (toMonadRand . PrAlgo . cont)

-- |Run a probabilistic algorithm in `IO`.
--
-- The random bits are faithfully sampled using OS RNG.
runIO :: PrAlgo a -> IO a
runIO = toMonadRand
