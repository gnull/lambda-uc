module UCHS.Games.SignatureScheme where

import UCHS.Types
import UCHS.Monad.Class
import UCHS.Monad.Algo
import UCHS.Monad.InterT
import UCHS.Monad.Extra

import Control.XMonad
import Control.XFreer.Join
import qualified Control.XMonad.Do as M

import Data.Maybe (isJust)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad (MonadPlus(..))
-- import qualified Control.Monad.Trans.Class as Trans

type SigAlgo :: Bool -> Type -> Type
type SigAlgo ra = Algo False ra

data SignatureScheme sk pk mes sig = SignatureScheme
  { sigKey :: forall m. Rand m => m (sk, pk)
  , sigSign :: forall m. Rand m => sk -> mes -> m sig
  , sigVer :: pk -> mes -> sig -> Bool
  }

type SpSignatureScheme sk pk mes sig = Integer -> SignatureScheme sk pk mes sig

-- |Oracle that computes the given monadic function upon request. When
-- requested to terminate, returns the list of all request-response pairs it
-- got.
oracleMapM :: (Monad m)
           => (a -> m b)
           -> OracleWrapper m '(a, b) [(a, b)]
oracleMapM f = OracleWrapper $ M.do
  accept >>=: \case
    OracleReqHalt -> xreturn []
    OracleReq x -> M.do
      y <- lift $ f x
      yield y
      rest <- runOracleWrapper $ oracleMapM f
      xreturn $ (x, y) : rest

type AdvAlgo pk mes sig = pk -> OracleCallerWrapper (SigAlgo True) '[ '(mes, sig) ] (mes, sig)
type SpAdvAlgo pk mes sig = Integer -> AdvAlgo pk mes sig

-- |Existential Unforgeability under Chosen Message Attack, EU-CMA
gameEuCma :: Eq mes
          => Integer
          -- ^Security parameter
          -> SpSignatureScheme sk pk mes sig
          -- ^Signature scheme
          -> SpAdvAlgo pk mes sig
          -- ^Adversary
          -> SigAlgo True Bool
gameEuCma sec sch adv = do
  let sch' = sch sec
  (sk, pk) <- sigKey sch'
  fmap isJust $ runMaybeT $ do
    ((m, sig), q) <- runWithOracles1 (adv sec pk) $ (oracleMapM $ sigSign sch' sk)
    -- check that the guess is correct
    True <- pure $ sigVer sch' pk m sig
    -- check that it was never queried
    assert $ not $ any (\(m', _) -> m' == m) q
    return ()

assert :: MonadPlus m => Bool -> m ()
assert True = pure ()
assert False = mzero
