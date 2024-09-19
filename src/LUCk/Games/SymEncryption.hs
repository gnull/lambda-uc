{-# LANGUAGE ScopedTypeVariables #-}

module LUCk.Games.SymEncryption where

import LUCk.Types
import LUCk.Syntax.Class
import LUCk.Syntax.Algo
import LUCk.Syntax.Async
import LUCk.Syntax.Sync.Eval
import LUCk.Syntax.Extra

import Control.XMonad
import Control.XFreer.Join
import qualified Control.XMonad.Do as M

import Data.Maybe (isJust, fromMaybe, fromJust)
import Data.Default (Default(..))
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Trans.State (StateT(..), evalStateT)
import Control.Monad (MonadPlus(..))
import Control.Monad.State (MonadState(..))
-- import qualified Control.Monad.Trans.Class as Trans

import LUCk.Games.Common

type ProbAlgo :: Type -> Type
type ProbAlgo = Algo False True

data SymEncryptionScheme key mes ciph s = SymEncryptionScheme
  { symEKey :: forall m. Rand m => m key
  , symEEnc :: forall m. Rand m
            => key -> mes -> s -> m (Maybe (s, ciph))
            -- ^Probabilistic, stateful computation that may fail,
            --
            -- This is equivalent to `key -> mes -> StateT s (MaybeT m) ciph`.
  , symEDec :: key -> ciph -> Maybe mes
            -- ^Deterministic, stateless computation that may fail
  }

type SpSymEncryptionScheme key mes ciph s = Integer -> SymEncryptionScheme key mes ciph s

data EncDecReq mes ciph = EncReq mes | DecReq ciph
data EncDecResp mes ciph = EncResp ciph | DecResp mes | RespError

type EncDecIface mes ciph = '(EncDecReq mes ciph, EncDecResp mes ciph)

type AdvAlgo mes ciph
  = OracleCaller ProbAlgo '[ EncDecIface mes ciph ] Bool

advantageIndCca2 :: forall key mes ciph s. (UniformDist mes, Default s)
                 => Integer
                 -- ^Security parameter
                 -> SpSymEncryptionScheme key mes ciph s
                 -- ^Encryption scheme
                 -> (Integer -> AdvAlgo mes ciph)
                 -- ^Adversary
                 -> Rational
advantageIndCca2 sec sch adv = pr real - pr bogus
  where
    sch' = sch sec
    adv' = adv sec

    real = do
      k <- symEKey sch'
      (b, ()) <- fmap fromJust $ runMaybeT
               $ runWithOracles1 adv' $ OracleWrapper $ oracleEncDec sch' k def
      pure b

    bogus = do
      k <- symEKey sch'
      (b, ()) <- fmap fromJust $ runMaybeT
               $ runWithOracles1 adv' $ OracleWrapper $ oracleEncRandDec sch' k def
      pure b

-- |Authenticated Encryption formulated as a form of Indistinguishability under
-- Chosen Ciphertext Attack, see https://eprint.iacr.org/2004/272
--
-- TODO: implement without-loss-of-generality logic for the adversary here
advantageIndCca3 :: forall key mes ciph s. (UniformDist mes, Default s)
                 => Integer
                 -- ^Security parameter
                 -> SpSymEncryptionScheme key mes ciph s
                 -- ^Encryption scheme
                 -> (Integer -> AdvAlgo mes ciph)
                 -- ^Adversary
                 -> Rational
advantageIndCca3 sec sch adv = pr real - pr bogus
  where
    sch' = sch sec
    adv' = adv sec

    real = do
      k <- symEKey sch'
      (b, ()) <- fmap fromJust $ runMaybeT
               $ runWithOracles1 adv' $ OracleWrapper $ oracleEncDec sch' k def
      pure b

    bogus = do
      k <- symEKey sch'
      (b, ()) <- fmap fromJust $ runMaybeT
               $ runWithOracles1 adv' $ OracleWrapper $ oracleEncRandNoDec sch' k def
      pure b

oracleEncDec :: SymEncryptionScheme key mes ciph s
             -> key
             -> s
             -> Oracle ProbAlgo (EncDecIface mes ciph) ()
oracleEncDec sch' k s = M.do
  recvOne >>=: \case
    OracleReqHalt -> xreturn ()
    OracleReq req -> M.do
      (s', c) <- case req of
        EncReq m -> lift $ do
          symEEnc sch' k m s >>= \case
            Nothing -> pure (s, RespError)
            Just (s', x) -> pure $ (s', EncResp x)
        DecReq c -> lift $ fmap (s,) $ do
          case symEDec sch' k c of
            Nothing -> pure RespError
            Just x -> pure $ DecResp x
      sendOne c
      oracleEncDec sch' k s'

oracleEncRandNoDec :: UniformDist mes
                   => SymEncryptionScheme key mes ciph s
                   -> key
                   -> s
                   -> Oracle ProbAlgo (EncDecIface mes ciph) ()
oracleEncRandNoDec sch' k s = M.do
  recvOne >>=: \case
    OracleReqHalt -> xreturn ()
    OracleReq req -> M.do
      (s', c) <- case req of
        EncReq _ -> lift $ do
          m <- uniformDist
          symEEnc sch' k m s >>= \case
            Nothing -> pure (s, RespError)
            Just (s', x) -> pure $ (s', EncResp x)
        DecReq _ -> xreturn (s, RespError)
      sendOne c
      oracleEncRandNoDec sch' k s'

oracleEncRandDec :: UniformDist mes
                 => SymEncryptionScheme key mes ciph s
                 -> key
                 -> s
                 -> Oracle ProbAlgo (EncDecIface mes ciph) ()
oracleEncRandDec sch' k s = M.do
  recvOne >>=: \case
    OracleReqHalt -> xreturn ()
    OracleReq req -> M.do
      (s', c) <- case req of
        EncReq _ -> lift $ do
          m <- uniformDist
          symEEnc sch' k m s >>= \case
            Nothing -> pure (s, RespError)
            Just (s', x) -> pure $ (s', EncResp x)
        DecReq c -> lift $ fmap (s,) $ do
          case symEDec sch' k c of
            Nothing -> pure RespError
            Just x -> pure $ DecResp x
      sendOne c
      oracleEncRandNoDec sch' k s'
