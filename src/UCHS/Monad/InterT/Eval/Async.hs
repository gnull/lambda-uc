{-# LANGUAGE AllowAmbiguousTypes #-}

module UCHS.Monad.InterT.Eval.Async where

import Data.Either.Extra (mapLeft)

import Control.XMonad
import qualified Control.XMonad.Do as M

import UCHS.Monad
import UCHS.Types

data ForkIndexCompT (befFst :: Index) (befSnd :: Index) where
  ForkIndexCompNone :: ForkIndexCompT NextRecv NextRecv
  ForkIndexCompFst :: ForkIndexCompT NextSend NextRecv
  ForkIndexCompSnd :: ForkIndexCompT NextRecv NextSend

type ForkIndexComp :: Index -> Index -> Constraint
class ForkIndexComp befFst befSnd where
  getIndexStartCompPrf :: ForkIndexCompT befFst befSnd

instance ForkIndexComp NextRecv NextRecv where
  getIndexStartCompPrf = ForkIndexCompNone
instance ForkIndexComp NextSend NextRecv where
  getIndexStartCompPrf = ForkIndexCompFst
instance ForkIndexComp NextRecv NextSend where
  getIndexStartCompPrf = ForkIndexCompSnd

type ForkIndexOr :: Index -> Index -> Index
type family ForkIndexOr bef bef' where
  ForkIndexOr NextSend NextRecv = NextSend
  ForkIndexOr NextRecv NextSend = NextSend
  ForkIndexOr NextRecv NextRecv = NextRecv

data MayOnlyReturnAfterRecvT (i :: Index) (a :: Type) where
  MayOnlyReturnVoid :: MayOnlyReturnAfterRecvT i Void
  MayOnlyReturnType :: MayOnlyReturnAfterRecvT NextSend a

type family ChooseRet i i' a a' where
  ChooseRet NextRecv NextRecv _ _ = Void
  ChooseRet NextSend _ a _ = a
  ChooseRet _ NextSend _ a' = a'

type MayOnlyReturnAfterRecv :: Index -> Type -> Constraint
class MayOnlyReturnAfterRecv i a where
  mayOnlyReturnAfterRecvPrf :: MayOnlyReturnAfterRecvT i a
instance MayOnlyReturnAfterRecv i Void where
  mayOnlyReturnAfterRecvPrf = MayOnlyReturnVoid
instance MayOnlyReturnAfterRecv NextSend a where
  mayOnlyReturnAfterRecvPrf = MayOnlyReturnType

chanFromConcat :: forall (ach :: [(Type, Type)]) ach' x y.
               KnownLenT ach
               -> Chan x y (Concat ach ach')
               -> Either (Chan x y ach) (Chan x y ach')
chanFromConcat = \case
  KnownLenZ -> Right
  KnownLenS rest -> \case
    Here -> Left Here
    There ch -> mapLeft There $ chanFromConcat rest ch

fstToConcat :: forall ach ach' x y.
               KnownLenT ach
            -> Chan x y ach
            -> Chan x y (Concat ach ach')
fstToConcat _ Here = Here
fstToConcat (KnownLenS n) (There rest) = There $ fstToConcat @_ @(ach') n rest

sndToConcat :: forall ach ach' x y.
               KnownLenT ach
            -> Chan x y ach'
            -> Chan x y (Concat ach ach')
sndToConcat KnownLenZ = id
sndToConcat (KnownLenS n) = There . sndToConcat n

fork :: forall m ach ach' bef bef' aft aft' a a'.
        ( Monad m
        , ForkIndexComp bef bef'
        , ForkIndexComp aft aft'
        , MayOnlyReturnAfterRecv aft a
        , MayOnlyReturnAfterRecv aft' a'
        )
     => KnownLenT ach
     -> AsyncT m ach bef aft a
     -> AsyncT m ach' bef' aft' a'
     -> AsyncT m (Concat ach ach') (ForkIndexOr bef bef') (ForkIndexOr aft aft') (ChooseRet aft aft' a a')
fork prf l r = case getIndexStartCompPrf @bef @bef' of
  ForkIndexCompNone -> M.do
    SomeSndMessage i m <- recvAny
    case chanFromConcat @ach @ach' prf i of
      Left i' -> lift (runTillRecv (SomeSndMessage i' m) l) >>=: \case
        RrRecv l' -> fork prf l' r
        RrCall contra _ _ -> case contra of {}
        RrHalt res -> case mayOnlyReturnAfterRecvPrf @aft @a of
          MayOnlyReturnVoid -> case res of {}
      Right i' -> lift (runTillRecv (SomeSndMessage i' m) r) >>=: \case
        RrRecv r' -> fork prf l r'
        RrCall contra _ _ -> case contra of {}
        RrHalt res -> case mayOnlyReturnAfterRecvPrf @aft' @a' of
          MayOnlyReturnVoid -> case res of {}
  ForkIndexCompFst ->
    lift (runTillSend l) >>=: \case
      SrSend (SomeFstMessage i m) cont -> M.do
        send (fstToConcat @ach @ach' prf i) m
        fork prf cont r
      SrCall contra _ _ -> case contra of {}
      SrHalt res -> case mayOnlyReturnAfterRecvPrf @aft @a of
        MayOnlyReturnVoid -> case res of {}
        MayOnlyReturnType -> case getIndexStartCompPrf @aft @aft' of
          ForkIndexCompFst -> xreturn res
  ForkIndexCompSnd ->
    lift (runTillSend r) >>=: \case
      SrSend (SomeFstMessage i m) cont -> M.do
        send (sndToConcat @ach @ach' prf i) m
        fork prf l cont
      SrCall contra _ _ -> case contra of {}
      SrHalt res -> case mayOnlyReturnAfterRecvPrf @aft' @a' of
        MayOnlyReturnVoid -> case res of {}
        MayOnlyReturnType -> case getIndexStartCompPrf @aft @aft' of
          ForkIndexCompSnd -> xreturn res
