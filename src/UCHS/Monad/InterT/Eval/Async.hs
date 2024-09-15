{-# LANGUAGE AllowAmbiguousTypes #-}

module UCHS.Monad.InterT.Eval.Async where

import Data.Either.Extra (mapLeft)

import UCHS.Monad
import UCHS.Types

data ForkIndexCompT (befFst :: Index) (befSnd :: Index) where
  ForkIndexCompNone :: ForkIndexCompT NextRecv NextRecv
  ForkIndexCompFst :: ForkIndexCompT NextSend NextRecv
  ForkIndexCompSnd :: ForkIndexCompT NextRecv NextSend

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
               Chan x y ach
            -> KnownLenT ach
            -> Chan x y (Concat ach ach')
fstToConcat Here _ = Here
fstToConcat (There rest) (KnownLenS n) = There $ fstToConcat @_ @(ach') rest n

sndToConcat :: KnownLenT ach
            -> Chan x y ach'
            -> Chan x y (Concat ach ach')
sndToConcat KnownLenZ = id
sndToConcat (KnownLenS rest) = There . sndToConcat rest

fork :: forall m ach ach' bef bef' aft aft' a b.
        (ForkIndexComp bef bef', ForkIndexComp aft aft')
     => KnownLenT ach
     -> AsyncT m ach bef aft a
     -> AsyncT m ach' bef' aft' b
     -> AsyncT m (Concat ach ach') (ForkIndexOr bef bef') (ForkIndexOr aft aft') (a, b)
fork prf l r = case getIndexStartCompPrf @bef @bef' of
  ForkIndexCompNone -> undefined
  ForkIndexCompFst -> undefined
  ForkIndexCompSnd -> undefined
