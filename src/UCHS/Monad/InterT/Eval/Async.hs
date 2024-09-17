{-# LANGUAGE AllowAmbiguousTypes #-}

module UCHS.Monad.InterT.Eval.Async
  (
  -- * Core combinators
  -- $core
    fork
  -- , mapTail
  , swap
  , connect
  , connectSelf
  -- *Helper functions and types
  -- $helpers
  , chanFromConcat
  , fstToConcat
  , sndToConcat
  , ForkIndexComp(..)
  , ForkIndexCompT(..)
  , ForkIndexOr
  , MayOnlyReturnAfterRecv(..)
  , MayOnlyReturnAfterRecvT(..)
  , ChooseRet
  )
where

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

-- |Given an index in the concatenation of @`Concat` ach ach'@, return the
-- corresponding element's index either in @ach@ or in @ach'@.
chanFromConcat :: forall (ach :: [(Type, Type)]) ach' x y.
                  KnownLenT ach
               -> Chan x y (Concat ach ach')
               -> Either (Chan x y ach) (Chan x y ach')
chanFromConcat = \case
  KnownLenZ -> Right
  KnownLenS rest -> \case
    Here -> Left Here
    There ch -> mapLeft There $ chanFromConcat rest ch

-- |Given an element's index in @ach@, return the same element's index in @`Concat` ach ach'@.
fstToConcat :: forall ach ach' x y.
               KnownLenT ach
            -> Chan x y ach
            -> Chan x y (Concat ach ach')
fstToConcat _ Here = Here
fstToConcat (KnownLenS n) (There rest) = There $ fstToConcat @_ @(ach') n rest

-- |Given an element's index in @ach'@, return the same element's index in @`Concat` ach ach'@.
sndToConcat :: forall ach ach' x y.
               KnownLenT ach
            -> Chan x y ach'
            -> Chan x y (Concat ach ach')
sndToConcat KnownLenZ = id
sndToConcat (KnownLenS n) = There . sndToConcat n

-- |Run two processes in parallel exposing the channels of both of them.
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
      Left i' -> lift (runTillRecv l) >>=: \case
        RrRecv l' -> fork prf (l' $ SomeSndMessage i' m) r
        RrCall contra _ _ -> case contra of {}
        RrHalt res -> case mayOnlyReturnAfterRecvPrf @aft @a of
          MayOnlyReturnVoid -> case res of {}
      Right i' -> lift (runTillRecv r) >>=: \case
        RrRecv r' -> fork prf l (r' $ SomeSndMessage i' m)
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

-- -- |Apply the given action to the tail of the channels list, keeping the head unchanged.
-- mapTail :: ( KnownIndex bef
--            , Monad m
--            )
--         => AsyncT m (h:ach) bef aft a
--         -- ^Original action
--         -> (forall i. KnownIndex i => AsyncT m ach i aft a -> AsyncT m ach' i aft a)
--         -- ^What to do with the tail of the channels list
--         -> AsyncT m (h:ach') bef aft a
--         -- ^Result with tail changed
-- mapTail x f = getWT >>=: \case
--   SNextSend -> M.do
--     lift (runTillSend x) >>=: \case
--       SrSend (SomeFstMessage i m) cont -> case i of
--         Here -> M.do
--           send Here m
--           mapTail cont f
--         There i' -> M.do
--           undefined
--       SrCall contra _ _ -> case contra of {}
--       SrHalt res -> xreturn res
--   SNextRecv -> undefined

-- |Swap the two adjacent channels.
swap :: ( KnownIndex bef
        , Monad m
        )
     => ListSplit l p (f:s:rest)
     -> ListSplit l' p (s:f:rest)
     -> AsyncT m l bef aft a
     -> AsyncT m l' bef aft a
swap SplitHere SplitHere cont = getWT >>=: \case
  SNextRecv -> M.do
    lift (runTillRecv cont) >>=: \case
      RrCall contra _ _ -> case contra of {}
      RrHalt res -> xreturn res
      RrRecv cont' -> M.do
        SomeSndMessage i m <- recvAny
        swap SplitHere SplitHere $ case i of
          Here -> cont' (SomeSndMessage (There Here) m)
          There Here -> cont' (SomeSndMessage Here m)
          There2 i' -> cont' (SomeSndMessage (There2 i') m)
  SNextSend -> M.do
    lift (runTillSend cont) >>=: \case
      SrCall contra _ _ -> case contra of {}
      SrHalt res -> xreturn res
      SrSend (SomeFstMessage i m) cont' -> M.do
        case i of
          Here -> send (There Here) m
          There Here -> send Here m
          There2 i' -> send (There2 i') m
        swap SplitHere SplitHere cont'
swap (SplitThere prf) (SplitThere prf') cont= undefined
-- swap prf prf' cont = getWT >>=: \case
--   SNextRecv -> M.do
--     SomeSndMessage i m <- recvAny
--     case
--   SNextSend -> _

-- |Connect the first two channels with each other.
connect :: AsyncT m ('(x, y) : '(y, x) : rest) bef aft a
        -> AsyncT m rest bef aft a
connect = undefined

-- |Connect the first channel to itself.
connectSelf :: AsyncT m ('(x, x) : rest) bef aft a
            -> AsyncT m rest bef aft a
connectSelf = undefined
