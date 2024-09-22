{-# LANGUAGE AllowAmbiguousTypes #-}

module LUCk.Syntax.Async.Eval.Internal
  (
  -- * Execution Implementation
  -- $core
    fork_
  , swap_
  , connect_
  -- ** Unsafe
  , permChans
  -- *Helper functions and types
  -- $helpers
  , ForkPremiseD(..)
  , getForkPremiseD
  , ForkIndexComp(..)
  , ForkIndexCompD(..)
  , ForkIndexOr
  , MayOnlyReturnAfterRecv(..)
  , MayOnlyReturnAfterRecvD(..)
  , ChooseRet
  ) where

import Data.Either.Extra (mapLeft)

import Control.Arrow
import Control.XMonad
import Control.XMonad.Trans
import qualified Control.XMonad.Do as M

import LUCk.Syntax
import LUCk.Types

data ForkIndexCompD (befFst :: Index) (befSnd :: Index) where
  ForkIndexCompNone :: ForkIndexCompD NextRecv NextRecv
  ForkIndexCompFst :: ForkIndexCompD NextSend NextRecv
  ForkIndexCompSnd :: ForkIndexCompD NextRecv NextSend

type ForkIndexComp :: Index -> Index -> Constraint
class ForkIndexComp befFst befSnd where
  getForkIndexComp :: ForkIndexCompD befFst befSnd

instance KnownIndex i => ForkIndexComp NextRecv i where
  getForkIndexComp = case getSIndex @i of
    SNextRecv -> ForkIndexCompNone
    SNextSend -> ForkIndexCompSnd
instance (i ~ NextRecv) => ForkIndexComp NextSend i where
  getForkIndexComp = ForkIndexCompFst

type ForkIndexOr :: Index -> Index -> Index
type family ForkIndexOr bef bef' where
  ForkIndexOr NextSend NextRecv = NextSend
  ForkIndexOr NextRecv NextSend = NextSend
  ForkIndexOr NextRecv NextRecv = NextRecv

data MayOnlyReturnAfterRecvD (i :: Index) (a :: Type) where
  MayOnlyReturnVoid :: MayOnlyReturnAfterRecvD i Void
  MayOnlyReturnType :: MayOnlyReturnAfterRecvD NextSend a

type family ChooseRet i i' a a' where
  ChooseRet NextRecv NextRecv _ _ = Void
  ChooseRet NextSend _ a _ = a
  ChooseRet _ NextSend _ a' = a'

type MayOnlyReturnAfterRecv :: Index -> Type -> Constraint
class MayOnlyReturnAfterRecv i a where
  getMayOnlyReturnAfterRecvPrf :: MayOnlyReturnAfterRecvD i a
instance MayOnlyReturnAfterRecv NextRecv Void where
  getMayOnlyReturnAfterRecvPrf = MayOnlyReturnVoid
instance MayOnlyReturnAfterRecv NextSend a where
  getMayOnlyReturnAfterRecvPrf = MayOnlyReturnType

-- |Given an index in the concatenation of @`Concat` ach ach'@, return the
-- corresponding element's index either in @ach@ or in @ach'@.
chanFromConcat :: forall (ach :: [(Type, Type)]) ach' x y.
                  KnownLenD ach
               -> Chan x y (Concat ach ach')
               -> Either (Chan x y ach) (Chan x y ach')
chanFromConcat = \case
  KnownLenZ -> Right
  KnownLenS rest -> \case
    Here -> Left Here
    There ch -> mapLeft There $ chanFromConcat rest ch

-- |Given an element's index in @ach@, return the same element's index in @`Concat` ach ach'@.
fstToConcat :: forall ach ach' x y.
               KnownLenD ach
            -> Chan x y ach
            -> Chan x y (Concat ach ach')
fstToConcat _ Here = Here
fstToConcat (KnownLenS n) (There rest) = There $ fstToConcat @_ @(ach') n rest

-- |Given an element's index in @ach'@, return the same element's index in @`Concat` ach ach'@.
sndToConcat :: forall ach ach' x y.
               KnownLenD ach
            -> Chan x y ach'
            -> Chan x y (Concat ach ach')
sndToConcat KnownLenZ = id
sndToConcat (KnownLenS n) = There . sndToConcat n

-- $core
--
-- These are utility functions that are used by `runExec` to evaluate an exection.
--
-- The `fork_`, `swap_` and `connect_` correspond one-to-one to the constructors
-- of `Exec`. And `escapeSyncT` evaluates a concurrent algorithm that has all
-- of its channels bound as a local algorithm.

data ForkPremiseD bef bef' aft aft' a a' = ForkPremiseD
  { forkPremiseIndexCompBef :: ForkIndexCompD bef bef'
  , forkPremiseIndexCompAft :: ForkIndexCompD aft aft'
  , forkPremiseRet :: MayOnlyReturnAfterRecvD aft a
  , forkPremiseRet' :: MayOnlyReturnAfterRecvD aft' a'
  }

getForkPremiseD :: ( ForkIndexComp bef bef'
                   , ForkIndexComp aft aft'
                   , MayOnlyReturnAfterRecv aft a
                   , MayOnlyReturnAfterRecv aft' a'
                   )
                => ForkPremiseD bef bef' aft aft' a a'
getForkPremiseD =
  ForkPremiseD getForkIndexComp
               getForkIndexComp
               getMayOnlyReturnAfterRecvPrf
               getMayOnlyReturnAfterRecvPrf

-- |Run two processes in parallel exposing the free channels of both of them.
--
-- The typeclass constaint `Forkable` here ensures that:
--
-- 1. No more than one of forked processes expects to finish in `NextSend`.
-- 2. Only the process that finishes in `NextSend` is allowed to produce a (non-`Void`) result.
--
-- The resulting action that implements the fork_ starts in `NextSend` if one
-- of the forked actions started in `NextSend`. Similarly, it finishes in
-- `NextSend` if one of the forked two finishes in `NextSend`. (Implemented
-- with `ForkIndexOr`.)
--
-- The return value of the fork_ is the same as return value of process that
-- finishes in `NextSend`. If both finish in `NextRecv`, then fork_'s return
-- value is `Void`.
fork_ :: forall m ach ach' bef bef' aft aft' a a'.
        (Monad m)
     => ForkPremiseD bef bef' aft aft' a a'
     -- ^Proof that this combination of indices and return values is valid
     -> KnownLenD ach
     -- ^Depdendent length of free channels list in left branch
     -> AsyncT ach m bef aft a
     -- ^Left branch of the fork_
     -> AsyncT ach' m bef' aft' a'
     -- ^Right branch of the fork_
     -> AsyncT (Concat ach ach') m (ForkIndexOr bef bef') (ForkIndexOr aft aft') (ChooseRet aft aft' a a')
fork_ fPrf lPrf l r = case forkPremiseIndexCompBef fPrf of
  ForkIndexCompNone -> M.do
    SomeSndMessage i m <- recvAny
    case chanFromConcat @ach @ach' lPrf i of
      Left i' -> xlift (runTillRecv l) >>=: \case
        RrRecv l' -> M.do
          let fPrf' = fPrf {forkPremiseIndexCompBef = getForkIndexComp}
          fork_ fPrf' lPrf (l' $ SomeSndMessage i' m) r
        RrHalt res -> case forkPremiseRet fPrf of
          MayOnlyReturnVoid -> case res of {}
      Right i' -> xlift (runTillRecv r) >>=: \case
        RrRecv r' -> M.do
          let fPrf' = fPrf {forkPremiseIndexCompBef = getForkIndexComp}
          fork_ fPrf' lPrf l (r' $ SomeSndMessage i' m)
        RrHalt res -> case forkPremiseRet' fPrf of
          MayOnlyReturnVoid -> case res of {}
  ForkIndexCompFst ->
    xlift (runTillSend l) >>=: \case
      SrSend (SomeFstMessage i m) cont -> M.do
        send (fstToConcat @ach @ach' lPrf i) m
        let fPrf' = fPrf {forkPremiseIndexCompBef = getForkIndexComp}
        fork_ fPrf' lPrf cont r
      SrHalt res -> case forkPremiseRet fPrf of
        MayOnlyReturnVoid -> case res of {}
        MayOnlyReturnType -> case forkPremiseIndexCompAft fPrf of
          ForkIndexCompFst -> xreturn res
  ForkIndexCompSnd ->
    xlift (runTillSend r) >>=: \case
      SrSend (SomeFstMessage i m) cont -> M.do
        send (sndToConcat @ach @ach' lPrf i) m
        let fPrf' = fPrf {forkPremiseIndexCompBef = getForkIndexComp}
        fork_ fPrf' lPrf l cont
      SrHalt res -> case forkPremiseRet' fPrf of
        MayOnlyReturnVoid -> case res of {}
        MayOnlyReturnType -> case forkPremiseIndexCompAft fPrf of
          ForkIndexCompSnd -> xreturn res

-- |Reorders the open the free channels.
--
-- The @`permChans` f g@ should only be called with @f . g = id@. This is not
-- verified by compiler, should be checked manually.
--
-- For a safe alternative, see `swap_`. That one is guaranteed to only permute
-- channels and never cause bad behaviors.
permChans :: (KnownIndex bef, Monad m)
         => (forall x y. Chan x y l -> Chan x y l')
         -> (forall x y. Chan x y l' -> Chan x y l)
         -> AsyncT l m bef aft a
         -> AsyncT l' m bef aft a
permChans f g cont = getWT >>=: \case
  SNextRecv -> M.do
    xlift (runTillRecv cont) >>=: \case
      RrHalt res -> xreturn res
      RrRecv cont' -> M.do
        SomeSndMessage i m <- recvAny
        permChans f g $ cont' $ SomeSndMessage (g i) m
  SNextSend -> M.do
    xlift (runTillSend cont) >>=: \case
      SrHalt res -> xreturn res
      SrSend (SomeFstMessage i m) cont' -> M.do
        send (f i) m
        permChans f g cont'

-- |Swap the two adjacent free channels.
--
-- `p` is the prefix of free channels list that is skipped and left untouched
-- before swapping the two channels that follow.
--
-- The first two arguments can often be derived automatically using
-- `getListSplit`, when @p@ and @s@ are fully known.
swap_ :: ( KnownIndex bef
        , Monad m
        )
     => ListSplitD l p (f:s:rest)
     -- ^Proof of @l == p ++ (f:s:rest)@
     -> AsyncT l m bef aft a
     -> AsyncT (Concat p (s:f:rest)) m bef aft a
swap_ prf cont = case listSplitConcat prf of
    Refl -> permChans (f prf $ listSplitSwap prf) (f (listSplitSwap prf) prf) cont
  where
    f :: ListSplitD l p (f:s:rest)
      -> ListSplitD l' p (s:f:rest)
      -> Chan x y l
      -> Chan x y l'
    f SplitHere SplitHere = \case
      Here -> There Here
      There Here -> Here
      There2 i -> There2 i
    f (SplitThere p) (SplitThere p') = \case
      Here -> Here
      There i -> There $ f p p' i

-- |Proof that an action that's only allowed to return in `NextSend` state will
-- not do so in `NextRecv` state.
doesNotReturnInRecvPrf :: MayOnlyReturnAfterRecvD aft a
                       -> RecvRes ach m aft a
                       -- ^Result of running `runTillRecv`
                       -> (SomeSndMessage ach -> AsyncT ach m NextSend aft a)
                       -- ^The continutation that tells how the process chose to receive the message
doesNotReturnInRecvPrf retPrf = \case
  RrHalt contra -> case retPrf of
    MayOnlyReturnVoid -> case contra of {}
  RrRecv cont -> cont

-- |Connect two adjacent free channels with each other. This binds them and
-- removes from the free list.
connect_ :: (Monad m, KnownIndex bef)
        => MayOnlyReturnAfterRecvD aft a
        -> ListSplitD l p ('(x, y) : '(y, x) : rest)
        -- ^Proof of @l == p ++ ('(x, y) : '(y, x) : rest)@
        -> AsyncT l m bef aft a
        -- ^Exectuion where we want to connect_ the channels
        -> AsyncT (Concat p rest) m bef aft a
connect_ retPrf prf cont = case listSplitConcat prf of
  Refl -> let prf' = listSplitPopSuffix $ listSplitPopSuffix prf in
    getWT >>=: \case
      SNextRecv -> M.do
        xlift (runTillRecv cont) >>=: \case
          RrRecv cont' -> M.do
            SomeSndMessage i m <- recvAny
            connect_ retPrf prf $ cont' $ SomeSndMessage (g prf prf' i) m
          RrHalt res -> xreturn res
      SNextSend -> M.do
        xlift (runTillSend cont) >>=: \case
          SrHalt res -> xreturn res
          SrSend (SomeFstMessage i m) cont' -> case f prf prf' i of
              SomeValue Here (Refl, Refl) -> M.do
                cont'' <- doesNotReturnInRecvPrf retPrf <$> xlift (runTillRecv cont')
                connect_ retPrf prf $ cont'' $ SomeSndMessage (snd $ splitToInlistPair prf) m
              SomeValue (There Here) (Refl, Refl) -> M.do
                cont'' <- doesNotReturnInRecvPrf retPrf <$> xlift (runTillRecv cont')
                connect_ retPrf prf $ cont'' $ SomeSndMessage (fst $ splitToInlistPair prf) m
              SomeValue (There2 Here) i' -> M.do
                send i' m
                connect_ retPrf prf cont'
              SomeValue (There3 contra) _ -> case contra of {}

  where
    f :: ListSplitD l p ( '(x', y') : '(y', x') : rest)
      -> ListSplitD l' p rest
      -> Chan x y l
      -> SomeValue '[ (x :~: x', y :~: y')
                    , (x :~: y', y :~: x')
                    , Chan x y l'
                    ]
    f SplitHere SplitHere = \case
      Here -> SomeValue Here (Refl, Refl)
      There Here -> SomeValue (There Here) (Refl, Refl)
      There2 i -> SomeValue (There2 Here) i
    f (SplitThere p) (SplitThere p') = \case
      Here -> SomeValue (There2 Here) Here
      There i -> case f p p' i of
        SomeValue Here v -> SomeValue Here v
        SomeValue (There Here) v -> SomeValue (There Here) v
        SomeValue (There2 Here) v -> SomeValue (There2 Here) $ There v
        SomeValue (There3 contra) _ -> case contra of {}

    g :: ListSplitD l p ( '(x', y') : '(y', x') : rest)
      -> ListSplitD l' p rest
      -> Chan x y l'
      -> Chan x y l
    g SplitHere SplitHere = \i -> There2 i
    g (SplitThere p) (SplitThere p') = \case
      Here -> Here
      There i -> There $ g p p' i

    splitToInlistPair :: ListSplitD l p ( '(x, y) : '(x', y') : rest)
                      -> (Chan x y l, Chan x' y' l)
    splitToInlistPair SplitHere = (Here, There Here)
    splitToInlistPair (SplitThere i) = There *** There $ splitToInlistPair i
