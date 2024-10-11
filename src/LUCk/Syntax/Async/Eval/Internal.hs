{-# LANGUAGE AllowAmbiguousTypes #-}

module LUCk.Syntax.Async.Eval.Internal
  (
  -- * Execution Implementation
  -- $core
    fork_
  , swap_
  , connect_
  -- ** Unsafe
  , permPorts
  -- *Helper functions and types
  -- $helpers
  , ForkPremiseD(..)
  , getForkPremiseD
  , ForkIndexComp(..)
  , getForkIndexSwap
  , getForkIndexRecv
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

getForkIndexRecv :: SIndex i -> ForkIndexCompD NextRecv i
getForkIndexRecv = \case
  SNextRecv -> getForkIndexComp
  SNextSend -> getForkIndexComp

getForkIndexSwap :: ForkIndexCompD i i'
                 -> ForkIndexCompD i' i
getForkIndexSwap = \case
  ForkIndexCompNone -> ForkIndexCompNone
  ForkIndexCompFst -> ForkIndexCompSnd
  ForkIndexCompSnd -> ForkIndexCompFst

type ForkIndexOr :: Index -> Index -> Index
type family ForkIndexOr bef bef' where
  ForkIndexOr NextSend NextRecv = NextSend
  ForkIndexOr NextRecv i = i

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
portFromConcat :: forall (ach :: [Port]) ach' x y.
                  KnownLenD ach
               -> PortInList x y (Concat ach ach')
               -> Either (PortInList x y ach) (PortInList x y ach')
portFromConcat = \case
  KnownLenZ -> Right
  KnownLenS rest -> \case
    Here -> Left Here
    There ch -> mapLeft There $ portFromConcat rest ch

-- |Given an element's index in @ach@, return the same element's index in @`Concat` ach ach'@.
fstToConcat :: forall ach ach' x y.
               KnownLenD ach
            -> PortInList x y ach
            -> PortInList x y (Concat ach ach')
fstToConcat _ Here = Here
fstToConcat (KnownLenS n) (There rest) = There $ fstToConcat @_ @(ach') n rest

-- |Given an element's index in @ach'@, return the same element's index in @`Concat` ach ach'@.
sndToConcat :: forall ach ach' x y.
               KnownLenD ach
            -> PortInList x y ach'
            -> PortInList x y (Concat ach ach')
sndToConcat KnownLenZ = id
sndToConcat (KnownLenS n) = There . sndToConcat n

-- $core
--
-- These are utility functions that are used by `runExec` to evaluate an exection.
--
-- The `fork_`, `swap_` and `connect_` correspond one-to-one to the constructors
-- of `Exec`. And `escapeSyncT` evaluates a concurrent algorithm that has all
-- of its ports bound as a local algorithm.

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

-- |Run two processes in parallel exposing the free ports of both of them.
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
     -- ^Depdendent length of free ports list in left branch
     -> AsyncT ach m bef aft a
     -- ^Left branch of the fork_
     -> AsyncT ach' m bef' aft' a'
     -- ^Right branch of the fork_
     -> AsyncT (Concat ach ach') m (ForkIndexOr bef bef') (ForkIndexOr aft aft') (ChooseRet aft aft' a a')
fork_ fPrf lPrf l r = case forkPremiseIndexCompBef fPrf of
  ForkIndexCompNone -> M.do
    SomeRxMess i m <- recvAny
    case portFromConcat @ach @ach' lPrf i of
      Left i' -> xlift (runTillRecv l) >>=: \case
        RrRecv l' -> M.do
          let fPrf' = fPrf {forkPremiseIndexCompBef = getForkIndexComp}
          fork_ fPrf' lPrf (l' $ SomeRxMess i' m) r
        RrHalt res -> case forkPremiseRet fPrf of
          MayOnlyReturnVoid -> case res of {}
      Right i' -> xlift (runTillRecv r) >>=: \case
        RrRecv r' -> M.do
          let fPrf' = fPrf {forkPremiseIndexCompBef = getForkIndexComp}
          fork_ fPrf' lPrf l (r' $ SomeRxMess i' m)
        RrHalt res -> case forkPremiseRet' fPrf of
          MayOnlyReturnVoid -> case res of {}
  ForkIndexCompFst ->
    xlift (runTillSend l) >>=: \case
      SrSend (SomeTxMess i m) cont -> M.do
        send (fstToConcat @ach @ach' lPrf i) m
        let fPrf' = fPrf {forkPremiseIndexCompBef = getForkIndexComp}
        fork_ fPrf' lPrf cont r
      SrHalt res -> case forkPremiseRet fPrf of
        MayOnlyReturnVoid -> case res of {}
        MayOnlyReturnType -> case forkPremiseIndexCompAft fPrf of
          ForkIndexCompFst -> xreturn res
  ForkIndexCompSnd ->
    xlift (runTillSend r) >>=: \case
      SrSend (SomeTxMess i m) cont -> M.do
        send (sndToConcat @ach @ach' lPrf i) m
        let fPrf' = fPrf {forkPremiseIndexCompBef = getForkIndexComp}
        fork_ fPrf' lPrf l cont
      SrHalt res -> case forkPremiseRet' fPrf of
        MayOnlyReturnVoid -> case res of {}
        MayOnlyReturnType -> case forkPremiseIndexCompAft fPrf of
          ForkIndexCompSnd -> xreturn res

-- |Reorders the open the free ports.
--
-- The @`permPorts` f g@ should only be called with @f . g = id@. This is not
-- verified by compiler, should be checked manually.
--
-- For a safe alternative, see `swap_`. That one is guaranteed to only permute
-- ports and never cause bad behaviors.
permPorts :: (KnownIndex bef, Monad m)
         => (forall x y. PortInList x y l -> PortInList x y l')
         -> (forall x y. PortInList x y l' -> PortInList x y l)
         -> AsyncT l m bef aft a
         -> AsyncT l' m bef aft a
permPorts f g cont = asyncGetIndex >>=: \case
  SNextRecv -> M.do
    xlift (runTillRecv cont) >>=: \case
      RrHalt res -> xreturn res
      RrRecv cont' -> M.do
        SomeRxMess i m <- recvAny
        permPorts f g $ cont' $ SomeRxMess (g i) m
  SNextSend -> M.do
    xlift (runTillSend cont) >>=: \case
      SrHalt res -> xreturn res
      SrSend (SomeTxMess i m) cont' -> M.do
        send (f i) m
        permPorts f g cont'

-- |Swap two free ports.
--
-- We go from an action where free ports are 
--   @p ++ [f] ++ p' ++ [s] ++ rest@
--   to
--   @p ++ [s] ++ p' ++ [f] ++ rest@.
-- In other words, the elemens `f` and `s` are swapped.
--
-- The `ListSplitD` arguments can often be derived automatically if `p` `p'`
-- and `rest` are fully known.
swap_ :: ( KnownIndex bef
         , Monad m
         )
     => ListSplitD l p (f:l')
     -- ^Proof of @l == p ++ (f:l')@
     -> ListSplitD l' p' (s:rest)
     -- ^Proof of @l' == p' ++ (s:rest)@
     -> AsyncT l m bef aft a
     -> AsyncT (Concat p (s : Concat p' (f:rest))) m bef aft a
swap_ prfF prfS cont = case (listSplitConcat prfF, listSplitConcat prfS) of
    (Refl, Refl) -> permPorts (f prfF prfS)
                              (uncurry f $ listSplitSwap prfF prfS)
                              cont
  where
    f :: ListSplitD l p (f:l')
      -> ListSplitD l' p' (s:rest)
      -> PortInList x y l
      -> PortInList x y (Concat p (s : Concat p' (f:rest)))
    f p p' i = let
        (pInv, pInv') = listSplitSwap p p'
      in case (listSplitConcat p, listSplitConcat p') of
        (Refl, Refl) -> case findIndex p i of
          Left i' -> padRightIndexSameSuff pInv i'
          Right Here -> padLeftIndexSameSuff pInv $ There $ padLeftIndexSameSuff pInv' Here
          Right (There i') -> case findIndex p' i' of
            Left i'' -> padLeftIndexSameSuff pInv $ There $ padRightIndexSameSuff pInv' i''
            Right Here -> padLeftIndexSameSuff pInv Here
            Right (There i'') -> padLeftIndexSameSuff pInv $ There $ padLeftIndexSameSuff pInv' $ There i''

padRightIndex :: forall s' s p l x.
                 ListSplitD l p s
              -> InList p x
              -> InList (Concat p s') x
padRightIndex SplitHere = \contra -> case contra of {}
padRightIndex (SplitThere i) = \case
  Here -> Here
  There j -> There $ padRightIndex @s' i j

padRightIndexSameSuff :: forall s p l x. ListSplitD l p s
                      -> InList p x
                      -> InList (Concat p s) x
padRightIndexSameSuff = padRightIndex @s

padLeftIndex :: forall s' s l p x.
                ListSplitD l p s
             -> InList s' x
             -> InList (Concat p s') x
padLeftIndex SplitHere = id
padLeftIndex (SplitThere i) = There . padLeftIndex i

padLeftIndexSameSuff :: forall s l p x.
                        ListSplitD l p s
                     -> InList s x
                     -> InList (Concat p s) x
padLeftIndexSameSuff = padLeftIndex @s

findIndex :: ListSplitD l p s
          -> InList l z
          -> Either (InList p z) (InList s z)
findIndex SplitHere Here = Right Here
findIndex SplitHere (There i) = Right $ There i
findIndex (SplitThere _) Here = Left Here
findIndex (SplitThere j) (There i) = case findIndex j i of
  Left k -> Left $ There k
  Right k -> Right k


-- |Proof that an action that's only allowed to return in `NextSend` state will
-- not do so in `NextRecv` state.
doesNotReturnInRecvPrf :: MayOnlyReturnAfterRecvD aft a
                       -> RecvRes ach m aft a
                       -- ^Result of running `runTillRecv`
                       -> (SomeRxMess ach -> AsyncT ach m NextSend aft a)
                       -- ^The continutation that tells how the process chose to receive the message
doesNotReturnInRecvPrf retPrf = \case
  RrHalt contra -> case retPrf of
    MayOnlyReturnVoid -> case contra of {}
  RrRecv cont -> cont

-- |Connect two adjacent free ports with each other. This binds them and
-- removes from the free list.
connect_ :: (Monad m, KnownIndex bef)
        => MayOnlyReturnAfterRecvD aft a
        -> ListSplitD l p (P x y : l')
        -- ^ Proof of @l == p ++ [(x, y)] ++ l'@
        -> ListSplitD l' p' (P y x : rest)
        -- ^ Proof of @l' == p' ++ [(y, x)] ++ rest@
        -> AsyncT l m bef aft a
        -- ^Exectuion where we want to connect_ the ports
        -> AsyncT (Concat p (Concat p' rest)) m bef aft a
connect_ retPrf prf prf' cont = case (listSplitConcat prf, listSplitConcat prf') of
  (Refl, Refl) -> let
    in
    asyncGetIndex >>=: \case
      SNextRecv -> M.do
        xlift (runTillRecv cont) >>=: \case
          RrRecv cont' -> M.do
            SomeRxMess i m <- recvAny
            connect_ retPrf prf prf' $ cont' $ SomeRxMess (g prf prf' i) m
          RrHalt res -> xreturn res
      SNextSend -> M.do
        xlift (runTillSend cont) >>=: \case
          SrHalt res -> xreturn res
          SrSend (SomeTxMess i m) cont' -> case f prf prf' i of
              SomeValue Here (Refl, Refl) -> M.do
                cont'' <- doesNotReturnInRecvPrf retPrf <$> xlift (runTillRecv cont')
                let i' = padLeftIndexSameSuff prf $ There $ padLeftIndexSameSuff prf' Here
                connect_ retPrf prf prf' $ cont'' $ SomeRxMess i' m
              SomeValue (There Here) (Refl, Refl) -> M.do
                cont'' <- doesNotReturnInRecvPrf retPrf <$> xlift (runTillRecv cont')
                let i' = padLeftIndexSameSuff prf Here
                connect_ retPrf prf prf' $ cont'' $ SomeRxMess i' m
              SomeValue (There2 Here) i' -> M.do
                send i' m
                connect_ retPrf prf prf' cont'
              SomeValue (There3 contra) _ -> case contra of {}

  where
    f :: ListSplitD l p (P x' y' : l')
      -> ListSplitD l' p' (P y' x' : rest)
      -> PortInList x y l
      -> SomeValue '[ (x :~: x', y :~: y')
                    , (x :~: y', y :~: x')
                    , PortInList x y (Concat p (Concat p' rest))
                    ]
    f p p' c = case (listSplitConcat p, listSplitConcat p') of
        (Refl, Refl) -> let
          (pInv, pInv') = listSplitSuff2 p p'
           in case findIndex p c of
          Left i -> SomeValue (There2 Here) $ padRightIndexSameSuff pInv i
          Right Here -> SomeValue Here (Refl, Refl)
          Right (There i) -> case findIndex p' i of
            Left i' -> SomeValue (There2 Here) $ padLeftIndex p $ padRightIndexSameSuff pInv' i'
            Right Here -> SomeValue (There Here) (Refl, Refl)
            Right (There i') -> SomeValue (There2 Here) $ padLeftIndex p $ padLeftIndex p' i'

    g :: ListSplitD l p (P x' y' : l')
      -> ListSplitD l' p' (P y' x' : rest)
      -> PortInList x y (Concat p (Concat p' rest))
      -> PortInList x y l
    g p p' c = case (listSplitConcat p, listSplitConcat p') of
        (Refl, Refl) -> let
          (pInv, pInv') = listSplitSuff2 p p'
         in case findIndex pInv c of
            Left i -> padRightIndexSameSuff p i
            Right i -> case findIndex pInv' i of
              Left i' -> padLeftIndexSameSuff p $ There $ padRightIndexSameSuff p' i'
              Right i' -> padLeftIndexSameSuff p $ There $ padLeftIndexSameSuff p' $ There i'
