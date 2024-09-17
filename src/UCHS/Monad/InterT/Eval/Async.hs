{-# LANGUAGE AllowAmbiguousTypes #-}

module UCHS.Monad.InterT.Eval.Async
  (
  -- * Core combinators
  -- $core
    fork
  , mapChans
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

import Control.Arrow
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
instance MayOnlyReturnAfterRecv NextRecv Void where
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

mapChans :: (KnownIndex bef, Monad m)
         => (forall x y. Chan x y l -> Chan x y l')
         -> (forall x y. Chan x y l' -> Chan x y l)
         -> AsyncT m l bef aft a
         -> AsyncT m l' bef aft a
mapChans f g cont = getWT >>=: \case
  SNextRecv -> M.do
    lift (runTillRecv cont) >>=: \case
      RrCall contra _ _ -> case contra of {}
      RrHalt res -> xreturn res
      RrRecv cont' -> M.do
        SomeSndMessage i m <- recvAny
        mapChans f g $ cont' $ SomeSndMessage (g i) m
  SNextSend -> M.do
    lift (runTillSend cont) >>=: \case
      SrCall contra _ _ -> case contra of {}
      SrHalt res -> xreturn res
      SrSend (SomeFstMessage i m) cont' -> M.do
        send (f i) m
        mapChans f g cont'

-- |Swap the two adjacent channels.
swap :: ( KnownIndex bef
        , Monad m
        )
     => ListSplit l p (f:s:rest)
     -> ListSplit l' p (s:f:rest)
     -> AsyncT m l bef aft a
     -> AsyncT m l' bef aft a
swap prf prf' cont = mapChans (f prf prf') (f prf' prf) cont
  where
    f :: ListSplit l p (f:s:rest)
      -> ListSplit l' p (s:f:rest)
      -> Chan x y l
      -> Chan x y l'
    f SplitHere SplitHere = \case
      Here -> There Here
      There Here -> Here
      There2 i -> There2 i
    f (SplitThere p) (SplitThere p') = \case
      Here -> Here
      There i -> There $ f p p' i

-- |Connect two adjacent channels with each other.
connect :: (KnownIndex bef, Monad m)
        => ListSplit l p ('(x, y) : '(y, x) : rest)
        -> ListSplit l' p rest
        -> AsyncT m l bef NextSend a
        -> AsyncT m l' bef NextSend a
connect prf prf' cont = getWT >>=: \case
    SNextRecv -> M.do
      lift (runTillRecv cont) >>=: \case
        RrCall contra _ _ -> case contra of {}
        RrRecv cont' -> M.do
          SomeSndMessage i m <- recvAny
          connect prf prf' $ cont' $ SomeSndMessage (g prf prf' i) m
    SNextSend -> M.do
      lift (runTillSend cont) >>=: \case
        SrCall contra _ _ -> case contra of {}
        SrHalt res -> xreturn res
        SrSend (SomeFstMessage i m) cont' -> case f prf prf' i of
            SomeValue Here (Refl, Refl) -> M.do
              cont'' <- mayOnlyRecvWTPrf <$> lift (runTillRecv cont')
              connect prf prf' $ cont'' $ SomeSndMessage (snd $ splitToInlistPair prf) m
            SomeValue (There Here) (Refl, Refl) -> M.do
              cont'' <- mayOnlyRecvWTPrf <$> lift (runTillRecv cont')
              connect prf prf' $ cont'' $ SomeSndMessage (fst $ splitToInlistPair prf) m
            SomeValue (There2 Here) i' -> M.do
              send i' m
              connect prf prf' cont'
            SomeValue (There3 contra) _ -> case contra of {}

  where
    f :: ListSplit l p ( '(x', y') : '(y', x') : rest)
      -> ListSplit l' p rest
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

    g :: ListSplit l p ( '(x', y') : '(y', x') : rest)
      -> ListSplit l' p rest
      -> Chan x y l'
      -> Chan x y l
    g SplitHere SplitHere = \i -> There2 i
    g (SplitThere p) (SplitThere p') = \case
      Here -> Here
      There i -> There $ g p p' i

    splitToInlistPair :: ListSplit l p ( '(x, y) : '(x', y') : rest)
                      -> (Chan x y l, Chan x' y' l)
    splitToInlistPair SplitHere = (Here, There Here)
    splitToInlistPair (SplitThere i) = There *** There $ splitToInlistPair i


-- |Connect the first channel to itself.
--
-- This one can be expressed with other combinators and is not necessary.
connectSelf :: forall bef m x rest a . (Monad m, KnownIndex bef)
            => AsyncT m ('(x, x) : rest) bef NextSend a
            -> AsyncT m rest bef NextSend a
connectSelf p = getWT >>=: \case
    SNextRecv -> connect SplitHere SplitHere $ fork getKnownLenPrf idProc p
    SNextSend -> connect SplitHere SplitHere $ fork getKnownLenPrf idProc p
  where
    idProc :: AsyncT m '[ '(x, x)] NextRecv NextRecv Void
    idProc = M.do
      oracleAccept >>=: oracleYield
      idProc
