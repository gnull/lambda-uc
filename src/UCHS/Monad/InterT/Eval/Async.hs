{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}

module UCHS.Monad.InterT.Eval.Async
  (
  -- * Execution Syntax
  -- $exec
    Exec(..)
  , runExec
  -- * Execution Implementation
  -- $core
  , fork
  , swap
  , connect
  , escapeSyncT
  -- ** Unsafe
  , permChans
  -- *Helper functions and types
  -- $helpers
  , Forkable
  , ForkIndexComp(..)
  , ForkIndexCompD(..)
  , ForkIndexOr
  , MayOnlyReturnAfterRecv(..)
  , MayOnlyReturnAfterRecvD(..)
  , ChooseRet
  -- * Derived Gadgets
  , connectSelf
  , idProc
  , mergeProc
  )
where

import Data.Either.Extra (mapLeft)

import Control.Arrow
import Control.XApplicative
import Control.XMonad
import Control.XMonad.XWriter
import qualified Control.XMonad.Do as M

import UCHS.Monad
import UCHS.Types

data ForkIndexCompD (befFst :: Index) (befSnd :: Index) where
  ForkIndexCompNone :: ForkIndexCompD NextRecv NextRecv
  ForkIndexCompFst :: ForkIndexCompD NextSend NextRecv
  ForkIndexCompSnd :: ForkIndexCompD NextRecv NextSend

type ForkIndexComp :: Index -> Index -> Constraint
class ForkIndexComp befFst befSnd where
  getIndexStartCompPrf :: ForkIndexCompD befFst befSnd

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
-- The `fork`, `swap` and `connect` correspond one-to-one to the constructors
-- of `Exec`. And `escapeSyncT` evaluates a concurrent algorithm that has all
-- of its channels bound as a local algorithm.

type Forkable bef bef' aft aft' a a' =
  ( ForkIndexComp bef bef'
  , ForkIndexComp aft aft'
  , MayOnlyReturnAfterRecv aft a
  , MayOnlyReturnAfterRecv aft' a'
  )

-- |Run two processes in parallel exposing the free channels of both of them.
--
-- The typeclass constaint `Forkable` here ensures that:
--
-- 1. No more than one of forked processes expects to start in `NextSend`.
-- 2. No more than one of forked processes expects to finish in `NextSend`.
-- 3. Only the process that finishes in `NextSend` is allowed to produce a (non-`Void`) result.
--
-- The resulting action that implements the fork starts in `NextSend` if one
-- of the forked actions started in `NextSend`. Similarly, it finishes in
-- `NextSend` if one of the forked two finishes in `NextSend`. (Implemented
-- with `ForkIndexOr`.)
--
-- The return value of the fork is the same as return value of process that
-- finishes in `NextSend`. If both finish in `NextRecv`, then fork's return
-- value is `Void`.
fork :: forall m ach ach' bef bef' aft aft' a a'.
        (Monad m, Forkable bef bef' aft aft' a a')
     => KnownLenD ach
     -- ^Depdendent length of free channels list in left branch
     -> AsyncT m ach bef aft a
     -- ^Left branch of the fork
     -> AsyncT m ach' bef' aft' a'
     -- ^Right branch of the fork
     -> AsyncT m (Concat ach ach') (ForkIndexOr bef bef') (ForkIndexOr aft aft') (ChooseRet aft aft' a a')
fork prf l r = case getIndexStartCompPrf @bef @bef' of
  ForkIndexCompNone -> M.do
    SomeSndMessage i m <- recvAny
    case chanFromConcat @ach @ach' prf i of
      Left i' -> lift (runTillRecv l) >>=: \case
        RrRecv l' -> fork prf (l' $ SomeSndMessage i' m) r
        RrCall contra _ _ -> case contra of {}
        RrHalt res -> case getMayOnlyReturnAfterRecvPrf @aft @a of
          MayOnlyReturnVoid -> case res of {}
      Right i' -> lift (runTillRecv r) >>=: \case
        RrRecv r' -> fork prf l (r' $ SomeSndMessage i' m)
        RrCall contra _ _ -> case contra of {}
        RrHalt res -> case getMayOnlyReturnAfterRecvPrf @aft' @a' of
          MayOnlyReturnVoid -> case res of {}
  ForkIndexCompFst ->
    lift (runTillSend l) >>=: \case
      SrSend (SomeFstMessage i m) cont -> M.do
        send (fstToConcat @ach @ach' prf i) m
        fork prf cont r
      SrCall contra _ _ -> case contra of {}
      SrHalt res -> case getMayOnlyReturnAfterRecvPrf @aft @a of
        MayOnlyReturnVoid -> case res of {}
        MayOnlyReturnType -> case getIndexStartCompPrf @aft @aft' of
          ForkIndexCompFst -> xreturn res
  ForkIndexCompSnd ->
    lift (runTillSend r) >>=: \case
      SrSend (SomeFstMessage i m) cont -> M.do
        send (sndToConcat @ach @ach' prf i) m
        fork prf l cont
      SrCall contra _ _ -> case contra of {}
      SrHalt res -> case getMayOnlyReturnAfterRecvPrf @aft' @a' of
        MayOnlyReturnVoid -> case res of {}
        MayOnlyReturnType -> case getIndexStartCompPrf @aft @aft' of
          ForkIndexCompSnd -> xreturn res

-- |Reorders the open the free channels.
--
-- The @`permChans` f g@ should only be called with @f . g = id@. This is not
-- verified by compiler, should be checked manually.
--
-- For a safe alternative, see `swap`. That one is guaranteed to only permute
-- channels and never cause bad behaviors.
permChans :: (KnownIndex bef, Monad m)
         => (forall x y. Chan x y l -> Chan x y l')
         -> (forall x y. Chan x y l' -> Chan x y l)
         -> AsyncT m l bef aft a
         -> AsyncT m l' bef aft a
permChans f g cont = getWT >>=: \case
  SNextRecv -> M.do
    lift (runTillRecv cont) >>=: \case
      RrCall contra _ _ -> case contra of {}
      RrHalt res -> xreturn res
      RrRecv cont' -> M.do
        SomeSndMessage i m <- recvAny
        permChans f g $ cont' $ SomeSndMessage (g i) m
  SNextSend -> M.do
    lift (runTillSend cont) >>=: \case
      SrCall contra _ _ -> case contra of {}
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
swap :: ( KnownIndex bef
        , Monad m
        )
     => ListSplitD l p (f:s:rest)
     -- ^Proof of @l == p ++ (f:s:rest)@
     -> ListSplitD l' p (s:f:rest)
     -- ^Proof of @l' == p ++ (s:f:rest)@
     -> AsyncT m l bef aft a
     -> AsyncT m l' bef aft a
swap prf prf' cont = permChans (f prf prf') (f prf' prf) cont
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
doesNotReturnInRecvPrf :: forall aft a m ach. MayOnlyReturnAfterRecv aft a
                       => RecvRes m ach '[] aft a
                       -- ^Result of running `runTillRecv`
                       -> (SomeSndMessage ach -> InterT ('InterPars m '[] ach '[]) NextSend aft a)
                       -- ^The continutation that tells how the process chose to receive the message
doesNotReturnInRecvPrf = \case
  RrCall contra _ _ -> case contra of {}
  RrHalt contra -> case getMayOnlyReturnAfterRecvPrf @aft @a of
    MayOnlyReturnVoid -> case contra of {}
  RrRecv cont -> cont

-- |Connect two adjacent free channels with each other. This binds them and
-- removes from the free list.
connect :: (Monad m, KnownIndex bef, MayOnlyReturnAfterRecv aft a)
        => ListSplitD l p ('(x, y) : '(y, x) : rest)
        -- ^Proof of @l == p ++ ('(x, y) : '(y, x) : rest)@
        -> ListSplitD l' p rest
        -- ^Proof of @l' == p ++ rest@
        -> AsyncT m l bef aft a
        -- ^Exectuion where we want to connect the channels
        -> AsyncT m l' bef aft a
connect prf prf' cont = getWT >>=: \case
    SNextRecv -> M.do
      lift (runTillRecv cont) >>=: \case
        RrCall contra _ _ -> case contra of {}
        RrRecv cont' -> M.do
          SomeSndMessage i m <- recvAny
          connect prf prf' $ cont' $ SomeSndMessage (g prf prf' i) m
        RrHalt res -> xreturn res
    SNextSend -> M.do
      lift (runTillSend cont) >>=: \case
        SrCall contra _ _ -> case contra of {}
        SrHalt res -> xreturn res
        SrSend (SomeFstMessage i m) cont' -> case f prf prf' i of
            SomeValue Here (Refl, Refl) -> M.do
              cont'' <- doesNotReturnInRecvPrf <$> lift (runTillRecv cont')
              connect prf prf' $ cont'' $ SomeSndMessage (snd $ splitToInlistPair prf) m
            SomeValue (There Here) (Refl, Refl) -> M.do
              cont'' <- doesNotReturnInRecvPrf <$> lift (runTillRecv cont')
              connect prf prf' $ cont'' $ SomeSndMessage (fst $ splitToInlistPair prf) m
            SomeValue (There2 Here) i' -> M.do
              send i' m
              connect prf prf' cont'
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


-- |Interactive action with no free channels can be interpreted as local.
--
-- Apply this function once you've bound all the free channels to run the execution.
escapeSyncT :: Monad m
            => AsyncT m '[] NextSend NextSend a
            -> m a
escapeSyncT cont = runTillSend cont >>= \case
  SrCall contra _ _ -> case contra of {}
  SrSend (SomeFstMessage contra _) _ -> case contra of {}
  SrHalt res -> pure res


-- |Connect the first channel to itself.
--
-- This is not a basic combinator and is derived using `fork` and `connect`.
connectSelf :: forall bef m x rest a . (Monad m, KnownIndex bef)
            => AsyncT m ('(x, x) : rest) bef NextSend a
            -- ^An execution where the first free channel is its own dual
            -> AsyncT m rest bef NextSend a
connectSelf p = getWT >>=: \case
    SNextRecv -> connect SplitHere SplitHere $ fork getKnownLenPrf idProc p
    SNextSend -> connect SplitHere SplitHere $ fork getKnownLenPrf idProc p

-- |Process that sends back everything it gets
idProc :: Monad m
       => AsyncT m '[ '(x, x)] NextRecv NextRecv Void
idProc = M.do
  recvOne >>=: sendOne
  idProc

-- |Merge two single-directional channels into one.
--
-- Any message that arrives on the merged channels is passed as is with no
-- marking to tell what channel it came from.
mergeProc :: AsyncT m '[ '(a, Void), '(Void, a), '(Void, a)] NextRecv NextRecv Void
mergeProc = M.do
  () <- recvAny >>=: \case
    SomeSndMessage Here contra -> case contra of {}
    SomeSndMessage (There Here) x -> send Here x
    SomeSndMessage (There2 Here) x -> send Here x
    SomeSndMessage (There3 contra) _ -> case contra of {}
  mergeProc

-- $exec
--
-- This section defines syntax for distributed exection of processes.
--
-- You define your processes and their connections as a value of type `Exec`,
-- and then run it using `runExec`.
--
-- You start with the processes defined as @`AsyncT` m ach i i a`@ wrapped
-- in `ExecProc`, then you combine them using `ExecFork`, `ExecConn` and
-- `ExecSwap` until you've connected all the free channels and left with
-- @`Exec` m '[] `NextSend` a@. The latter can be evaluated with `runExec` to
-- yield the final result of evaluation.
--
-- Only one process in the whole execution is allowed to return a result. It
-- is the (only) process that finishes in `NextSend` state, all the other
-- processes are forced to have their return type `Void` (and never
-- finish). These conditions are checked statically by the typeclass
-- restrictions of `Exec` constructors.
--
-- Function `runExec` returns the result of the process that termiates in
-- `NextSend`.

data Exec m ach i a where
  -- |An execution consisting of one process.
  ExecProc :: (MayOnlyReturnAfterRecv i a)
           => AsyncT m ach i i a
           -- ^The code that the process will run
           -> Exec m ach i a
  -- |Combine two executions.
  ExecFork :: (Forkable i i' i i' a a')
           => KnownLenD ach
           -> Exec m ach i a
           -- ^First forked process
           -> Exec m ach' i' a'
           -- ^Second forked process
           -> Exec m (Concat ach ach') (ForkIndexOr i i') (ChooseRet i i' a a')
  -- |Swap positions of two adjacent free channels.
  ExecSwap :: ( KnownIndex i
              , Monad m
              )
           => ListSplitD l p (f:s:rest)
           -- ^Proof of @l == p ++ (f:s:rest)@
           -> ListSplitD l' p (s:f:rest)
           -- ^Proof of @l' == p ++ (s:f:rest)@
           -> Exec m l i a
           -> Exec m l' i a
  -- |Connect two adjacent free channels of a given execution (making them bound).
  ExecConn :: (KnownIndex i, MayOnlyReturnAfterRecv i a)
           => ListSplitD l p ('(x, y) : '(y, x) : rest)
           -- ^Proof of @l == p ++ ('(x, y) : '(y, x) : rest)@
           -> ListSplitD l' p rest
           -- ^Proof of @l' == p ++ rest@
           -> Exec m l i a
           -- ^Exectuion where we want to connect the channels
           -> Exec m l' i a

data ExecIndex
  = ExecIndexInit
  -- ^We haven't started any executions
  | ExecIndexSome [(Type, Type)] Index Type
  -- ^An execution with given @ach@, @i@, and @res@ is started

type MatchExecIndex :: (Type -> Type) -> ExecIndex -> Type
type family MatchExecIndex m i where
  MatchExecIndex _ ExecIndexInit = ()
  MatchExecIndex m (ExecIndexSome l i res) = Exec m l i res

type ExecWriter :: (Type -> Type) -> ExecIndex -> ExecIndex -> Type -> Type
newtype ExecWriter m i j a = ExecWriter
  { runExecWriter :: XWriter (MatchExecIndex m i) (MatchExecIndex m j) a
  }
  deriving (Functor) via (XWriter (MatchExecIndex m i) (MatchExecIndex m j))

instance XApplicative (ExecWriter m) where
  xpure = ExecWriter . xpure
  f <*>: x = ExecWriter $ runExecWriter f <*>: runExecWriter x

instance XMonad (ExecWriter m) where
  m >>=: f = ExecWriter $ runExecWriter m >>=: (runExecWriter . f)

execWriterToExec :: ExecWriter m ExecIndexInit (ExecIndexSome l i res) ()
                 -> MatchExecIndex m (ExecIndexSome l i res)
execWriterToExec p = f ()
  where
    (f, ()) = runXWriter $ runExecWriter p

forkLeft :: Forkable i i' i i' res res'
         => KnownLenD l
         -> ExecWriter m ExecIndexInit (ExecIndexSome l' i' res') ()
         -> ExecWriter m (ExecIndexSome l i res)
                         (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                         ()
forkLeft prf p = ExecWriter $ tell $
  \e -> ExecFork prf e $ execWriterToExec p

forkRight :: Forkable i i' i i' res res'
          => KnownLenD l
          -> ExecWriter m ExecIndexInit (ExecIndexSome l i res) ()
          -> ExecWriter m (ExecIndexSome l' i' res')
                          (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                          ()
forkRight prf p = ExecWriter $ tell $
  \e -> ExecFork prf (execWriterToExec p) e

connectM :: (KnownIndex i, MayOnlyReturnAfterRecv i res)
         => ListSplitD l p ('(x, y) : '(y, x) : rest)
         -- ^Proof of @l == p ++ ('(x, y) : '(y, x) : rest)@
         -> ListSplitD l' p rest
         -- ^Proof of @l' == p ++ rest@
         -> ExecWriter m (ExecIndexSome l i res) (ExecIndexSome l' i res) ()
connectM prf prf' = ExecWriter $ tell $ ExecConn prf prf'

swapM :: ( KnownIndex i
         , Monad m
         )
      => ListSplitD l p (f:s:rest)
      -- ^Proof of @l == p ++ (f:s:rest)@
      -> ListSplitD l' p (s:f:rest)
      -- ^Proof of @l' == p ++ (s:f:rest)@
      -> ExecWriter m (ExecIndexSome l i res) (ExecIndexSome l' i res) ()
swapM prf prf' = ExecWriter $ tell $ ExecSwap prf prf'

-- hey :: ExecWriter m ExecIndexInit (ExecIndexSome l i res) ()
-- hey = _

-- |Run an execution.
--
-- Note that the list of free channels must be empty, i.e. all channels must be
-- bound for an execution to be defined.
runExec :: Monad m
        => Exec m '[] NextSend a
        -> m a
runExec = escapeSyncT . f
  where
    f :: Monad m
      => Exec m ach i a
      -> AsyncT m ach i i a
    f = \case
      ExecProc p -> p
      ExecFork prf l r -> fork prf (f l) (f r)
      ExecSwap k k' p -> swap k k' $ f p
      ExecConn k k' p -> connect k k' $ f p
