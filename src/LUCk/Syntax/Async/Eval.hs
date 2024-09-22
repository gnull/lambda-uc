{-# LANGUAGE AllowAmbiguousTypes #-}

module LUCk.Syntax.Async.Eval
  (
  -- * Execution Syntax
  -- $exec
    Exec(..)
  , runExec
  , escapeSyncT
  -- * Writer Monad for Execution
  -- $writer
  , ExecWriter(..)
  , ExecIndex(..)
  , execWriterToExec
  -- ** Actions
  -- $actions
  , process
  , forkLeft
  , forkRight
  , connect
  , swap
  -- $explicit
  , process'
  , forkLeft'
  , forkRight'
  , connect'
  -- , swap
  , guard
  )
where

import Control.XApplicative
import Control.XMonad
import Control.XMonad.XWriter
import qualified Control.XMonad.Do as M

import LUCk.Syntax.Async.Eval.Internal
import LUCk.Syntax.Async
import LUCk.Syntax.Class
import LUCk.Types

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

data Exec ach m i a where
  -- |An execution consisting of one process.
  ExecProc :: MayOnlyReturnAfterRecvD i a
           -> AsyncT m ach i i a
           -- ^The code that the process will run
           -> Exec m ach i a
  -- |Combine two executions.
  ExecFork :: ForkPremiseD i i' i i' a a'
           -> KnownLenD ach
           -> Exec ach m i a
           -- ^First forked process
           -> Exec ach' m i' a'
           -- ^Second forked process
           -> Exec (Concat ach ach') m (ForkIndexOr i i') (ChooseRet i i' a a')
  -- |Swap positions of two adjacent free channels.
  ExecSwap :: ( KnownIndex i
              , Monad m
              )
           => ListSplitD l p (f:s:rest)
           -- ^Proof of @l == p ++ (f:s:rest)@
           -> Exec l m i a
           -> Exec (Concat p (s:f:rest)) m i a
  -- |Connect two adjacent free channels of a given execution (making them bound).
  ExecConn :: KnownIndex i
           => MayOnlyReturnAfterRecvD i a
           -> ListSplitD l p ('(x, y) : '(y, x) : rest)
           -- ^Proof of @l == p ++ ('(x, y) : '(y, x) : rest)@
           -> Exec l m i a
           -- ^Exectuion where we want to connect the channels
           -> Exec (Concat p rest) m i a

-- $writer
--
-- This section defines the `ExecWriter` monad that simplifies the construction
-- of `Exec` exections. Any `Exec` value is built like a tree where each node
-- is marked with one of constructors of `Exec`: `ExecFork` has two children
-- nodes, `ExecProc` is a leaf (no children nodes), while `ExecSwap` and
-- `ExecFork` have one child each.
--
-- This structure, while precisely matching the technical aspect of
-- constructing an execution, are not so convenient for human to
-- build. Especially, if your `Exec` formala is complex and you want to build
-- it gradually and see intermediate results.
--
-- The `ExecWriter` monad aids in building `Exec` values in a modular
-- way and providing the programmer with feedback at each step. Each
-- `ExecWriter` action internally stores a function @`Exec` l m i res ->
-- `Exec` l' m i' res'@ or a function @() -> `Exec` l m i res@ (given by the
-- `ExecIndex`). Two actions can be composed together if the corresponding
-- functions compose.
--
-- To get a runnable execution @`Exec` '[] m i res@, define a value of type
-- @`ExecWriter` m `ExecIndexInit` (`ExecIndexSome` l i res) ()@ and pass it
-- to `execWriterToExec`. The result can be passed to `runExec` to actually
-- run it.  The basic actions available in `ExecWriter` are `forkLeft`,
-- `forkRight`, `connect` and `swap`.

-- |Index of the `ExecWriter` monad.
data ExecIndex
  = ExecIndexInit
  -- ^We haven't started any executions
  | ExecIndexSome [(Type, Type)] Index Type
  -- ^An execution with given @ach@, @i@, and @res@ is started

-- |Mapping from the indices of `ExecWriter` to the indices of internal indexed
-- monoid @(->)@.
type MatchExecIndex :: (Type -> Type) -> ExecIndex -> Type
type family MatchExecIndex m i where
  MatchExecIndex _ ExecIndexInit = ()
  MatchExecIndex m (ExecIndexSome l i res) = Exec l m i res

-- Indexed writer that uses @`Exec` _ _ _ _ -> `Exec` _ _ _ _@ as internal indexed monoid.
type ExecWriter :: (Type -> Type) -> ExecIndex -> ExecIndex -> Type -> Type
newtype ExecWriter m i j a = ExecWriter
  { runExecWriter :: XWriter (MatchExecIndex m i) (MatchExecIndex m j) a
  }
  deriving (Functor)

instance XApplicative (ExecWriter m) where
  xpure = ExecWriter . xpure
  f <*>: x = ExecWriter $ runExecWriter f <*>: runExecWriter x

instance XMonad (ExecWriter m) where
  m >>=: f = ExecWriter $ runExecWriter m >>=: (runExecWriter . f)

-- |Extract the internal `Exec` from `ExecWriter`.
--
-- Note that `ExecWriter m i j ()` internally stores a function
-- @`MatchExecIndex` i -> `MatchExecIndex` j@. The function can be extracted
-- using `runXWriter`.
--
-- At the same time, @`MatchExecIndex` `ExecIndexInit` = ()`@. Therefore,
-- @`ExecWriter` m `ExecIndexInit` (`ExecIndexSome` l i res)@ stores a function
-- @() -> `Exec` m l i res@, which is isomorphic to just value @`Exec` m l i
-- res@, which this functions extracts.
execWriterToExec :: ExecWriter m ExecIndexInit (ExecIndexSome l i res) ()
                 -> MatchExecIndex m (ExecIndexSome l i res)
execWriterToExec p = f ()
  where
    (f, ()) = runXWriter $ runExecWriter p

-- $actions
--
-- The following are basic actions you can perform in `ExecWriter`. The
-- `process`, `forkLeft`, `forkRight`, `connect`, `swap` correpond to the
-- constructors of `Exec`. The difference between `forkLeft` and `forkRight` is
-- merely in the order of composing the child nodes.
--
-- The @`guard` = xreturn ()@ has no effect in the monad, but can be inserted
-- in-between other operations in `ExecWriter` to annotate the current
-- context. This can be used to document the code, while having the compiler
-- verify that the annotation is correct. In some rare cases, `guard` can also
-- be used to resolve ambiguous types.

-- $explicit
--
-- Following are the versions of `process`, `forkLeft`, `forkRight` and
-- `connect` that take the proofs as explicit arguments instead of implicit
-- typeclass constraints.

process' :: MayOnlyReturnAfterRecvD i res
         -> AsyncT l m i i res
         -> ExecWriter m ExecIndexInit (ExecIndexSome l i res) ()
process' retPrf = ExecWriter . tell . const . ExecProc retPrf

process :: MayOnlyReturnAfterRecv i res
        => AsyncT l m i i res
        -> ExecWriter m ExecIndexInit (ExecIndexSome l i res) ()
process = process' getMayOnlyReturnAfterRecvPrf

forkLeft' :: ForkPremiseD i i' i i' res res'
         -> KnownLenD l
         -> ExecWriter m ExecIndexInit (ExecIndexSome l' i' res') ()
         -> ExecWriter m (ExecIndexSome l i res)
                         (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                         ()
forkLeft' fPrf prf p = ExecWriter $ tell $
  \e -> ExecFork fPrf prf e $ execWriterToExec p

forkLeft :: ( ForkIndexComp i i'
            , MayOnlyReturnAfterRecv i res
            , MayOnlyReturnAfterRecv i' res'
            , KnownLen l
            )
         => ExecWriter m ExecIndexInit (ExecIndexSome l' i' res') ()
         -> ExecWriter m (ExecIndexSome l i res)
                         (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                         ()
forkLeft = forkLeft' getForkPremiseD getKnownLenPrf

forkRight' :: ForkPremiseD i i' i i' res res'
           -> KnownLenD l
           -> ExecWriter m ExecIndexInit (ExecIndexSome l i res) ()
           -> ExecWriter m (ExecIndexSome l' i' res')
                           (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                           ()
forkRight' fPrf prf p = ExecWriter $ tell $
  \e -> ExecFork fPrf prf (execWriterToExec p) e

forkRight :: ( ForkIndexComp i i'
             , MayOnlyReturnAfterRecv i res
             , MayOnlyReturnAfterRecv i' res'
             , KnownLen l
             )
          => ExecWriter m ExecIndexInit (ExecIndexSome l i res) ()
          -> ExecWriter m (ExecIndexSome l' i' res')
                           (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                           ()
forkRight = forkRight' getForkPremiseD getKnownLenPrf

connect' :: KnownIndex i
         => MayOnlyReturnAfterRecvD i res
         -> ListSplitD l p ('(x, y) : '(y, x) : rest)
         -- ^Proof of @l == p ++ ('(x, y) : '(y, x) : rest)@
         -> ExecWriter m (ExecIndexSome l i res) (ExecIndexSome (Concat p rest) i res) ()
connect' retPrf prf = ExecWriter $ tell $ ExecConn retPrf prf

connect :: -- forall l p i res x y rest m.
           ( KnownIndex i
           , MayOnlyReturnAfterRecv i res
           )
        => ListSplitD l p ('(x, y) : '(y, x) : rest)
        -> ExecWriter m (ExecIndexSome l i res) (ExecIndexSome (Concat p rest) i res) ()
connect p = connect' getMayOnlyReturnAfterRecvPrf p

swap :: ( KnownIndex i
        , Monad m
        )
      => ListSplitD l p (f:s:rest)
      -- ^Proof of @l == p ++ (f:s:rest)@
      -> ExecWriter m (ExecIndexSome l i res) (ExecIndexSome (Concat p (s:f:rest)) i res) ()
swap prf = ExecWriter $ tell $ ExecSwap prf

guard :: forall l i res m. ExecWriter m (ExecIndexSome l i res) (ExecIndexSome l i res) ()
guard = xreturn ()

-- |Run an execution.
--
-- Note that the list of free channels must be empty, i.e. all channels must be
-- bound for an execution to be defined.
runExec :: Monad m
        => Exec '[] m NextSend a
        -> m a
runExec = escapeSyncT . f
  where
    f :: Monad m
      => Exec ach m i a
      -> AsyncT ach m i i a
    f = \case
      ExecProc _ p -> p
      ExecFork fPrf prf l r -> fork_ fPrf prf (f l) (f r)
      ExecSwap k p -> swap_ k $ f p
      ExecConn retPrf k p -> connect_ retPrf k $ f p

-- |Interactive action with no free channels can be interpreted as local.
--
-- Apply this function once you've bound all the free channels to run the execution.
escapeSyncT :: Monad m
            => AsyncT '[] m NextSend NextSend a
            -> m a
escapeSyncT cont = runTillSend cont >>= \case
  SrSend (SomeFstMessage contra _) _ -> case contra of {}
  SrHalt res -> pure res
