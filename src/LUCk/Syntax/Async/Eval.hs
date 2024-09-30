{-# LANGUAGE AllowAmbiguousTypes #-}

module LUCk.Syntax.Async.Eval
  (
  -- * Execution Syntax
  -- $exec
    Exec(..)
  , runExec
  -- * Monad for Building Executions
  -- $writer
  , ExecBuilder(..)
  , ExecIndex(..)
  , runExecBuilder
  -- ** Actions
  -- $actions
  , process
  , forkLeft
  , forkRight
  , connect
  , swap
  , execGuard
  , execInvariantM
  -- $explicit
  , process'
  , forkLeft'
  , forkRight'
  -- * Helper functions
  , getForkIndexSwap
  )
where

import Control.XApplicative
import Control.XMonad
import Control.XMonad.XAccum

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
  ExecProc :: SIndex i
           -- ^Index the process starts from
           -> MayOnlyReturnAfterRecvD i a
           -- ^Proof of @a@ not being `Void` only if @i == `NextSend`@
           -> AsyncT m ach i i a
           -- ^The code that the process will run
           -> Exec m ach i a
  -- |Combine two executions.
  ExecFork :: ForkIndexCompD i i'
           -- ^Proof of @i@ and @i'@ not being `NextSend` at the same time
           -> KnownLenD ach
           -> Exec ach m i a
           -- ^First forked process
           -> Exec ach' m i' a'
           -- ^Second forked process
           -> Exec (Concat ach ach') m (ForkIndexOr i i') (ChooseRet i i' a a')
  -- |Swap positions of two adjacent free channels.
  ExecSwap :: ListSplitD l p (f:l')
           -- ^Proof of @l == p ++ (f:l')@
           -> ListSplitD l' p' (s:rest)
           -- ^Proof of @l' == p' ++ (s:rest)@
           -> Exec l m i a
           -> Exec (Concat p (s : Concat p' (f:rest))) m i a
  -- |Connect two adjacent free channels of a given execution (making them bound).
  ExecConn :: ListSplitD l p ('(x, y) : l')
           -- ^ Proof of @l == p ++ [(x, y)] ++ l'@
           -> ListSplitD l' p' ('(y, x) : rest)
           -- ^ Proof of @l' == p' ++ [(y, x)] ++ rest@
           -> Exec l m i a
           -- ^Exectuion where we want to connect the channels
           -> Exec (Concat p (Concat p' rest)) m i a

execInvariant :: Exec ach m i a
              -> (SIndex i, MayOnlyReturnAfterRecvD i a)
execInvariant = \case
  ExecProc i prf _ -> (i, prf)
  ExecFork iPrf _ _ _ -> case iPrf of
    ForkIndexCompNone -> (getSIndex, getMayOnlyReturnAfterRecvPrf)
    ForkIndexCompFst -> (getSIndex, getMayOnlyReturnAfterRecvPrf)
    ForkIndexCompSnd -> (getSIndex, getMayOnlyReturnAfterRecvPrf)
  ExecSwap _ _ p -> execInvariant p
  ExecConn _ _ p -> execInvariant p

-- $writer
--
-- This section defines the `ExecBuilder` monad that simplifies the construction
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
-- The `ExecBuilder` monad aids in building `Exec` values in a modular
-- way and providing the programmer with feedback at each step. Each
-- `ExecBuilder` action internally stores a function @`Exec` l m i res ->
-- `Exec` l' m i' res'@ or a function @() -> `Exec` l m i res@ (given by the
-- `ExecIndex`). Two actions can be composed together if the corresponding
-- functions compose.
--
-- To get a runnable execution @`Exec` '[] m i res@, define a value of type
-- @`ExecBuilder` m `ExecIndexInit` (`ExecIndexSome` l i res) ()@ and pass it
-- to `runExecBuilder`. The result can be passed to `runExec` to actually
-- run it.  The basic actions available in `ExecBuilder` are `forkLeft`,
-- `forkRight`, `connect` and `swap`.

-- |Index of the `ExecBuilder` monad.
data ExecIndex
  = ExecIndexInit
  -- ^We haven't started any executions
  | ExecIndexSome [(Type, Type)] Index Type
  -- ^An execution with given @ach@, @i@, and @res@ is started

-- |Mapping from the indices of `ExecBuilder` to the indices of internal indexed
-- monoid @(->)@.
type MatchExecIndex :: (Type -> Type) -> ExecIndex -> Type
type family MatchExecIndex m i where
  MatchExecIndex _ ExecIndexInit = ()
  MatchExecIndex m (ExecIndexSome l i res) = Exec l m i res

-- Indexed writer that uses @`Exec` _ _ _ _ -> `Exec` _ _ _ _@ as internal indexed monoid.
type ExecBuilder :: (Type -> Type) -> ExecIndex -> ExecIndex -> Type -> Type
newtype ExecBuilder m i j a = ExecBuilder
  { fromExecBuilder :: XAccum (MatchExecIndex m i) (MatchExecIndex m j) a
  }
  deriving (Functor)

instance XApplicative (ExecBuilder m) where
  xpure = ExecBuilder . xpure
  f <*>: x = ExecBuilder $ fromExecBuilder f <*>: fromExecBuilder x

instance XMonad (ExecBuilder m) where
  m >>=: f = ExecBuilder $ fromExecBuilder m >>=: (fromExecBuilder . f)

-- |Extract the internal `Exec` from `ExecBuilder`.
--
-- Note that `ExecBuilder m i j ()` internally stores a function
-- @`MatchExecIndex` i -> `MatchExecIndex` j@. The function can be extracted
-- using `runXWriter`.
--
-- At the same time, @`MatchExecIndex` `ExecIndexInit` = ()`@. Therefore,
-- @`ExecBuilder` m `ExecIndexInit` (`ExecIndexSome` l i res)@ stores a function
-- @() -> `Exec` m l i res@, which is isomorphic to just value @`Exec` m l i
-- res@, which this functions extracts.
runExecBuilder :: ExecBuilder m ExecIndexInit (ExecIndexSome l i res) ()
                 -> MatchExecIndex m (ExecIndexSome l i res)
runExecBuilder p = fst $ runXAccum (fromExecBuilder p) ()

-- $actions
--
-- The following are basic actions you can perform in `ExecBuilder`. The
-- `process`, `forkLeft`, `forkRight`, `connect`, `swap` correpond to the
-- constructors of `Exec`. The difference between `forkLeft` and `forkRight` is
-- merely in the order of composing the child nodes.
--
-- The @`execGuard` = xreturn ()@ has no effect in the monad, but can be inserted
-- in-between other operations in `ExecBuilder` to annotate the current
-- context. This can be used to document the code, while having the compiler
-- verify that the annotation is correct. In some rare cases, `execGuard` can also
-- be used to resolve ambiguous types.

-- $explicit
--
-- Following are the versions of `process`, `forkLeft` and `forkRight` that
-- take the proofs as explicit arguments instead of implicit typeclass
-- constraints.

process' :: SIndex i
         -> MayOnlyReturnAfterRecvD i res
         -- ^Proof of @res@ not being `Void` only if @i == `NextSend`@
         -> AsyncT l m i i res
         -- ^The program that the created process will run
         -> ExecBuilder m ExecIndexInit (ExecIndexSome l i res) ()
process' i retPrf = ExecBuilder . add . const . ExecProc i retPrf

process :: (KnownIndex i, MayOnlyReturnAfterRecv i res)
        => AsyncT l m i i res
        -- ^The program that the created process will run
        -> ExecBuilder m ExecIndexInit (ExecIndexSome l i res) ()
process = process' getSIndex getMayOnlyReturnAfterRecvPrf

forkLeft' :: ForkIndexCompD i i'
          -- ^Proof of @i@ and @i'@ not being `NextSend` both
          -> KnownLenD l
          -- ^Length of list `l` (left branch)
          -> ExecBuilder m ExecIndexInit (ExecIndexSome l' i' res') ()
          -- ^Right branch of the fork
          -> ExecBuilder m (ExecIndexSome l i res)
                          (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                          ()
forkLeft' fPrf prf p = ExecBuilder $ add $
  \e -> ExecFork fPrf prf e $ runExecBuilder p

forkLeft :: ( ForkIndexComp i i'
            , KnownLen l
            )
         => ExecBuilder m ExecIndexInit (ExecIndexSome l' i' res') ()
         -- ^Right branch of the fork
         -> ExecBuilder m (ExecIndexSome l i res)
                         (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                         ()
forkLeft = forkLeft' getForkIndexComp getKnownLenPrf

forkRight' :: ForkIndexCompD i i'
           -- ^Proof of @i@ and @i'@ not being `NextSend` both
           -> KnownLenD l
           -- ^Length of list `l` (left branch)
           -> ExecBuilder m ExecIndexInit (ExecIndexSome l i res) ()
           -- ^Left branch of the fork
           -> ExecBuilder m (ExecIndexSome l' i' res')
                           (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                           ()
forkRight' fPrf prf p = ExecBuilder $ add $
  \e -> ExecFork fPrf prf (runExecBuilder p) e

forkRight :: ( ForkIndexComp i i'
             , KnownLen l
             )
          => ExecBuilder m ExecIndexInit (ExecIndexSome l i res) ()
          -- ^Left branch of the fork
          -> ExecBuilder m (ExecIndexSome l' i' res')
                           (ExecIndexSome (Concat l l') (ForkIndexOr i i') (ChooseRet i i' res res'))
                           ()
forkRight = forkRight' getForkIndexComp getKnownLenPrf

connect :: ListSplitD l p ('(x, y) : l')
        -- ^ Proof of @l == p ++ [(x, y)] ++ l'@
        -> ListSplitD l' p' ('(y, x) : rest)
        -- ^ Proof of @l' == p' ++ [(y, x)] ++ rest@
        -> ExecBuilder m (ExecIndexSome l i res) (ExecIndexSome (Concat p (Concat p' rest)) i res) ()
connect prf prf' = ExecBuilder $ add $ ExecConn prf prf'

swap :: ListSplitD l p (f:l')
     -- ^Proof of @l == p ++ (f:l')@
     -> ListSplitD l' p' (s:rest)
     -- ^Proof of @l' == p' ++ (s:rest)@
     -> ExecBuilder m (ExecIndexSome l i res) (ExecIndexSome (Concat p (s : Concat p' (f:rest))) i res) ()
swap prf prf' = ExecBuilder $ add $ ExecSwap prf prf'

execGuard :: forall l i res m. ExecBuilder m (ExecIndexSome l i res) (ExecIndexSome l i res) ()
execGuard = xreturn ()

execInvariantM :: ExecBuilder m (ExecIndexSome ach i a) (ExecIndexSome ach i a)
                                (SIndex i, MayOnlyReturnAfterRecvD i a)
execInvariantM = execInvariant <$> ExecBuilder look

-- |Run an execution.
--
-- Note that the list of free channels must be empty, i.e. all channels must be
-- bound for an execution to be defined.
runExec :: Monad m
        => Exec '[] m NextSend a
        -> m a
runExec = escapeAsyncT . f
  where
    f :: Monad m
      => Exec ach m i a
      -> AsyncT ach m i i a
    f e = case e of
      ExecProc _ _ p -> p
      ExecFork fPrf prf l r -> let
          (_, lPrf) = execInvariant l
          (_, rPrf) = execInvariant r
        in fork_ (ForkPremiseD fPrf fPrf lPrf rPrf) prf (f l) (f r)
      ExecSwap k k' p -> case execInvariant e of
        (SNextRecv, _) -> swap_ k k' $ f p
        (SNextSend, _) -> swap_ k k' $ f p
      ExecConn k k' p -> case execInvariant e of
        (SNextRecv, prf) -> connect_ prf k k' $ f p
        (SNextSend, prf) -> connect_ prf k k' $ f p
