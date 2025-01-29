{-# LANGUAGE AllowAmbiguousTypes #-}

module LUCk.Syntax.Async.Eval
  (
  -- * Execution Syntax
  -- $exec
    Exec(..)
  , runExec
  , runExecAsync
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
  , link
  , swap
  , spawnOnDemand
  , execGuard
  , execInvariantM
  -- $explicit
  , process'
  , forkLeft'
  , forkRight'
  , spawnOnDemand'
  -- * Helper functions
  , getForkIndexSwap
  , InitStatus(..)
  , InitStatusIndexRetD(..)
  )
where

import Control.XApplicative
import Control.XMonad
import Control.XMonad.XAccum

import LUCk.Syntax.Async.Eval.Internal
import LUCk.Syntax.Async
import qualified LUCk.Syntax.PrAlgo as L
import LUCk.Types

-- $exec
--
-- This section defines syntax for distributed exection of processes.
--
-- You define your processes and their links as a value of type `Exec`,
-- and then run it using `runExec`.
--
-- You start with the processes defined as @`AsyncT` m ach i i a`@ wrapped
-- in `ExecProc`, then you combine them using `ExecFork`, `ExecLink` and
-- `ExecSwap` until you've linked all the free ports and left with
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

data Exec ach (i :: InitStatus) where
  -- |An execution consisting of one process.
  ExecProc :: InitStatusIndexRetD st i res
           -- ^Proof of @a@ not being `Void` only if @i == `NextSend`@
           -> AsyncT ach i i res
           -- ^The code that the process will run
           -> Exec ach st
  ExecSpawnOnDemand :: forall l r ports.
                       ConstrAllD Ord l
                    -> ConstrAllD Ord r
                    -> KnownHPPortsD ports
                    -> KnownLenD l
                    -> KnownLenD r
                    -> (HListPair l r -> Exec ports InitAbsent)
                    -> Exec (MapConcat2 l r ports) InitAbsent
  -- |Combine two executions.
  ExecFork :: InitStatusCompD st st'
           -- ^Proof of @i@ and @i'@ not being `NextSend` at the same time
           -> KnownLenD ach
           -> Exec ach st
           -- ^First forked process
           -> Exec ach' st'
           -- ^Second forked process
           -> Exec (Concat ach ach') (InitStatusOr st st')
  -- |Swap positions of two adjacent free ports.
  ExecSwap :: ListSplitD l p (f:l')
           -- ^Proof of @l == p ++ (f:l')@
           -> ListSplitD l' p' (s:rest)
           -- ^Proof of @l' == p' ++ (s:rest)@
           -> Exec l st
           -> Exec (Concat p (s : Concat p' (f:rest))) st
  -- |Link two adjacent free ports of a given execution (making them bound).
  ExecLink :: ListSplitD l p (x :> y : l')
           -- ^ Proof of @l == p ++ [x :> y] ++ l'@
           -> ListSplitD l' p' (y :> x : rest)
           -- ^ Proof of @l' == p' ++ [y :> x] ++ rest@
           -> Exec l st
           -- ^Exectuion where we want to link the ports
           -> Exec (Concat p (Concat p' rest)) st

execInvariant :: Exec ach st
              -> SomeInitStatusIndexRetD st
execInvariant ex = case ex of
  ExecProc prf _ -> case prf of
    InitStatusIndexRetAbsent -> SomeInitStatusIndexRetD InitStatusIndexRetAbsent
    InitStatusIndexRetPresent -> SomeInitStatusIndexRetD InitStatusIndexRetPresent
  ExecSpawnOnDemand {} -> SomeInitStatusIndexRetD InitStatusIndexRetAbsent
  ExecFork iPrf _ _ _ -> case iPrf of
    InitStatusNone -> SomeInitStatusIndexRetD InitStatusIndexRetAbsent
    InitStatusFst -> SomeInitStatusIndexRetD InitStatusIndexRetPresent
    InitStatusSnd -> SomeInitStatusIndexRetD InitStatusIndexRetPresent
  ExecSwap _ _ p -> execInvariant p
  ExecLink _ _ p -> execInvariant p

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
-- `forkRight`, `link` and `swap`.

-- |Index of the `ExecBuilder` monad.
data ExecIndex
  = ExecIndexInit
  -- ^We haven't started any executions
  | ExecIndexSome [Port] InitStatus
  -- ^An execution with given @ach@, @i@, and @res@ is started

-- |Mapping from the indices of `ExecBuilder` to the indices of internal indexed
-- monoid @(->)@.
type MatchExecIndex :: ExecIndex -> Type
type family MatchExecIndex i where
  MatchExecIndex ExecIndexInit = ()
  MatchExecIndex (ExecIndexSome l st) = Exec l st

-- Indexed writer that uses @`Exec` _ _ _ _ -> `Exec` _ _ _ _@ as internal indexed monoid.
type ExecBuilder :: ExecIndex -> ExecIndex -> Type -> Type
newtype ExecBuilder i j a = ExecBuilder
  { fromExecBuilder :: XAccum (MatchExecIndex i) (MatchExecIndex j) a
  }
  deriving (Functor)

instance XApplicative ExecBuilder where
  xpure = ExecBuilder . xpure
  f <*>: x = ExecBuilder $ fromExecBuilder f <*>: fromExecBuilder x

instance XMonad ExecBuilder where
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
runExecBuilder :: ExecBuilder ExecIndexInit (ExecIndexSome l st) ()
                 -> MatchExecIndex (ExecIndexSome l st)
runExecBuilder p = fst $ runXAccum (fromExecBuilder p) ()

-- $actions
--
-- The following are basic actions you can perform in `ExecBuilder`. The
-- `process`, `forkLeft`, `forkRight`, `link`, `swap` correpond to the
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

process' :: InitStatusIndexRetD st i res
         -- ^Proof of @res@ not being `Void` only if @i == `NextSend`@
         -> AsyncT l i i res
         -- ^The program that the created process will run
         -> ExecBuilder ExecIndexInit (ExecIndexSome l st) ()
process' prf = ExecBuilder . add . const . ExecProc prf

process :: (InitStatusIndexRet st i res)
        => AsyncT l i i res
        -- ^The program that the created process will run
        -> ExecBuilder ExecIndexInit (ExecIndexSome l st) ()
process = process' getInitStatusIndexRetD

forkLeft' :: InitStatusCompD st st'
          -- ^Proof of @i@ and @i'@ not being `NextSend` both
          -> KnownLenD l
          -- ^Length of list `l` (left branch)
          -> ExecBuilder ExecIndexInit (ExecIndexSome l' st') ()
          -- ^Right branch of the fork
          -> ExecBuilder (ExecIndexSome l st)
                         (ExecIndexSome (Concat l l') (InitStatusOr st st'))
                         ()
forkLeft' fPrf prf p = ExecBuilder $ add $
  \e -> ExecFork fPrf prf e $ runExecBuilder p

forkLeft :: ( InitStatusComp st st'
            , KnownLen l
            )
         => ExecBuilder ExecIndexInit (ExecIndexSome l' st') ()
         -- ^Right branch of the fork
         -> ExecBuilder (ExecIndexSome l st)
                        (ExecIndexSome (Concat l l') (InitStatusOr st st'))
                        ()
forkLeft = forkLeft' getInitStatusCompD getKnownLenPrf

forkRight' :: InitStatusCompD st st'
           -- ^Proof of @i@ and @i'@ not being `NextSend` both
           -> KnownLenD l
           -- ^Length of list `l` (left branch)
           -> ExecBuilder ExecIndexInit (ExecIndexSome l st) ()
           -- ^Left branch of the fork
           -> ExecBuilder (ExecIndexSome l' st')
                          (ExecIndexSome (Concat l l') (InitStatusOr st st'))
                          ()
forkRight' fPrf prf p = ExecBuilder $ add $
  \e -> ExecFork fPrf prf (runExecBuilder p) e

forkRight :: ( InitStatusComp st st'
             , KnownLen l
             )
          => ExecBuilder ExecIndexInit (ExecIndexSome l st) ()
          -- ^Left branch of the fork
          -> ExecBuilder (ExecIndexSome l' st')
                         (ExecIndexSome (Concat l l') (InitStatusOr st st'))
                         ()
forkRight = forkRight' getInitStatusCompD getKnownLenPrf

link :: ListSplitD l p (x :> y : l')
        -- ^ Proof of @l == p ++ [(x, y)] ++ l'@
        -> ListSplitD l' p' (y :> x : rest)
        -- ^ Proof of @l' == p' ++ [(y, x)] ++ rest@
        -> ExecBuilder (ExecIndexSome l st) (ExecIndexSome (Concat p (Concat p' rest)) st) ()
link prf prf' = ExecBuilder $ add $ ExecLink prf prf'

swap :: ListSplitD l p (f:l')
     -- ^Proof of @l == p ++ (f:l')@
     -> ListSplitD l' p' (s:rest)
     -- ^Proof of @l' == p' ++ (s:rest)@
     -> ExecBuilder (ExecIndexSome l st) (ExecIndexSome (Concat p (s : Concat p' (f:rest))) st) ()
swap prf prf' = ExecBuilder $ add $ ExecSwap prf prf'

spawnOnDemand :: (ConstrAll Ord l, ConstrAll Ord r, KnownHPPorts ports, KnownLen l, KnownLen r)
              => (HListPair l r -> ExecBuilder ExecIndexInit (ExecIndexSome ports InitAbsent) ())
              -> ExecBuilder ExecIndexInit (ExecIndexSome (MapConcat2 l r ports) InitAbsent) ()
spawnOnDemand = spawnOnDemand' getConstrAllD getConstrAllD getKnownHPPorts getKnownLenPrf getKnownLenPrf

spawnOnDemand' :: forall l r ports.
                  ConstrAllD Ord l
               -> ConstrAllD Ord r
               -> KnownHPPortsD ports
               -> KnownLenD l
               -> KnownLenD r
               -> (HListPair l r -> ExecBuilder ExecIndexInit (ExecIndexSome ports InitAbsent) ())
               -> ExecBuilder ExecIndexInit (ExecIndexSome (MapConcat2 l r ports) InitAbsent) ()
spawnOnDemand' a b c d e f
  = ExecBuilder
  $ add
  $ \() -> ExecSpawnOnDemand a b c d e
  $ runExecBuilder . f

execGuard :: forall l st. ExecBuilder (ExecIndexSome l st) (ExecIndexSome l st) ()
execGuard = xreturn ()

execInvariantM
  :: ExecBuilder
       (ExecIndexSome ach st) (ExecIndexSome ach st)
       (SomeInitStatusIndexRetD st)
execInvariantM = execInvariant <$> ExecBuilder look

-- |Run an execution.
--
-- Note that the list of free ports must be empty, i.e. all ports must be
-- bound for an execution to be defined.
runExec :: Exec '[] (InitPresent a)
        -> L.PrAlgo a
runExec = escapeAsyncT . runExecAsync

runExecAsync :: Exec ach st
  -> AsyncT ach (InitStatusIndex st) (InitStatusIndex st) (InitStatusRes st)
runExecAsync e = case e of
  ExecProc prf p -> case prf of
    InitStatusIndexRetAbsent -> p
    InitStatusIndexRetPresent -> p
  ExecSpawnOnDemand a b c d e' runExecAsync' -> spawnOnDemand_ a b c d e' $ runExecAsync . runExecAsync'
  ExecFork fPrf prf l r -> case fPrf of
      InitStatusNone -> fork_ getForkPremiseD prf (runExecAsync l) (runExecAsync r)
      InitStatusFst -> fork_ getForkPremiseD prf (runExecAsync l) (runExecAsync r)
      InitStatusSnd -> fork_ getForkPremiseD prf (runExecAsync l) (runExecAsync r)
  ExecSwap k k' p -> case execInvariant e of
    SomeInitStatusIndexRetD InitStatusIndexRetAbsent
      -> swap_ k k' $ runExecAsync p
    SomeInitStatusIndexRetD InitStatusIndexRetPresent
      -> swap_ k k' $ runExecAsync p
  ExecLink k k' p -> case execInvariant e of
    SomeInitStatusIndexRetD InitStatusIndexRetAbsent
      -> link_ getMayOnlyReturnAfterRecvPrf k k' $ runExecAsync p
    SomeInitStatusIndexRetD InitStatusIndexRetPresent
      -> link_ getMayOnlyReturnAfterRecvPrf k k' $ runExecAsync p
