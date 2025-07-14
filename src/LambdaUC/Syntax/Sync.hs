{-# LANGUAGE ScopedTypeVariables #-}

module LambdaUC.Syntax.Sync (
  -- * Interactive Algorithm Monad
  -- $monad
    SyncT(..)
  , freeSync
  , lift
  , call
  -- , catch
  -- * Syntax
  -- $actions
  , SyncActions(..)
  -- * Step-by-step Execution
  -- $step
  , runTillCall
  , CallRes(..)
) where

import qualified Control.Monad as Monad
import Control.Monad.Trans.Class as Trans

import Control.Monad.Free

import LambdaUC.Types

-- $actions
--
-- Actions are given in Free monad syntax.

data SyncActions (sch :: [Port]) (m :: Type -> Type) a where
  -- |Perform a call to a child, immediately getting the result
  CallAction :: PortInList x y sch -> x -> (y -> a) -> SyncActions sch m a
  -- |Run a local action in the inner monad.
  LiftAction :: m x -> (x -> a) -> SyncActions sch m a

instance Functor (SyncActions sch m) where
  fmap f (CallAction i m cont) = CallAction i m $ f . cont
  fmap f (LiftAction m cont) = LiftAction m $ f . cont

-- $monad

-- |Non-indexed transformer that adds syncronous `call` (ports given
-- by @sch@) to monad @m@ (lifted with `lift`). You will often see
-- `LambdaUC.Syntax.Algo.Algo` used as @m@, and `SyncT` will automatically
-- implement its typeclasses such as `Print` or `Rand`.
--
-- If you need exceptions in `SyncT`, feel free to use regular monadic
-- mechanisms such as `ExceptT` or `MaybeT`.
--
-- `SyncT` only adds syntax for synchronous interaction, therefore (unlike
-- `AsyncT`) it is a regular monad, not an indexed one. Consider code below for
-- an example. The function @reportSum@ has access to to oracles: oracle A with
-- requests of type `String`, and responses of type `Int`; and oracle B with
-- request of type `()` and responses of type `String`.
--
-- @
--   reportSum :: `SyncT` m '[P String Int, P () String] (Int, String)
--   reportSum = do
--     let a = Here
--         b = There Here
--     x <- `call` a "hello"
--     y <- `call` a "world"
--     z <- `call` b ()
--     `return` (x + y, z)
-- @
--
-- To run the code above, implement the oracles and use
-- `LambdaUC.Syntax.Sync.Eval.runWithOracles2`.
newtype SyncT sch m a
    = SyncT { runSyncT :: Free (SyncActions sch m) a }
  deriving (Functor)

instance Applicative (SyncT sch m) where
  f <*> m = SyncT $ runSyncT f <*> runSyncT m
  pure = SyncT . pure

instance Monad (SyncT sch m) where
  m >>= f = SyncT $ runSyncT m Monad.>>= (runSyncT . f)

freeSync :: SyncActions sch m a -> SyncT sch m a
freeSync = SyncT . liftF

-- Sync

instance Trans.MonadTrans (SyncT sch) where
  lift m = freeSync $ LiftAction m id

-- $sync
--
-- Side-effects of a syncronous interactive algorithm. Such an algorithm can
-- issue oracle calls to its children (`Sync`).
--
-- Oracle calls are synchronous: calling algorithm is put to sleep until the
-- oracle responds to the call.

call :: PortInList x y down -> x -> SyncT down m y
call i x = freeSync $ CallAction i x id

-- $step
--
-- The following functions let you evaluate a synchronous algorithm
-- step-by-step.

-- |The result of `runTillCall`
data CallRes (sch :: [Port]) (m :: Type -> Type) a where
  -- |Algorithm called `call`.
  CrCall :: PortInList x y sch
         -> x
         -> (y -> SyncT sch m a)
         -> CallRes sch m a
  -- |Algorithm halted without a `call`
  CrHalt :: a
         -> CallRes sch m a

-- |Given `SyncT` action starting in `True` state (holding write token), run
-- it until it does `call` or halts.
runTillCall :: Monad m
            => SyncT sch m a
            -> m (CallRes sch m a)
runTillCall (SyncT (Pure v)) = pure $ CrHalt v
runTillCall (SyncT (Free v)) = case v of
  CallAction i x cont -> pure $ CrCall i x $ SyncT . cont
  LiftAction m cont -> m >>= runTillCall . SyncT . cont
