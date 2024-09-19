{-# LANGUAGE ScopedTypeVariables #-}

module LUCk.Monad.Sync (
  -- * Interactive Algorithm Monad
  -- $monad
    SyncT(..)
  , freeSync
  , lift
  -- , catch
  -- * Syntax
  -- $actions
  , SyncActions(..)
  -- * Derived Definitions
  , SyncT
  -- * Step-by-step Execution
  -- $step
  , runTillCall
  , CallRes(..)
) where

import qualified Control.Monad as Monad
import Data.Functor

import Control.Monad.Free

import LUCk.Types
import LUCk.Monad.Class

-- $actions
--
-- Actions are given in Free monad syntax.

data SyncActions (m :: Type -> Type) (sch :: [(Type, Type)]) a where
  -- |Perform a call to a child, immediately getting the result
  CallAction :: Chan x y sch -> x -> (y -> a) -> SyncActions m sch a
  -- |Run a local action in the inner monad.
  LiftAction :: m x -> (x -> a) -> SyncActions m sch a

instance Functor (SyncActions m sch) where
  fmap f (CallAction i m cont) = CallAction i m $ f . cont
  fmap f (LiftAction m cont) = LiftAction m $ f . cont

-- $monad

-- |Non-indexed transformer that adds syncronous `call` (channels given by
-- @sch@) to monad @m@.
--
-- If you need exceptions in `SyncT`, feel free to use regular monadic
-- mechanisms such as `ExceptT` or `MaybeT`.
--
-- `SyncT` does not handle asynchronous interaction, therefore (unlike
-- `AsyncT`) it is a regular monad, not an indexed one. Consider code below for
-- an example. The function @reportSum@ has access to to oracles: oracle A with
-- requests of type `String`, and responses of type `Int`; and oracle B with
-- request of type `()` and responses of type `String`.
--
-- @
--   reportSum :: `SyncT` m '[ '(String, Int), '((), String)] (Int, String)
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
-- `LUCk.Monad.SyncT.Eval.Oracle.runWithOracles2`.
newtype SyncT sch m a
    = SyncT { runSyncT :: Free (SyncActions sch m) a }
  deriving (Functor)

instance Applicative (SyncT m sch) where
  f <*> m = SyncT $ runSyncT f <*> runSyncT m
  pure = SyncT . pure

instance Monad (SyncT m sch) where
  m >>= f = SyncT $ runSyncT m Monad.>>= (runSyncT . f)

freeSync :: SyncActions m sch a -> SyncT m sch a
freeSync = SyncT . liftF

-- Sync

lift :: m a -> SyncT m sch a
lift m = freeSync $ LiftAction m id

instance Print m => Print (SyncT m sch) where
  debugPrint = lift . debugPrint

instance Rand m => Rand (SyncT m sch) where
  rand = lift $ rand

instance Sync (SyncT m sch) sch where
  call i x = freeSync $ CallAction i x id

-- $step
--
-- The following functions let you evaluate an interactive algorithm
-- step-by-step.

-- |The result of `runTillCall`
data CallRes (m :: Type -> Type) (sch :: [(Type, Type)]) a where
  -- |Algorithm called `sendFinal`.
  CrCall :: Chan x y sch
         -> x
         -> (y -> SyncT m sch a)
         -> CallRes m sch a
  -- |Algorithm halted without sending anything
  CrHalt :: a
         -> CallRes m sch a

-- |Given `SyncT` action starting in `True` state (holding write token), run
-- it until it does `call`, `send` or halts.
runTillCall :: Monad m
            => SyncT m sch a
            -> m (CallRes m sch a)
runTillCall (SyncT (Pure v)) = pure $ CrHalt v
runTillCall (SyncT (Free v)) = case v of
  CallAction i x cont -> pure $ CrCall i x $ SyncT . cont
  LiftAction m cont -> m >>= runTillCall . SyncT . cont
