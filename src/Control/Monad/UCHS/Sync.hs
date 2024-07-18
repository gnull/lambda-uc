{-# LANGUAGE DerivingVia #-}

module Control.Monad.UCHS.Sync (
  -- * Interactive Algorithm Monad
  -- $monad
    SyncAlgo(..)
  , SyncPars(..)

  -- * Basic Operations
  -- $basic
  -- , yield
  , accept
  , yield
  , call
  , debugPrint
  , rand
  , throw
  -- , catch
  -- * Syntax
  -- $actions
  , SyncActions(..)
) where

import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad
import Control.XFreer
import Control.XApplicative
import Control.XMonad
-- import qualified Control.XMonad.Do as M

-- import Data.Type.Equality ((:~:)(Refl))

import Types

import Data.Kind (Type)

-- |The parameters of @SyncAlgo@ that do not change throughout the execution
data SyncPars = SyncPars
  { stPr :: Bool
  -- ^Printing allowed?
  , stRa :: Bool
  -- ^Probabilistic choices allowed?
  , stEx :: [(Type, Bool)]
  -- ^Type of exceptions we throw and contexts (use @[]@ to disable exceptions)
  , stUp :: (Type, Type)
  -- ^The upstream interface to our parent
  , stDown :: [(Type, Type)]
  -- ^Downstream interfaces to our children
  }

-- $actions
--
-- Actions are given in Free monad syntax.


-- |Defines actions for:
--
-- - @bef@ and @aft@ are the states before and after the given action.
data SyncActions (st :: SyncPars) (bef :: Bool) (aft :: Bool) a where
  -- |Accept an oracle call from parent
  AcceptAction :: SyncActions ('SyncPars pr ra ex '(x, y) down) False True y
  -- |Yield the result of an oracle call from the parent
  YieldAction :: x -> SyncActions ('SyncPars pr ra ex '(x, y) down) True False ()
  -- |Perform a call to a child, immediately getting the result
  CallAction :: Chan x y down -> x -> SyncActions ('SyncPars pr ra ex up down) b b y

  -- Optional Actions that can be turned on/off with flags
  PrintAction :: String -> SyncActions ('SyncPars True ra ex up down) b b ()
  RandAction :: SyncActions ('SyncPars pr True ex up down) b b Bool
  ThrowAction :: InList '(e, b) ex -> e -> SyncActions ('SyncPars pr ra ex up down) b b' a

-- $monad

-- |The monad for expressing cryptographic algorithms.
--
-- By instantiating @SyncAlgo@ with different parameters, you can finely
-- control what side-effects you allow:
--
-- - @bef@ and @aft@ specify whether this action consumes and/or produces the Write Token.
newtype SyncAlgo
                 (st :: SyncPars)
                 (bef :: Bool) -- ^State before an action
                 (aft :: Bool) -- ^State after an action
                 a -- ^Returned value
    = SyncAlgo { fromSyncAlgo :: XFree (SyncActions st) bef aft a }

  deriving (Functor) via (XFree (SyncActions st) bef aft)

  deriving (XApplicative, XMonad) via (XFree (SyncActions st))

instance Applicative (SyncAlgo st bef bef) where
  f <*> m = SyncAlgo $ fromSyncAlgo f <*> fromSyncAlgo m
  pure = SyncAlgo . pure

instance Monad (SyncAlgo st bef bef) where
  m >>= f = SyncAlgo $ fromSyncAlgo m Monad.>>= (fromSyncAlgo . f)

-- $basic
--
-- The basic operations you can do in @SyncAlgo@.

-- |Accept an oracle call from parent
accept :: SyncAlgo ('SyncPars pr ra ex '(x, y) down) False True y
accept = SyncAlgo $ xfree $ AcceptAction

-- |Yield the response to parent oracle call
yield :: x -> SyncAlgo ('SyncPars pr ra ex '(x, y) down) True False ()
yield x = SyncAlgo $ xfree $ YieldAction x

-- |Call a child oracle, immediately getting the result
call :: Chan x y down -> x -> SyncAlgo ('SyncPars pr ra ex up down) b b y
call i x = SyncAlgo $ xfree $ CallAction i x

-- |Print debug message
debugPrint :: String -> SyncAlgo ('SyncPars True ra ex up down) b b ()
debugPrint s = SyncAlgo $ xfree $ PrintAction s

-- |Sample a random bit
rand :: SyncAlgo ('SyncPars pr True ex up down) b b Bool
rand = SyncAlgo $ xfree $ RandAction

-- |Throw an exception
throw :: InList '(e, b) ex -> e -> SyncAlgo ('SyncPars pr ra ex up down) b b' a
throw i ex = SyncAlgo $ xfree $ ThrowAction i ex

-- -- |Catch an exception. The handler must be prepared for any of the exceptions declared in @e@
-- catch :: SyncAlgo ('SyncPars pr ra e l) bef aft a
--       -- ^The computation that may throw an exception
--       -> (forall ex b. InList '(ex, b) e -> ex -> SyncAlgo ('SyncPars pr ra e' l) b aft a)
--       -- ^How to handle the exception
--       -> SyncAlgo ('SyncPars pr ra e' l) bef aft a
-- catch (SyncAlgo m) handler = SyncAlgo $ helper (\i e -> fromSyncAlgo $ handler i e) m
--   where
--     helper :: (forall ex b. InList '(ex, b) e -> ex -> XFree (SyncActions ('SyncPars pr ra e' l)) b aft a)
--            -> XFree (SyncActions ('SyncPars pr ra e l)) bef aft a
--            -> XFree (SyncActions ('SyncPars pr ra e' l)) bef aft a
--     helper h = \case
--       Pure v -> Pure v
--       Bind RecvAction f -> Bind RecvAction $ helper h . f
--       Bind (SendAction v) f -> Bind (SendAction v) $ helper h . f
--       Bind GetWTAction f -> Bind GetWTAction $ helper h . f
--       Bind (PrintAction s) f -> Bind (PrintAction s) $ helper h . f
--       Bind RandAction f -> Bind RandAction $ helper h . f
--       Bind (ThrowAction i e) _ -> h i e
