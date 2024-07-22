{-# LANGUAGE DerivingVia #-}

module UCHS.Monad.SyncAlgo (
  -- * Interactive Algorithm Monad
  -- $monad
    SyncAlgo(..)
  , SyncPars(..)
  , xfreeSync
  -- , catch
  -- * Syntax
  -- $actions
  , SyncActions(..)
) where

import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad
import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad
-- import qualified Control.XMonad.Do as M

-- import Data.Type.Equality ((:~:)(Refl))

import UCHS.Types
import UCHS.Monad.Class

import Data.Kind (Type)

-- |The parameters of @SyncAlgo@ that do not change throughout the execution
data SyncPars = SyncPars
  { stPr :: Bool
  -- ^Printing allowed?
  , stRa :: Bool
  -- ^Probabilistic choices allowed?
  , stEx :: [(Type, Bool)]
  -- ^Type of exceptions we throw and contexts (use @[]@ to disable exceptions)
  , stChans :: Maybe ((Type, Type), [(Type, Type)])
  -- ^The upstream interface to our parent and downstream interfaces to children.
  -- Using @Nothing@ here disables both types of interfaces
  }

-- $actions
--
-- Actions are given in Free monad syntax.


-- |Defines actions for:
--
-- - @bef@ and @aft@ are the states before and after the given action.
data SyncActions (st :: SyncPars) (bef :: Bool) (aft :: Bool) a where
  -- |Accept an oracle call from parent
  AcceptAction :: (y -> a) -> SyncActions ('SyncPars pr ra ex (Just '( '(x, y), down))) False True a
  -- |Yield the result of an oracle call from the parent
  YieldAction :: x -> a -> SyncActions ('SyncPars pr ra ex (Just '( '(x, y), down))) True False a
  -- |Perform a call to a child, immediately getting the result
  CallAction :: Chan x y down -> x -> (y -> a) -> SyncActions ('SyncPars pr ra ex (Just '( up, down))) b b a
  -- |Get the current state of write token
  GetWTAction :: (SBool b -> a) -> SyncActions ('SyncPars pr ra ex (Just '(up, down))) b b a

  -- Optional Actions that can be turned on/off with flags
  PrintAction :: String -> a -> SyncActions ('SyncPars True ra ex chans) b b a
  RandAction :: (Bounded v, Enum v) => (v -> a) -> SyncActions ('SyncPars pr True ex chans) b b a
  ThrowAction :: InList '(e, b) ex -> e -> SyncActions ('SyncPars pr ra ex chans) b b' a

instance Functor (SyncActions st bef aft) where
  fmap f (AcceptAction cont) = AcceptAction $ f . cont
  fmap f (YieldAction m r) = YieldAction m $ f r
  fmap f (CallAction i m cont) = CallAction i m $ f . cont
  fmap f (GetWTAction cont) = GetWTAction $ f . cont
  fmap f (PrintAction m r) = PrintAction m $ f r
  fmap f (RandAction cont) = RandAction $ f . cont
  fmap _ (ThrowAction i e) = ThrowAction i e

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

xfreeSync :: SyncActions st bef aft a -> SyncAlgo st bef aft a
xfreeSync = SyncAlgo . xfree

-- Sync

instance Print (SyncAlgo ('SyncPars True ra ex chans) b b) where
  debugPrint s = xfreeSync $ PrintAction s ()

instance Rand (SyncAlgo ('SyncPars pr True ex chans) b b) where
  rand = xfreeSync $ RandAction id

instance Throw (SyncAlgo ('SyncPars pr ra '[ '(ex, b)] chans) b b) ex where
  throw = xthrow Here

instance XThrow (SyncAlgo ('SyncPars pr ra ex chans)) ex where
  xthrow i ex = xfreeSync $ ThrowAction i ex

instance XCatch
    (SyncAlgo ('SyncPars pr ra ex chans))
    ex
    (SyncAlgo ('SyncPars pr ra ex' chans))
  where
    xcatch (SyncAlgo a) h = SyncAlgo $ xcatch' a $ \i e -> fromSyncAlgo (h i e)
      where
        xcatch' :: XFree (SyncActions ('SyncPars pr ra ex chans)) bef aft a
                -> (forall e b. InList '(e, b) ex -> e -> XFree (SyncActions ('SyncPars pr ra ex' chans)) b aft a)
                -> XFree (SyncActions ('SyncPars pr ra ex' chans)) bef aft a
        xcatch' (Pure x) _ = xreturn x
        xcatch' (Join a) h' = case a of
            AcceptAction cont -> Join $ AcceptAction $ (`xcatch'` h') . cont
            YieldAction x r -> Join $ YieldAction x $ r `xcatch'` h'
            CallAction i m cont -> Join $ CallAction i m $ (`xcatch'` h') . cont
            GetWTAction cont -> Join $ GetWTAction $ (`xcatch'` h') . cont
            PrintAction v r -> Join $ PrintAction v $ r `xcatch'` h'
            RandAction cont -> Join $ RandAction $ (`xcatch'` h') . cont
            ThrowAction i e -> h' i e

instance GetWT (SyncAlgo ('SyncPars pr ra ex (Just '(up, down)))) where
  getWT = xfreeSync $ GetWTAction id

instance SyncUp (SyncAlgo ('SyncPars pr ra ex (Just '( '(x, y), down)))) '(x, y) where
  accept = xfreeSync $ AcceptAction id
  yield x = xfreeSync $ YieldAction x ()

instance SyncDown (SyncAlgo ('SyncPars pr ra ex (Just '(up, down)))) down where
  call i x = xfreeSync $ CallAction i x id
