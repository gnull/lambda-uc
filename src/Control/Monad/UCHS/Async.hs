{-# LANGUAGE DerivingVia #-}

module Control.Monad.UCHS.Async (
  -- * Interactive Algorithm Monad
  -- $monad
    AsyncAlgo(..)
  , AsyncPars(..)

  -- * Basic Operations
  -- $basic
  -- , yield
  , catch
  -- * Syntax
  -- $actions
  , AsyncActions(..)
  -- * Helper functions
  , xfreeAsync
) where

import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad
import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad

-- import Control.Monad.Trans.Class (MonadTrans(lift))


import Types

import Data.Kind (Type)

-- |The parameters of @AsyncAlgo@ that do not change throughout the execution
data AsyncPars = AsyncPars
  { stPr :: Bool
  -- ^Printing allowed?
  , stRa :: Bool
  -- ^Probabilistic choices allowed?
  , stEx :: [(Type, Bool)]
  -- ^Type of exceptions we throw and contexts (use @[]@ to disable exceptions)
  , stCh :: [(Type, Type)]
  -- ^Channels we can communicate with
  }

-- $actions
--
-- Actions are given in Free monad syntax.


-- |Defines actions for:
--
-- - sending/receiving messages through channels defined in @st@
-- - reading current state of write token
-- - sampling random bits
-- - debug printing
--
-- - @bef@ and @aft@ are the states of write token before and after the given
--   action.
data AsyncActions (st :: AsyncPars) (bef :: Bool) (aft :: Bool) (a :: Type) where
  -- IPC actions: recv, send
  RecvAction :: (SomeSndMessage ch -> a) -> AsyncActions ('AsyncPars pr ra ex ch) False True a
  SendAction :: SomeFstMessage ch -> a -> AsyncActions ('AsyncPars pr ra ex ch) True False a

  -- |Get the current state of Write Token
  GetWTAction :: (SBool b -> a) -> AsyncActions st b b a

  -- Optional Actions that can be turned on/off with flags
  PrintAction :: String -> a -> AsyncActions ('AsyncPars True ra ex ch) b b a
  RandAction :: (Bool -> a) -> AsyncActions ('AsyncPars pr True ex ch) b b a
  ThrowAction :: InList '(e, b) ex -> e -> AsyncActions ('AsyncPars pr ra ex ch) b b' a

instance Functor (AsyncActions st bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m r) = SendAction m $ f r
  fmap f (GetWTAction cont) = GetWTAction $ f . cont
  fmap f (PrintAction m r) = PrintAction m $ f r
  fmap f (RandAction cont) = RandAction $ f . cont
  fmap _ (ThrowAction i e) = ThrowAction i e

-- $monad

-- |The monad for expressing cryptographic algorithms.
--
-- By instantiating @AsyncAlgo@ with different parameters, you can finely
-- control what side-effects you allow:
--
-- - @bef@ and @aft@ specify whether this action consumes and/or produces the Write Token.
newtype AsyncAlgo
                 (st :: AsyncPars)
                 (bef :: Bool) -- ^State of Write Token before an action
                 (aft :: Bool) -- ^State of Write Token after an action
                 a -- ^Returned value
    = AsyncAlgo { fromAsyncAlgo :: XFree (AsyncActions st) bef aft a }

  deriving (Functor) via (XFree (AsyncActions st) bef aft)

  deriving (XApplicative, XMonad) via (XFree (AsyncActions st))

instance Applicative (AsyncAlgo st bef bef) where
  f <*> m = AsyncAlgo $ fromAsyncAlgo f <*> fromAsyncAlgo m
  pure = AsyncAlgo . pure

instance Monad (AsyncAlgo st bef bef) where
  m >>= f = AsyncAlgo $ fromAsyncAlgo m Monad.>>= (fromAsyncAlgo . f)

xfreeAsync :: AsyncActions st bef aft a -> AsyncAlgo st bef aft a
xfreeAsync = AsyncAlgo . xfree

-- $basic
--
-- The basic operations you can do in @AsyncAlgo@.

-- |Catch an exception. The handler must be prepared for any of the exceptions declared in @e@
catch :: AsyncAlgo ('AsyncPars pr ra e l) bef aft a
      -- ^The computation that may throw an exception
      -> (forall ex b. InList '(ex, b) e -> ex -> AsyncAlgo ('AsyncPars pr ra e' l) b aft a)
      -- ^How to handle the exception
      -> AsyncAlgo ('AsyncPars pr ra e' l) bef aft a
catch (AsyncAlgo m) handler = AsyncAlgo $ helper (\i e -> fromAsyncAlgo $ handler i e) m
  where
    helper :: (forall ex b. InList '(ex, b) e -> ex -> XFree (AsyncActions ('AsyncPars pr ra e' l)) b aft a)
           -> XFree (AsyncActions ('AsyncPars pr ra e l)) bef aft a
           -> XFree (AsyncActions ('AsyncPars pr ra e' l)) bef aft a
    helper h = \case
      Pure v -> Pure v
      Join (RecvAction cont) -> Join $ RecvAction $ helper h . cont
      Join (SendAction v r) -> Join $ SendAction v $ helper h r
      Join (GetWTAction cont) -> Join $ GetWTAction $ helper h . cont
      Join (PrintAction v r) -> Join $ PrintAction v $ helper h r
      Join (RandAction cont) -> Join $ RandAction $ helper h . cont
      Join (ThrowAction i e) -> h i e
