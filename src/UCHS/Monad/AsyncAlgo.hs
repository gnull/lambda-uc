{-# LANGUAGE DerivingVia #-}

module UCHS.Monad.AsyncAlgo (
  -- * Interactive Algorithm Monad
  -- $monad
    AsyncAlgo(..)
  , AsyncPars(..)
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
import qualified Control.XMonad.Do as M
import Data.Type.Equality ((:~:)(Refl))

-- import Control.Monad.Trans.Class (MonadTrans(lift))


import UCHS.Types
import UCHS.Monad.Class

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
  RandAction :: (Bounded v, Enum v) => (v -> a) -> AsyncActions ('AsyncPars pr True ex ch) b b a
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

-- Async

instance Print (AsyncAlgo ('AsyncPars True ra ex chans) b b) where
  debugPrint s = xfreeAsync $ PrintAction s ()

instance Rand (AsyncAlgo ('AsyncPars pr True ex chans) b b) where
  rand = xfreeAsync $ RandAction id

instance Throw (AsyncAlgo ('AsyncPars pr ra '[ '(ex, b)] chans) b b) ex where
  throw = xthrow Here

instance XThrow (AsyncAlgo ('AsyncPars pr ra ex chans)) ex where
  xthrow i ex = xfreeAsync $ ThrowAction i ex

instance XCatch
    (AsyncAlgo ('AsyncPars pr ra ex chans))
    ex
    (AsyncAlgo ('AsyncPars pr ra ex' chans))
  where
    xcatch (AsyncAlgo a) h = AsyncAlgo $ xcatch' a $ \i e -> fromAsyncAlgo (h i e)
      where
        xcatch' :: XFree (AsyncActions ('AsyncPars pr ra ex chans)) bef aft a
                -> (forall e b. InList '(e, b) ex -> e -> XFree (AsyncActions ('AsyncPars pr ra ex' chans)) b aft a)
                -> XFree (AsyncActions ('AsyncPars pr ra ex' chans)) bef aft a
        xcatch' (Pure x) _ = xreturn x
        xcatch' (Join a) h' = case a of
            RecvAction cont -> Join $ RecvAction $ (`xcatch'` h') . cont
            SendAction x r -> Join $ SendAction x $ r `xcatch'` h'
            GetWTAction cont -> Join $ GetWTAction $ (`xcatch'` h') . cont
            PrintAction v r -> Join $ PrintAction v $ r `xcatch'` h'
            RandAction cont -> Join $ RandAction $ (`xcatch'` h') . cont
            ThrowAction i e -> h' i e


instance GetWT (AsyncAlgo ('AsyncPars pr ra ex chans)) where
  getWT = xfreeAsync $ GetWTAction id

instance Async (AsyncAlgo ('AsyncPars pr ra ex chans)) chans where
  sendMess m = xfreeAsync $ SendAction m ()
  recvAny = xfreeAsync $ RecvAction id
