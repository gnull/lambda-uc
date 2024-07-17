{-# LANGUAGE DerivingVia #-}

module Control.Monad.UCHS.Async (
  -- * Interactive Algorithm Monad
  -- $monad
    AsyncAlgo(..)
  , AsyncPars(..)

  -- * Basic Operations
  -- $basic
  -- , yield
  , recvAny
  , sendMess
  , SBool(..)
  , getWT
  , debugPrint
  , rand
  , throw
  , catch
  -- * Derived Operations
  -- $derived
  -- , recv
  , recv
  , send
  , sendSync
  -- * Syntax
  -- $actions
  , AsyncActions(..)
  -- * Helper functions
  , cryptoXFree
) where

import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad
import Control.XFreer
import Control.XApplicative
import Control.XMonad
import qualified Control.XMonad.Do as M

-- import Control.Monad.Trans.Class (MonadTrans(lift))

import Data.Type.Equality ((:~:)(Refl))

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
  RecvAction :: AsyncActions ('AsyncPars pr ra ex ch) False True (SomeSndMessage ch)
  SendAction :: SomeFstMessage ch -> AsyncActions ('AsyncPars pr ra ex ch) True False ()

  -- |Get the current state of Write Token
  GetWTAction :: AsyncActions st b b (SBool b)

  -- Optional Actions that can be turned on/off with flags
  PrintAction :: String -> AsyncActions ('AsyncPars True ra ex ch) b b ()
  RandAction :: AsyncActions ('AsyncPars pr True ex ch) b b Bool
  ThrowAction :: InList '(e, b) ex -> e -> AsyncActions ('AsyncPars pr ra ex ch) b b' a

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

cryptoXFree :: AsyncActions st bef aft a -> AsyncAlgo st bef aft a
cryptoXFree = AsyncAlgo . xfree

-- $basic
--
-- The basic operations you can do in @AsyncAlgo@.

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Get the current state of the write token.
getWT :: AsyncAlgo st b b (SBool b)
getWT = cryptoXFree $ GetWTAction

-- |Receive from any channel
recvAny :: AsyncAlgo ('AsyncPars pr ra e l) False True (SomeSndMessage l)
recvAny = cryptoXFree $ RecvAction

-- |Same as @send@, but arguments are packed into one
sendMess :: SomeFstMessage l -> AsyncAlgo ('AsyncPars pr ra e l) True False ()
sendMess m = cryptoXFree $ SendAction m

-- |Print debug message
debugPrint :: String -> AsyncAlgo ('AsyncPars True ra e l) b b ()
debugPrint s = cryptoXFree $ PrintAction s

-- |Sample a random bit
rand :: AsyncAlgo ('AsyncPars pr True e l) b b Bool
rand = cryptoXFree $ RandAction

-- |Throw an exception
throw :: InList '(ex, b) e -> ex -> AsyncAlgo ('AsyncPars pr ra e l) b b' a
throw i ex = cryptoXFree $ ThrowAction i ex

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
      Bind RecvAction f -> Bind RecvAction $ helper h . f
      Bind (SendAction v) f -> Bind (SendAction v) $ helper h . f
      Bind GetWTAction f -> Bind GetWTAction $ helper h . f
      Bind (PrintAction s) f -> Bind (PrintAction s) $ helper h . f
      Bind RandAction f -> Bind RandAction $ helper h . f
      Bind (ThrowAction i e) _ -> h i e

-- $derived
--
-- Some convenient shorthand operations built from basic ones.

-- |Receive from a specific channel. If an unexpected message arrives from
-- another channel, ignore it and yield back the control.
recv :: Chan x y l -> AsyncAlgo ('AsyncPars pr ra '[ '((), True) ] l) False True y
recv i = M.do
  SomeSndMessage j m <- recvAny
  case testEquality i j of
    Just Refl -> xpure m
    Nothing -> M.do
      throw Here ()

-- |Send a message to a given channel
send :: Chan x y l -> x -> AsyncAlgo ('AsyncPars pr ra e l) True False ()
send i m = sendMess $ SomeFstMessage i m

-- |Send message to a given channel and wait for a response
sendSync :: x -> Chan x y l -> AsyncAlgo ('AsyncPars pr ra '[ '((), True) ] l) True True y
sendSync m chan = M.do
  send chan m
  (SomeSndMessage i y) <- recvAny
  case testEquality i chan of
    Just Refl -> xpure y
    Nothing -> throw Here ()
