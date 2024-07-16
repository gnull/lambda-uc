{-# LANGUAGE DerivingVia #-}

module MachineMonad (
  -- * Interactive Algorithm Monad
  -- $monad
    CryptoMonad(..)
  , StaticPars(..)

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
  , CryptoActions(..)
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

-- |The parameters of @CryptoMonad@ that do not change throughout the execution
data StaticPars = StaticPars
  { stPrint :: Bool
  -- ^Printing allowed?
  , stRand :: Bool
  -- ^Probabilistic choices allowed?
  , stThrow :: [(Type, Bool)]
  -- ^Type of exceptions we throw and contexts (use @[]@ to disable exceptions)
  , stChans :: [Type]
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
data CryptoActions (st :: StaticPars) (bef :: Bool) (aft :: Bool) (a :: Type) where
  -- IPC actions: recv, send
  RecvAction :: CryptoActions ('StaticPars pr ra e l) False True (SomeSndMessage l)
  SendAction :: SomeFstMessage l -> CryptoActions ('StaticPars pr ra e l) True False ()

  -- |Get the current state of Write Token
  GetWTAction :: CryptoActions st b b (SBool b)

  -- Optional Actions that can be turned on/off with flags
  PrintAction :: String -> CryptoActions ('StaticPars True ra e l) b b ()
  RandAction :: CryptoActions ('StaticPars pr True e l) b b Bool
  ThrowAction :: InList '(ex, b) e -> ex -> CryptoActions ('StaticPars pr ra e l) b b' a

-- $monad

-- |The monad for expressing cryptographic algorithms.
--
-- By instantiating @CryptoMonad@ with different parameters, you can finely
-- control what side-effects you allow:
--
-- - @bef@ and @aft@ specify whether this action consumes and/or produces the Write Token.
newtype CryptoMonad
                 (st :: StaticPars)
                 (bef :: Bool) -- ^State of Write Token before an action
                 (aft :: Bool) -- ^State of Write Token after an action
                 a -- ^Returned value
    = CryptoMonad { fromCryptoMonad :: XFree (CryptoActions st) bef aft a }

  deriving (Functor) via (XFree (CryptoActions st) bef aft)

  deriving (XApplicative, XMonad) via (XFree (CryptoActions st))

instance Applicative (CryptoMonad st bef bef) where
  f <*> m = CryptoMonad $ fromCryptoMonad f <*> fromCryptoMonad m
  pure = CryptoMonad . pure

instance Monad (CryptoMonad st bef bef) where
  m >>= f = CryptoMonad $ fromCryptoMonad m Monad.>>= (fromCryptoMonad . f)

cryptoXFree :: CryptoActions st bef aft a -> CryptoMonad st bef aft a
cryptoXFree = CryptoMonad . xfree

-- $basic
--
-- The basic operations you can do in @CryptoMonad@.

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Get the current state of the write token.
getWT :: CryptoMonad st b b (SBool b)
getWT = cryptoXFree $ GetWTAction

-- |Receive from any channel
recvAny :: CryptoMonad ('StaticPars pr ra e l) False True (SomeSndMessage l)
recvAny = cryptoXFree $ RecvAction

-- |Same as @send@, but arguments are packed into one
sendMess :: SomeFstMessage l -> CryptoMonad ('StaticPars pr ra e l) True False ()
sendMess m = cryptoXFree $ SendAction m

-- |Print debug message
debugPrint :: String -> CryptoMonad ('StaticPars True ra e l) b b ()
debugPrint s = cryptoXFree $ PrintAction s

-- |Sample a random bit
rand :: CryptoMonad ('StaticPars pr True e l) b b Bool
rand = cryptoXFree $ RandAction

-- |Throw an exception
throw :: InList '(ex, b) e -> ex -> CryptoMonad ('StaticPars pr ra e l) b b' a
throw i ex = cryptoXFree $ ThrowAction i ex

-- |Catch an exception. The handler must be prepared for any of the exceptions declared in @e@
catch :: CryptoMonad ('StaticPars pr ra e l) bef aft a
      -- ^The computation that may throw an exception
      -> (forall ex b. InList '(ex, b) e -> ex -> CryptoMonad ('StaticPars pr ra e' l) b aft a)
      -- ^How to handle the exception
      -> CryptoMonad ('StaticPars pr ra e' l) bef aft a
catch (CryptoMonad m) handler = CryptoMonad $ helper (\i e -> fromCryptoMonad $ handler i e) m
  where
    helper :: (forall ex b. InList '(ex, b) e -> ex -> XFree (CryptoActions ('StaticPars pr ra e' l)) b aft a)
           -> XFree (CryptoActions ('StaticPars pr ra e l)) bef aft a
           -> XFree (CryptoActions ('StaticPars pr ra e' l)) bef aft a
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
recv :: InList (x, y) l -> CryptoMonad ('StaticPars pr ra '[ '((), True) ] l) False True y
recv i = M.do
  SomeSndMessage j m <- recvAny
  case testEquality i j of
    Just Refl -> xpure m
    Nothing -> M.do
      throw Here ()

-- |Send a message to a given channel
send :: InList (x, y) l -> x -> CryptoMonad ('StaticPars pr ra e l) True False ()
send i m = sendMess $ SomeFstMessage i m

-- |Send message to a given channel and wait for a response
sendSync :: x -> InList (x, y) l -> CryptoMonad ('StaticPars pr ra '[ '((), True) ] l) True True y
sendSync m chan = M.do
  send chan m
  (SomeSndMessage i y) <- recvAny
  case testEquality i chan of
    Just Refl -> xpure y
    Nothing -> throw Here ()
