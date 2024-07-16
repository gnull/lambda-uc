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
  -- * Derived Operations
  -- $derived
  -- , recv
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
  -- IPC actions: recv, send and yield control to another thread
  -- YieldAction :: InList (Maybe x, y) l -> a -> CryptoActions (StaticPars pr ra e l) True False a
  RecvAction :: (SomeSndMessage l -> a) -> CryptoActions ('StaticPars pr ra e l) False True a
  SendAction :: SomeFstMessage l -> a -> CryptoActions ('StaticPars pr ra e l) True False a

  -- |Get the current state of Write Token
  GetWTAction :: (SBool b -> a) -> CryptoActions st b b a

  -- Optional Actions that can be turned on/off with flags
  PrintAction :: String -> a -> CryptoActions ('StaticPars True ra e l) b b a
  RandAction :: (Bool -> a) -> CryptoActions ('StaticPars pr True e l) b b a
  ThrowAction :: InList '(ex, b) e -> ex -> CryptoActions ('StaticPars pr ra e l) b b' a

instance Functor (CryptoActions st bef aft) where
  -- fmap f (YieldAction m x) = YieldAction m $ f x
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m x) = SendAction m $ f x
  fmap f (GetWTAction cont) = GetWTAction $ f . cont
  fmap f (PrintAction m x) = PrintAction m $ f x
  fmap f (RandAction cont) = RandAction $ f . cont
  fmap _ (ThrowAction i ex) = ThrowAction i ex

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

-- |Yield control to the machine behind the given channel
-- yield :: InList (Maybe x, y) l -> CryptoMonad st True False ()
-- yield i = cryptoXFree $ YieldAction i ()

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Get the current state of the write token.
getWT :: CryptoMonad st b b (SBool b)
getWT = cryptoXFree $ GetWTAction id

-- |Receive from any channel
recvAny :: CryptoMonad ('StaticPars pr ra e l) False True (SomeSndMessage l)
recvAny = cryptoXFree $ RecvAction id

-- |Same as @send@, but arguments are packed into one
sendMess :: SomeFstMessage l -> CryptoMonad ('StaticPars pr ra e l) True False ()
sendMess m = cryptoXFree $ SendAction m ()

-- |Print debug message
debugPrint :: String -> CryptoMonad ('StaticPars True ra e l) b b ()
debugPrint s = cryptoXFree $ PrintAction s ()

-- |Sample a random bit
rand :: CryptoMonad ('StaticPars pr True e l) b b Bool
rand = cryptoXFree $ RandAction id

-- |Throw an exception
throw :: InList '(ex, b) e -> ex -> CryptoMonad ('StaticPars pr ra e l) b b' a
throw i ex = cryptoXFree $ ThrowAction i ex

-- catch :: CryptoMonad ('StaticPars pr ra e l) bef aft a
--       -- ^The computation that may throw an exception
--       -> (InList (ex, b) e -> ex -> CryptoMonad st b aft a)
--       -- ^How to handle the exception
--       -> CryptoMonad st bef aft a
-- catch (CryptoMonad m) h = helper h m
--   where
--     helper h = \case
--       Pure v -> xpure v
--       Bind x f -> case x of
--         RecvAction
--         SendAction
--         GetWTAction
--         PrintAction
--         RandAction
--         ThrowAction


-- $derived
--
-- Some convenient shorthand operations built from basic ones.

-- |Receive from a specific channel. If an unexpected message arrives from
-- another channel, ignore it and yield back the control.
-- recv :: InList (x, y) l -> CryptoMonad st False True y
-- recv i = M.do
--   SomeSndMessage j m <- recvAny
--   case testEquality i j of
--     Just Refl -> xpure m
--     Nothing -> M.do
--       yield j
--       recv i

-- |Send a message to a given channel
send :: InList (x, y) l -> x -> CryptoMonad ('StaticPars pr ra e l) True False ()
send i m = sendMess $ SomeFstMessage i m

-- |Send message to a given channel and wait for a response
sendSync :: x -> InList (x, y) l -> CryptoMonad ('StaticPars pr ra e l) True True y
sendSync m chan = M.do
  send chan m
  (SomeSndMessage i y) <- recvAny
  case testEquality i chan of
    Just Refl -> xpure y
    Nothing -> undefined -- TODO: use a cleaner error-handling mechanism
