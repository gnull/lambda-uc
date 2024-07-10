{-# LANGUAGE DerivingVia #-}

module MachineMonad (
  -- * Interactive Algorithm Monad
  -- $monad
    CryptoMonad(..)

  -- * Basic Operations
  -- $basic
  , yield
  , recvAny
  , sendMess
  , SBool(..)
  , getWT
  , debugPrint
  , rand
  -- * Derived Operations
  -- $derived
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

-- $actions
--
-- Actions are given in Free monad syntax.


-- |Augments the inner monad m with extra network actions.
--
-- - @pr@ flag enables debug printing.
-- - @ra@ flag enables sampling random bits.
-- - @l@ is the list of channels we can talk to.
-- - @bef@ and @aft@ are the states of write token before and after the given
--   action.
data CryptoActions (pr :: Bool) (ra :: Bool) (l :: [Type]) (bef :: Bool) (aft :: Bool) (a :: Type) where
  -- IPC actions: recv, send and yield control to another thread
  YieldAction :: InList (x, y) l -> a -> CryptoActions pr ra l True False a
  RecvAction :: (SomeSndMessage l -> a) -> CryptoActions pr ra l False True a
  SendAction :: SomeFstMessage l -> a -> CryptoActions pr ra l True False a

  -- |Get the current state of Write Token
  GetWTAction :: (SBool b -> a) -> CryptoActions pr ra l b b a

  -- Optional Actions that can be turned on/off with flags
  PrintAction :: String -> a -> CryptoActions True ra l b b a
  RandAction :: (Bool -> a) -> CryptoActions pr True l b b a

instance Functor (CryptoActions pr ra l bef aft) where
  fmap f (YieldAction m x) = YieldAction m $ f x
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m x) = SendAction m $ f x
  fmap f (GetWTAction cont) = GetWTAction $ f . cont
  fmap f (PrintAction m x) = PrintAction m $ f x
  fmap f (RandAction cont) = RandAction $ f . cont

-- $monad

-- |The monad for expressing cryptographic algorithms.
--
-- By instantiating @CryptoMonad@ with different parameters, you can finely
-- control what side-effects you allow:
--
-- - @pr@ enables debug printing,
-- - @ra@ enables sampling random values,
-- - @l@ is the list of channels that the algorithm can communicate over (empty
--   @l@ means no communication),
-- - @bef@ and @aft@ specify whether this action consumes and/or produces the Write Token.
newtype CryptoMonad
                 (pr :: Bool) -- ^Debug printing allowed?
                 (ra :: Bool) -- ^Sampling random bits allowed?
                 (l :: [Type]) -- ^List of available communication channels
                 (bef :: Bool) -- ^State of Write Token before an action
                 (aft :: Bool) -- ^State of Write Token after an action
                 a -- ^Returned value
    = CryptoMonad { fromCryptoMonad :: XFree (CryptoActions pr ra l) bef aft a }

  deriving (Functor) via (XFree (CryptoActions pr ra l) bef aft)

  deriving (XApplicative, XMonad) via (XFree (CryptoActions pr ra l))

instance Applicative (CryptoMonad pr ra l bef bef) where
  f <*> m = CryptoMonad $ fromCryptoMonad f <*> fromCryptoMonad m
  pure = CryptoMonad . pure

instance Monad (CryptoMonad pr ra l bef bef) where
  m >>= f = CryptoMonad $ fromCryptoMonad m Monad.>>= (fromCryptoMonad . f)

cryptoXFree :: CryptoActions pr ra l bef aft a -> CryptoMonad pr ra l bef aft a
cryptoXFree = CryptoMonad . xfree

-- $basic
--
-- The basic operations you can do in @CryptoMonad@.

-- |Yield control to the machine behind the given channel
yield :: InList (x, y) l -> CryptoMonad pr ra l True False ()
yield i = cryptoXFree $ YieldAction i ()

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Get the current state of the write token.
getWT :: CryptoMonad pr ra l b b (SBool b)
getWT = cryptoXFree $ GetWTAction id

-- |Receive from any channel
recvAny :: CryptoMonad pr ra l False True (SomeSndMessage l)
recvAny = cryptoXFree $ RecvAction id

-- |Same as @send@, but arguments are packed into one
sendMess :: SomeFstMessage l -> CryptoMonad pr ra l True False ()
sendMess m = cryptoXFree $ SendAction m ()

-- |Print debug message
debugPrint :: String -> CryptoMonad True ra l b b ()
debugPrint s = cryptoXFree $ PrintAction s ()

-- |Sample a random bit
rand :: CryptoMonad pr True l b b Bool
rand = cryptoXFree $ RandAction id

-- $derived
--
-- Some convenient shorthand operations built from basic ones.

-- |Receive from a specific channel. If an unexpected message arrives from
-- another channel, ignore it and yield back the control.
recv :: InList (x, y) l -> CryptoMonad pr ra l False True y
recv i = M.do
  SomeSndMessage j m <- recvAny
  case testEquality i j of
    Just Refl -> xpure m
    Nothing -> M.do
      yield j
      recv i

-- |Send a message to a given channel
send :: InList (x, y) l -> x -> CryptoMonad pr ra l True False ()
send i m = sendMess $ SomeFstMessage i m

-- |Send message to a given channel and wait for a response
sendSync :: InList (x, y) l -> x -> CryptoMonad pr ra l True True y
sendSync i m = M.do
  send i m
  recv i
