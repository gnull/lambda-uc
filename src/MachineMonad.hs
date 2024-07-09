{-# LANGUAGE DerivingVia #-}

module MachineMonad (
  -- * Interactive Algorithm Monad
  --
  -- $monad
    CryptoMonad(..)
  -- * Basic Operations
  , lift
  , yield
  , getWT
  , recvAny
  , recv
  , send
  , sendMess
  , sendSync
  , SBool(..)
  -- * Syntax
  --
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

import HeterogenousList

import Data.Kind (Type)

-- $actions
--
-- Actions are given in Free monad syntax.


-- |Augments the inner monad m with extra network actions.
--
-- * @m@ is the inner monad that may implement random values sampling and
--   logging.
-- * @l@ is the list of channels we can talk to.
-- * @bef@ and @aft@ are the states of write token before and after the given
--   action.
data CryptoActions (m :: Type -> Type) (l :: [Type]) (bef :: Bool) (aft :: Bool) (a :: Type) where
  LiftAction :: Monad m => m x -> (x -> a) -> CryptoActions m l b b a
  YieldAction :: InList (x, y) l -> a -> CryptoActions m l True False a
  GetWTAction :: (SBool b -> a) -> CryptoActions m l b b a
  RecvAction :: (SomeSndMessage l -> a) -> CryptoActions m l False True a
  SendAction :: SomeFstMessage l -> a -> CryptoActions m l True False a

instance Functor (CryptoActions m l bef aft) where
  fmap f (LiftAction x cont) = LiftAction x $ f . cont
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m x) = SendAction m $ f x
  fmap f (YieldAction m x) = YieldAction m $ f x
  fmap f (GetWTAction cont) = GetWTAction $ f . cont

-- $monad

newtype CryptoMonad (m :: Type -> Type) -- ^Inner monad
                 (l :: [Type]) -- ^List of available communication channels
                 (bef :: Bool) -- ^State of Write Token before an action
                 (aft :: Bool) -- ^State of Write Token after an action
                 a -- ^Returned value
    = CryptoMonad { fromCryptoMonad :: XFree (CryptoActions m l) bef aft a }

  deriving (Functor) via (XFree (CryptoActions m l) bef aft)

  deriving (XApplicative, XMonad) via (XFree (CryptoActions m l))

instance Applicative (CryptoMonad m l bef bef) where
  f <*> m = CryptoMonad $ fromCryptoMonad f <*> fromCryptoMonad m
  pure = CryptoMonad . pure

instance Monad (CryptoMonad m l bef bef) where
  m >>= f = CryptoMonad $ fromCryptoMonad m Monad.>>= (fromCryptoMonad . f)

cryptoXFree :: CryptoActions m l bef aft a -> CryptoMonad m l bef aft a
cryptoXFree = CryptoMonad . xfree

-- |Run a computation from the inner monad
lift :: Monad m => m a -> CryptoMonad m l x x a
lift m = cryptoXFree $ LiftAction m id

-- |Yield control to the machine behind the given channel
yield :: InList (x, y) l -> CryptoMonad m l True False ()
yield i = cryptoXFree $ YieldAction i ()

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Get the current state of the write token.
getWT :: CryptoMonad m l b b (SBool b)
getWT = cryptoXFree $ GetWTAction id

-- |Receive from any channel
recvAny :: CryptoMonad m l False True (SomeSndMessage l)
recvAny = cryptoXFree $ RecvAction id

-- |Receive from a specific channel. If an unexpected message arrives from
-- another channel, ignore it and yield back the control.
recv :: InList (x, y) l -> CryptoMonad m l False True y
recv i = M.do
  SomeSndMessage j m <- recvAny
  case areInListEqual i j of
    Just Refl -> xpure m
    Nothing -> M.do
      yield j
      recv i

-- |Send a message to a given channel
send :: InList (x, y) l -> x -> CryptoMonad m l True False ()
send i m = sendMess $ SomeFstMessage i m

-- |Same as @send@, but arguments are packed into one
sendMess :: SomeFstMessage l -> CryptoMonad m l True False ()
sendMess m = cryptoXFree $ SendAction m ()

-- |Send message to a given channel and wait for a response
sendSync :: InList (x, y) l -> x -> CryptoMonad m l True True y
sendSync i m = M.do
  send i m
  recv i
