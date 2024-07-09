module MachineMonad where

import Prelude hiding ((>>=), return)
import Control.XFreer
import Control.XMonad
import qualified Control.XMonad.Do as M

-- import Control.Monad.Trans.Class (MonadTrans(lift))

import Data.Type.Equality ((:~:)(Refl))

import HeterogenousList

import Data.Kind (Type)

-- |Augments the inner monad m with extra network actions.
--
-- * @m@ is the inner monad that may implement random values sampling and
--   logging.
-- * @l@ is the list of channels we can talk to.
-- * @bef@ and @aft@ are the states of write token before and after the given
--   action.
data CryptoActions (m :: Type -> Type) (l :: [Type]) (bef :: Bool) (aft :: Bool) (a :: Type) where
  LiftAction :: m x -> (x -> a) -> CryptoActions m l b b a
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

type CryptoMonad m l bef aft = XFree (CryptoActions m l) bef aft

-- |Run a computation from the inner monad
lift :: m a -> CryptoMonad m l x x a
lift m = xfree $ LiftAction m id

-- |Yield control to the machine behind the given channel
yield :: InList (x, y) l -> CryptoMonad m l True False ()
yield i = xfree $ YieldAction i ()

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Get the current state of the write token.
getWT :: CryptoMonad m l b b (SBool b)
getWT = xfree $ GetWTAction id

-- |Receive from any channel
recvAny :: CryptoMonad m l False True (SomeSndMessage l)
recvAny = xfree $ RecvAction id

-- |Receive from a specific channel. If an unexpected message arrives from
-- another channel, ignore it and yield back the control.
recv :: InList (x, y) l -> CryptoMonad m l False True y
recv i = M.do
  SomeSndMessage j m <- recvAny
  case areInListEqual i j of
    Just Refl -> pure m
    Nothing -> M.do
      yield j
      recv i

-- |Send a message to a given channel
send :: InList (x, y) l -> x -> CryptoMonad m l True False ()
send i m = sendMess $ SomeFstMessage i m

-- |Same as @send@, but arguments are packed into one
sendMess :: SomeFstMessage l -> CryptoMonad m l True False ()
sendMess m = xfree $ SendAction m ()

-- |Send message to a given channel and wait for a response
sendSync :: InList (x, y) l -> x -> CryptoMonad m l True True y
sendSync i m = M.do
  send i m
  recv i
