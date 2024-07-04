module ApproachXMonad where

import Prelude hiding ((>>=), return)
import Control.XFreer
import Control.XMonad
import qualified Control.XMonad.Do as M

import Data.Type.Equality ((:~:)(Refl))

import HeterogenousList

import Data.Kind (Type)

data CryptoActions (l :: [Type]) (bef :: Bool) (aft :: Bool) (a :: Type) where
  RecvAction :: (SomeSndMessage l -> a) -> CryptoActions l False True a
  SendAction :: SomeFstMessage l -> a -> CryptoActions l True False a
  WakeAction :: InList (x, y) l -> a -> CryptoActions l True False a
  RandAction :: (Bool -> a) -> CryptoActions l x x a
  PrintAction :: String -> a -> CryptoActions l x x a

instance Functor (CryptoActions l bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m x) = SendAction m $ f x
  fmap f (WakeAction m x) = WakeAction m $ f x
  fmap f (RandAction cont) = RandAction $ f . cont
  fmap f (PrintAction m x) = PrintAction m $ f x

type CryptoMonad l bef aft = XFree (CryptoActions l) bef aft

recvAny :: CryptoMonad l False True (SomeSndMessage l)
recvAny = xfree $ RecvAction id

sendMess :: SomeFstMessage l -> CryptoMonad l True False ()
sendMess m = xfree $ SendAction m ()

send :: InList (x, y) l -> x -> CryptoMonad l True False ()
send i m = sendMess $ SomeFstMessage i m

wake :: InList (x, y) l -> CryptoMonad l True False ()
wake i = xfree $ WakeAction i ()

recv :: InList (x, y) l -> CryptoMonad l False True y
recv i = M.do
  SomeSndMessage j m <- recvAny
  case areInListEqual i j of
    Just Refl -> pure m
    Nothing -> M.do
      wake j
      recv i

-- sendSync :: InList (x, y) l -> x -> CryptoMonad l True True y
-- sendSync i m = send i m >> recv

rand :: CryptoMonad l x x Bool
rand = xfree $ RandAction id

print :: String -> CryptoMonad l x x ()
print m = xfree $ PrintAction m ()

-- |Sends String s to the given channel, waits for the other side to repond with
test :: String -> InList (String, Int) l -> CryptoMonad l True True Int
test s chan = M.do
  send chan s
  recv chan

data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Allows you to express computations that may leave write token in either of
-- the two states. But the decision on which state to leave the monad in must
-- not be based on side-effects.
data PackWT l bef x = forall aft. SomeWT (SBool aft) (CryptoMonad l bef aft x)

-- |Hide the given aft index from the type.
packWT :: SBool aft -> CryptoMonad l bef aft x -> PackWT l bef x
packWT = SomeWT

-- |Wakes up whoever is on the other end of first channel if the passed
-- argument was True
maybeSends :: Bool -> PackWT ((x, y) : l) True ()
maybeSends True = packWT SFalse $ M.do
  wake Here
maybeSends False = packWT STrue $ M.do
  pure ()

-- testFail :: CryptoMonad l False False ()
-- testFail = send "hey"

hey :: IO ()
hey = putStrLn "hello"
