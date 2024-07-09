module MachineMonad where

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
  GetWTAction :: (SBool b -> a) -> CryptoActions l b b a

instance Functor (CryptoActions l bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m x) = SendAction m $ f x
  fmap f (WakeAction m x) = WakeAction m $ f x
  fmap f (RandAction cont) = RandAction $ f . cont
  fmap f (PrintAction m x) = PrintAction m $ f x
  fmap f (GetWTAction cont) = GetWTAction $ f . cont

type CryptoMonad l bef aft = XFree (CryptoActions l) bef aft

recvAny :: CryptoMonad l False True (SomeSndMessage l)
recvAny = xfree $ RecvAction id

getWT :: CryptoMonad l b b (SBool b)
getWT = xfree $ GetWTAction id

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
data SomeWT l bef x = forall aft. SomeWT (CryptoMonad l bef aft x)

-- |Like @SomeWT@, but lets you do some monadic computations before you decide
-- what state to leave the monad in.
data SomeWTM l bef x = forall i. SomeWTM (CryptoMonad l bef i (SomeWT l i x))

-- |Make a decision inside @SomeWTM@ computation.
decided :: CryptoMonad l i aft a -> CryptoMonad l i i (SomeWT l i a)
decided = xreturn . SomeWT

-- |Consume a @SomeWTM@ computation.
dispatchSomeWTM :: SomeWTM l bef x -> (forall i. x -> CryptoMonad l i aft a) -> CryptoMonad l bef aft a
dispatchSomeWTM (SomeWTM w) cont = M.do
  (SomeWT x) <- w
  x >>=: cont

-- |Demonstrates the use of @SomeWTM@. To express a computation that
-- dynamically chooses what state to leave the monad in, do the following:
--
-- 1. Wrap the whole thing in @SomeWTM@.
--
-- 2. Inside @SomeWTM@, wrap each branch where your WT state is fixed in
-- @decided@.
maybeSends :: InList (Bool, Bool) l -> SomeWTM l True Bool
maybeSends chan = SomeWTM $ M.do
  wake chan
  b <- recv chan
  -- wake chan
  case b of
    True -> decided $ M.do
      wake chan
      xreturn b
    False -> decided $ xreturn b


useMaybeSends :: InList (Bool, Bool) l -> CryptoMonad l True True Bool
useMaybeSends chan = M.do
  -- Step #1: pass @maybeSends@ to dispatchSomeWTM
  -- Step #2: pass it a continuation that starts from unknown WT state
  res <- dispatchSomeWTM (maybeSends chan) $ \b -> M.do
    -- _ -- in this context, the state of WT is unknown
    -- Step #3: match on the current WT and provide actions for every branch
    getWT >>=: \case
      STrue -> xreturn b
      SFalse -> M.do
        c <- recv chan
        xreturn c
  -- _ -- in this context, the state of WT is fixed
  xreturn $ not res

-- testFail :: CryptoMonad l False False ()
-- testFail = send "hey"

hey :: IO ()
hey = putStrLn "hello"
