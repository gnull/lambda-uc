module GADTApproach where

import Prelude hiding ((>>=), return)
import Control.XFreer
import Control.XMonad
import qualified Control.XMonad.Do as M

import HeterogenousList

import Data.Kind (Type)

data CryptoActions (bef :: Bool) (aft :: Bool) (a :: Type) where
  RecvAction :: (String -> a) -> CryptoActions False True a
  SendAction :: String -> a -> CryptoActions True False a
  RandAction :: (Bool -> a) -> CryptoActions x x a
  PrintAction :: String -> a -> CryptoActions x x a

instance Functor (CryptoActions bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m x) = SendAction m $ f x
  fmap f (RandAction cont) = RandAction $ f . cont
  fmap f (PrintAction m x) = PrintAction m $ f x

type CryptoMonad bef aft = XFree CryptoActions bef aft

recv :: CryptoMonad False True String
recv = xfree $ RecvAction id

send :: String -> CryptoMonad True False ()
send m = xfree $ SendAction m ()

rand :: CryptoMonad x x Bool
rand = xfree $ RandAction id

print :: String -> CryptoMonad x x ()
print m = xfree $ PrintAction m ()

test :: String -> CryptoMonad True True String
test s = M.do
  send s
  recv

data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Allows you to express computations that may leave write token in either of
-- the two states. But the decision on which state to leave the monad in must
-- not be based on side-effects.
data PackWT bef x = forall aft. SomeWT (SBool aft) (CryptoMonad bef aft x)

-- |Hide the given aft index from the type.
packWT :: SBool aft -> CryptoMonad bef aft x -> PackWT bef x
packWT = SomeWT

maybeSends :: Bool -> PackWT True ()
maybeSends True = packWT SFalse $ M.do
  send "hello"
maybeSends False = packWT STrue $ M.do
  pure ()

-- testFail :: CryptoMonad False False ()
-- testFail = send "hey"

hey :: IO ()
hey = putStrLn "hello"
