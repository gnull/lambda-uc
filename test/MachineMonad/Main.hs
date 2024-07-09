module Main where

import Test.Tasty            (TestTree, defaultMain)
import Test.Tasty.HUnit      (testCase, assertEqual)

import Control.XMonad
import qualified Control.XMonad.Do as M

import MachineMonad
import MachineMonad.SomeWTM
import HeterogenousList

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testCase "none" $ pure ()

-- |Sends String s to the given channel, waits for the other side to repond with
test :: String -> InList (String, Int) l -> CryptoMonad m l True True Int
test s chan = M.do
  send chan s
  recv chan

-- |Demonstrates the use of @SomeWTM@. To express a computation that
-- dynamically chooses what state to leave the monad in, do the following:
--
-- 1. Wrap the whole thing in @SomeWTM@.
--
-- 2. Inside @SomeWTM@, wrap each branch where your WT state is fixed in
-- @decided@.
maybeSends :: InList (Bool, Bool) l -> SomeWTM m l True Bool
maybeSends chan = SomeWTM $ M.do
  yield chan
  b <- recv chan
  -- yield chan
  case b of
    True -> decided $ M.do
      yield chan
      xreturn b
    False -> decided $ xreturn b


useMaybeSends :: InList (Bool, Bool) l -> CryptoMonad m l True True Bool
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

