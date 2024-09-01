module Main where

import Test.Tasty            (TestTree, defaultMain)
import Test.Tasty.HUnit      (testCase, assertEqual)

import Control.XMonad
import qualified Control.XMonad.Do as M

import Data.Type.Equality ((:~:)(Refl))

import UCHS.Monad
import UCHS.Monad.InterT.SomeWT
import UCHS.Types

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testCase "none" $ pure ()

-- |Sends String s to the given channel, waits for the other side to repond with
test :: String -> InterT ('InterPars (Algo pr ra) e '[ '(String, Int)] '[]) (Just True) (Just True) Int
test s = M.do
  send Here s
  recvAny >>=: \case
    SomeSndMessage (There contra) _ -> case contra of
    SomeSndMessage Here m -> xreturn m

-- |Demonstrates the use of @SomeWTM@. To express a computation that
-- dynamically chooses what state to leave the monad in, do the following:
--
-- 1. Wrap the whole thing in @SomeWTM@.
--
-- 2. Inside @SomeWTM@, wrap each branch where your WT state is fixed in
-- @decided@.
maybeSends :: Chan Bool Bool l -> SomeWT ('InterPars (Algo pr ra) e l '[]) (Just False) Bool
maybeSends chan = ContFromAnyWT $ \cont -> M.do
  (SomeSndMessage sender msg) <- recvAny
  case testEquality chan sender of
    Just Refl -> M.do
      send chan False
      cont getIndexReachablePrf msg
    Nothing -> cont getIndexReachablePrf False

useMaybeSends :: Chan Bool Bool l
              -> InterT ('InterPars (Algo pr ra) '[ '(ExBadSender, Just True) ] l '[]) (Just False) (Just True) Bool
useMaybeSends chan = M.do
  -- Step #1: pass @maybeSends@ to dispatchSomeWT
  -- Step #2: pass it a continuation that starts from unknown WT state
  res <- dispatchSomeWT (maybeSends chan) $ \prf b -> M.do
    -- _ -- in this context, the state of WT is unknown
    -- Step #3: match on the current WT and provide actions for every branch
    getWT >>=: \case
      SJustTrue -> xreturn b
      SJustFalse -> M.do
        m <- recv chan
        xreturn m
      SNothing -> case prf of {}
  -- _ -- in this context, the state of WT is fixed
  xreturn $ not res
