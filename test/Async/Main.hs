module Main where

import Test.Tasty            (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit      (testCase, assertEqual, (@?=))

import Control.XMonad
import qualified Control.XMonad.Do as M

import Data.Type.Equality ((:~:)(Refl))

import UCHS.Monad
import UCHS.Monad.InterT.Eval.Async
import UCHS.Monad.InterT.SomeWT
import UCHS.Types

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "async execution tests"
  [ testCase "round trip 2 processes" $
      liftAlgo (runExec $ twoSum 10 1) >>= (@?= 11)
  , testCase "round trip 3 processes" $
      liftAlgo (runExec $ threeSum 100 10 1) >>= (@?= 111)
  ]

type M = Algo False False

twoSum :: Int -> Int -> Exec M '[] NextSend Int
twoSum x y =
  ExecConn SplitHere SplitHere $
  ExecFork (KnownLenS KnownLenZ) (ExecProc $ sender x) (ExecProc $ receiver y)

threeSum :: Int -> Int -> Int -> Exec M '[] NextSend Int
threeSum x y z =
  ExecConn Split0 Split0 $
  ExecConn Split1 Split1 $
  ExecFork getKnownLenPrf (ExecProc $ sender2 x) $
  ExecConn Split1 Split1 $
  ExecFork getKnownLenPrf
    (ExecProc $ receiver2 y)
    (ExecProc $ receiver2 z)

-- threeSum ::

sender :: Int -> AsyncT M '[ '(Int, Int)] NextSend NextSend Int
sender x = M.do
  sendOne x
  recvOne

receiver :: Int -> AsyncT M '[ '(Int, Int)] NextRecv NextRecv Void
receiver x = M.do
  m <- recvOne
  sendOne $ m + x
  receiver x

sender2 :: Int -> AsyncT M '[ '(Int, Void), '(Void, Int)] NextSend NextSend Int
sender2 x = M.do
  send Here x
  recvAny >>=: \case
    SomeSndMessage Here contra -> case contra of {}
    SomeSndMessage (There Here) m -> xreturn m
    SomeSndMessage (There2 contra) _ -> case contra of {}

receiver2 :: Int -> AsyncT M '[ '(Int, Void), '(Void, Int)] NextRecv NextRecv Void
receiver2 x = M.do
  m <- recvAny >>=: \case
    SomeSndMessage Here contra -> case contra of {}
    SomeSndMessage (There Here) m -> xreturn m
    SomeSndMessage (There2 contra) _ -> case contra of {}
  send Here $ m + x
  receiver2 x


-- |Sends String s to the given channel, waits for the other side to repond with
test :: String -> AsyncExT m e '[ '(String, Int)] NextSend NextSend Int
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
maybeSends :: Chan Bool Bool l -> SomeWT ('InterPars m e l '[]) NextRecv Bool
maybeSends chan = ContFromAnyWT $ \cont -> M.do
  (SomeSndMessage sender msg) <- recvAny
  case testEquality chan sender of
    Just Refl -> M.do
      send chan False
      cont msg
    Nothing -> cont False

useMaybeSends :: InList '(ExBadSender, NextSend) ex
              -> Chan Bool Bool ach
              -> AsyncExT m ex ach NextRecv NextSend Bool
useMaybeSends e chan = M.do
  -- Step #1: pass @maybeSends@ to dispatchSomeWT
  -- Step #2: pass it a continuation that starts from unknown WT state
  res <- dispatchSomeWT (maybeSends chan) $ \b -> M.do
    -- _ -- in this context, the state of WT is unknown
    -- Step #3: match on the current WT and provide actions for every branch
    getWT >>=: \case
      SNextSend -> xreturn b
      SNextRecv -> M.do
        m <- recv e chan
        xreturn m
  -- _ -- in this context, the state of WT is fixed
  xreturn $ not res
