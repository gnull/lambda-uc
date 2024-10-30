module Main where

import Test.Tasty            (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit      (testCase, assertEqual, (@?=))

import Control.XMonad
import qualified Control.XMonad.Do as M

import Control.Monad.Writer.Class
import Control.Monad.Writer
import Data.Functor.Identity

import Data.Type.Equality
import Data.Fin (Fin(..))
import Data.Nat (Nat(..))
import Data.Type.Nat

import LUCk.Syntax
import LUCk.Syntax.Async.Eval
import LUCk.Syntax.Async.Eval.Internal
import LUCk.Syntax.Async.SomeWT
import LUCk.Types

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "async execution tests"
  [ testCase "round trip 2 processes" $
      toIO (runExec $ twoSum 10 1) >>= (@?= 11)
  , testCase "round trip 3 processes" $
      toIO (runExec $ threeSum 100 10 1) >>= (@?= 111)
  , testCase "round trip 3 processes, monadic notation" $
      toIO (runExec $ runExecBuilder $ threeSumWriter 100 10 1) >>= (@?= 111)
  , testCase "guessing game" $
      writerTtoIO (fmap (<= 7) $ runExec $ runExecBuilder guessingExec) >>= (@?= True)
  , testCase "pingExecBuilder" $
      toIO (runExec $ pingExec') >>= (@?= "hey")
  ]

type Log = [String]

debugPrint x = tell [x]

twoSum :: Int -> Int -> Exec '[] PrAlgo (InitPresent Int)
twoSum x y =
  ExecLink Split0 Split0 $
  ExecFork getInitStatusCompD getKnownLenPrf
    (ExecProc getInitStatusIndexRetD $ sender x)
    (ExecProc getInitStatusIndexRetD $ receiver y)

threeSum :: Int -> Int -> Int -> Exec '[] PrAlgo (InitPresent Int)
threeSum x y z =
  ExecLink Split0 Split0 $
  ExecLink Split1 Split0 $
  ExecFork getInitStatusCompD getKnownLenPrf (ExecProc getInitStatusIndexRetD $ sender2 x) $
  ExecLink Split1 Split0 $
  ExecFork getInitStatusCompD getKnownLenPrf
    (ExecProc getInitStatusIndexRetD $ receiver2 y)
    (ExecProc getInitStatusIndexRetD $ receiver2 z)

threeSumWriter :: Int -> Int -> Int -> ExecBuilder PrAlgo ExecIndexInit (ExecIndexSome '[] (InitPresent Int)) ()
threeSumWriter x y z = M.do
  process $ receiver2 x
  execGuard @'[P Int Void, P Void Int]
  forkLeft $
    process $ receiver2 y
  execGuard @'[P Int Void, P Void Int, P Int Void, P Void Int]
  link Split1 Split0
  execGuard @'[P Int Void, P Void Int]
  forkLeft  $
    process $ sender2 z
  execGuard @'[P Int Void, P Void Int, P Int Void, P Void Int]
  link Split1 Split0
  execGuard @'[P Int Void, P Void Int]
  link Split0 Split0

sender :: Int -> AsyncT '[P Int Int] PrAlgo NextSend NextSend Int
sender x = M.do
  sendOne x
  recvOne

receiver :: Int -> AsyncT '[P Int Int] PrAlgo NextRecv NextRecv Void
receiver x = M.do
  m <- recvOne
  sendOne $ m + x
  receiver x

sender2 :: Int -> AsyncT '[P Int Void, P Void Int] PrAlgo NextSend NextSend Int
sender2 x = M.do
  send Here x
  recvAny >>=: \case
    SomeRxMess Here contra -> case contra of {}
    SomeRxMess (There Here) m -> xreturn m
    SomeRxMess (There2 contra) _ -> case contra of {}

receiver2 :: Int -> AsyncT '[P Int Void, P Void Int] PrAlgo NextRecv NextRecv Void
receiver2 x = M.do
  m <- recvAny >>=: \case
    SomeRxMess Here contra -> case contra of {}
    SomeRxMess (There Here) m -> xreturn m
    SomeRxMess (There2 contra) _ -> case contra of {}
  send Here $ m + x
  receiver2 x

-- |Showcases properties:
--
-- - Directly using rangeDist local computation in AsyncT monad, due to its
--   polymorphic signatures. One could as well use an explicit `lift` call to
--   make types less ambiguous for constraint resolver.
--
-- - Recursive action helper, with type system ensuring that recursion preserves
--   alternation of `send` and `recvAny`.
--
-- - Polymorphic monad
guessingChallenger :: (MonadRand m, MonadWriter Log m)
                   => AsyncT '[P Ordering Integer] m NextRecv NextRecv Void
guessingChallenger =  M.do
    secret <- rangeDist 0 100
    debugPrint $ "challenger picked secret " ++ show secret
    helper secret
  where
    helper :: MonadWriter Log m => Integer -> AsyncT '[P Ordering Integer] m NextRecv NextRecv Void
    helper secret = M.do
      guess <- recvOne
      let res = secret `compare` guess
      debugPrint $ "challenger response " ++ show res
      sendOne res
      helper secret

-- |Showcases:
--
-- - ensuring that player is deterministic
-- - using undefined to mark conditions that are not considered (assumed to never occur)
guessingPlayer :: MonadWriter Log m
               => AsyncT '[P Integer Ordering] m NextSend NextSend Integer
guessingPlayer = M.do
    n <- helper 0 100
    debugPrint $ "found result in " ++ show n ++ " attempts"
    xreturn n
  where
    helper :: MonadWriter Log m
           => Integer
           -> Integer
           -> AsyncT '[P Integer Ordering] m NextSend NextSend Integer
    helper f t
      | f >= t = undefined
      | f == t - 1 = xreturn 0
      | otherwise = M.do
          let mid = (f + t) `div` 2
          debugPrint $ "guessing  " ++ show mid
          sendOne mid
          v <- recvOne >>=: \case
            LT -> helper f mid
            EQ -> xreturn 0
            GT -> helper (mid + 1) t
          xreturn $ v + 1

guessingExec :: ExecBuilder (WriterT Log PrAlgo) ExecIndexInit (ExecIndexSome '[] (InitPresent Integer)) ()
guessingExec = M.do
  process $ guessingChallenger
  forkLeft $
    process guessingPlayer
  link Split0 Split0

-- |Sends String s to the given port, waits for the other side to repond with
test :: String -> AsyncT '[P String Int] m NextSend NextSend Int
test s = M.do
  send Here s
  recvAny >>=: \case
    SomeRxMess (There contra) _ -> case contra of
    SomeRxMess Here m -> xreturn m

-- |Demonstrates the use of @SomeWTM@. To express a computation that
-- dynamically chooses what state to leave the monad in, do the following:
--
-- 1. Wrap the whole thing in @SomeWTM@.
--
-- 2. Inside @SomeWTM@, wrap each branch where your WT state is fixed in
-- @decided@.
maybeSends :: PortInList Bool Bool l -> SomeWT ex l m NextRecv Bool
maybeSends port =
  ContFromAnyWT $ \cont -> M.do
  (SomeRxMess s msg) <- recvAny
  case testEquality port s of
    Just Refl -> M.do
      send port False
      cont msg
    Nothing -> cont False

useMaybeSends :: PortInList Bool Bool ach
              -> AsyncT ach m NextRecv NextSend (SomeRxMess ach)
useMaybeSends port = M.do
  -- Step #1: pass @maybeSends@ to dispatchSomeWT
  -- Step #2: pass it a continuation that starts from unknown WT state
  res <- dispatchSomeWT (maybeSends port) $ \b -> M.do
    -- _ -- in this context, the state of WT is unknown
    -- Step #3: match on the current WT and provide actions for every branch
    asyncGetIndex >>=: \case
      SNextSend -> xreturn $ SomeRxMess port $ b
      SNextRecv -> M.do
        recvAny
  -- _ -- in this context, the state of WT is fixed
  xreturn $ res


-- |Link the first port to itself.
--
-- This is not a basic combinator and is derived using `fork` and `link`.
linkSelf :: forall m x st rest. (Monad m, KnownInitStatus st) =>
   ExecBuilder m (ExecIndexSome (P x x : rest) st) (ExecIndexSome rest st) ()
linkSelf = M.do
    lemma >>=: \case
      Refl -> M.do
        forkRight $ process idProc
        link Split0 Split0
  where
    lemma :: ExecBuilder m (ExecIndexSome l st) (ExecIndexSome l st)
                           (InitStatusOr InitAbsent st :~: st)
    lemma = execInvariantM $ \case
      InitStatusIndexRetAbsent -> Refl
      InitStatusIndexRetPresent -> Refl

-- |Process that sends back everything it gets
idProc :: Monad m
       => AsyncT '[P x x] m NextRecv NextRecv Void
idProc = M.do
  recvOne >>=: sendOne
  idProc

-- |Merge two single-directional ports into one.
--
-- Any message that arrives on the merged ports is passed as is with no
-- marking to tell what port it came from.
mergeProc :: AsyncT '[P a Void, P Void a, P Void a] m NextRecv NextRecv Void
mergeProc = M.do
  () <- recvAny >>=: \case
    SomeRxMess Here contra -> case contra of {}
    SomeRxMess (There Here) x -> send Here x
    SomeRxMess (There2 Here) x -> send Here x
    SomeRxMess (There3 contra) _ -> case contra of {}
  mergeProc

pingServe :: String -> AsyncT '[P String ()] m NextRecv NextRecv Void
pingServe hello = M.do
  () <- recvOne
  sendOne hello
  pingServe hello

pingRequest :: AsyncT '[P () String] m NextSend NextSend String
pingRequest = M.do
  sendOne ()
  recvOne

pingExecBuilder :: ExecBuilder m ExecIndexInit (ExecIndexSome '[] (InitPresent String)) ()
pingExecBuilder = M.do
  process $ pingServe "hey"
  forkLeft $ M.do
    process pingRequest
  link SplitHere SplitHere

pingExecBuilder' :: ExecBuilder m ExecIndexInit (ExecIndexSome '[] (InitPresent String)) ()
pingExecBuilder' = M.do
  process $ pingServe "hey"
  execGuard @'[P String ()] @InitAbsent
  -- ^One unlinked port, no initial process
  forkLeft $ M.do
    process pingRequest
    execGuard @'[P () String]
    -- ^One channel present
  execGuard @_ @(InitPresent String)
  -- ^Initial process with String result present
  execGuard @'[P String (), P () String]
  -- ^Two unlinked ports
  link SplitHere SplitHere

pingExec' :: Exec '[] m (InitPresent String)
pingExec' = runExecBuilder pingExecBuilder
