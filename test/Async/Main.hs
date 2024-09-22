module Main where

import Test.Tasty            (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit      (testCase, assertEqual, (@?=))

import Control.XMonad
import qualified Control.XMonad.Do as M

import Data.Type.Equality ((:~:)(Refl))
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
      generalizeAlgo (runExec $ twoSum 10 1) >>= (@?= 11)
  , testCase "round trip 3 processes" $
      generalizeAlgo (runExec $ threeSum 100 10 1) >>= (@?= 111)
  , testCase "round trip 3 processes, monadic notation" $
      generalizeAlgo (runExec $ execWriterToExec $ threeSumWriter 100 10 1) >>= (@?= 111)
  , testCase "guessing game" $
      generalizeAlgo (fmap (<= 7) $ runExec $ execWriterToExec guessingExec) >>= (@?= True)
  ]

type PureM = Algo True False
type RandM = Algo True True

twoSum :: Int -> Int -> Exec '[] PureM NextSend Int
twoSum x y =
  ExecConn SplitHere $
  ExecFork getForkIndexComp
           (KnownLenS KnownLenZ)
           (ExecProc getSIndex getMayOnlyReturnAfterRecvPrf $ sender x)
           (ExecProc getSIndex getMayOnlyReturnAfterRecvPrf $ receiver y)

threeSum :: Int -> Int -> Int -> Exec '[] PureM NextSend Int
threeSum x y z =
  ExecConn Split0 $
  ExecConn Split1 $
  ExecFork getForkIndexComp getKnownLenPrf (ExecProc getSIndex getMayOnlyReturnAfterRecvPrf $ sender2 x) $
  ExecConn Split1 $
  ExecFork getForkIndexComp getKnownLenPrf
    (ExecProc getSIndex getMayOnlyReturnAfterRecvPrf $ receiver2 y)
    (ExecProc getSIndex getMayOnlyReturnAfterRecvPrf $ receiver2 z)

threeSumWriter :: Int -> Int -> Int -> ExecWriter PureM ExecIndexInit (ExecIndexSome '[] NextSend Int) ()
threeSumWriter x y z = M.do
  process $ receiver2 x
  -- guard @('[ '(Int, Void), '(Void, Int)])
  forkLeft $
    process $ receiver2 y
  -- guard @('[ '(Int, Void), '(Void, Int), '(Int, Void), '(Void, Int)])
  connect Split1 
  -- guard @('[ '(Int, Void), '(Void, Int)])
  forkLeft  $
    process $ sender2 z
  -- guard @('[ '(Int, Void), '(Void, Int), '(Int, Void), '(Void, Int)])
  connect Split1
  -- guard @('[ '(Int, Void), '(Void, Int)])
  connect Split0 

sender :: Int -> AsyncT '[ '(Int, Int)] PureM NextSend NextSend Int
sender x = M.do
  sendOne x
  recvOne

receiver :: Int -> AsyncT '[ '(Int, Int)] PureM NextRecv NextRecv Void
receiver x = M.do
  m <- recvOne
  sendOne $ m + x
  receiver x

sender2 :: Int -> AsyncT '[ '(Int, Void), '(Void, Int)] PureM NextSend NextSend Int
sender2 x = M.do
  send Here x
  recvAny >>=: \case
    SomeSndMessage Here contra -> case contra of {}
    SomeSndMessage (There Here) m -> xreturn m
    SomeSndMessage (There2 contra) _ -> case contra of {}

receiver2 :: Int -> AsyncT '[ '(Int, Void), '(Void, Int)] PureM NextRecv NextRecv Void
receiver2 x = M.do
  m <- recvAny >>=: \case
    SomeSndMessage Here contra -> case contra of {}
    SomeSndMessage (There Here) m -> xreturn m
    SomeSndMessage (There2 contra) _ -> case contra of {}
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
guessingChallenger :: (Rand m, Print m)
                   => AsyncT '[ '(Ordering, Integer)] m NextRecv NextRecv Void
guessingChallenger =  M.do
    secret <- rangeDist 0 100
    debugPrint $ "challenger picked secret " ++ show secret
    helper secret
  where
    helper :: Print m => Integer -> AsyncT '[ '(Ordering, Integer)] m NextRecv NextRecv Void
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
guessingPlayer :: Print m
               => AsyncT '[ '(Integer, Ordering)] m NextSend NextSend Integer
guessingPlayer = M.do
    n <- helper 0 100
    debugPrint $ "found result in " ++ show n ++ " attempts"
    xreturn n
  where
    helper :: Print m
           => Integer
           -> Integer
           -> AsyncT '[ '(Integer, Ordering)] m NextSend NextSend Integer
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

guessingExec :: ExecWriter RandM ExecIndexInit (ExecIndexSome '[] NextSend Integer) ()
guessingExec = M.do
  process $ guessingChallenger
  forkLeft $
    process guessingPlayer
  connect Split0

-- |Sends String s to the given channel, waits for the other side to repond with
test :: String -> AsyncExT e '[ '(String, Int)] m NextSend NextSend Int
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
maybeSends :: Chan Bool Bool l -> SomeWT ex l m NextRecv Bool
maybeSends chan =
  ContFromAnyWT $ \cont -> M.do
  (SomeSndMessage s msg) <- recvAny
  case testEquality chan s of
    Just Refl -> M.do
      send chan False
      cont msg
    Nothing -> cont False

useMaybeSends :: InList '(ExBadSender, NextSend) ex
              -> Chan Bool Bool ach
              -> AsyncExT ex ach m NextRecv NextSend Bool
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


-- |Connect the first channel to itself.
--
-- This is not a basic combinator and is derived using `fork` and `connect`.
connectSelf :: forall i a m x rest.
               (Monad m, KnownIndex i, MayOnlyReturnAfterRecv i a)
            => ExecWriter m (ExecIndexSome ('(x, x) : rest) i a) (ExecIndexSome rest i a) ()
connectSelf = case lemma (getMayOnlyReturnAfterRecvPrf @i @a) getSIndex of
    (Refl, Refl) -> M.do
      forkRight $ process idProc
      connect SplitHere
  where
    lemma :: forall i a.
             MayOnlyReturnAfterRecvD i a
          -> SIndex i
          -> (ChooseRet NextRecv i Void a :~: a, ForkIndexOr NextRecv i :~: i)
    lemma = \case
      MayOnlyReturnType -> \_ -> (Refl, Refl)
      MayOnlyReturnVoid -> \case
        SNextRecv -> (Refl, Refl)
        SNextSend -> (Refl, Refl)

-- |Process that sends back everything it gets
idProc :: Monad m
       => AsyncT '[ '(x, x)] m NextRecv NextRecv Void
idProc = M.do
  recvOne >>=: sendOne
  idProc

-- |Merge two single-directional channels into one.
--
-- Any message that arrives on the merged channels is passed as is with no
-- marking to tell what channel it came from.
mergeProc :: AsyncT '[ '(a, Void), '(Void, a), '(Void, a)] m NextRecv NextRecv Void
mergeProc = M.do
  () <- recvAny >>=: \case
    SomeSndMessage Here contra -> case contra of {}
    SomeSndMessage (There Here) x -> send Here x
    SomeSndMessage (There2 Here) x -> send Here x
    SomeSndMessage (There3 contra) _ -> case contra of {}
  mergeProc
