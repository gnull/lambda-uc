module Main where

import Test.Tasty            (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit      (testCase, assertEqual, (@?=))

import Control.XMonad
import qualified Control.XMonad.Do as M

import UCHS.Monad.SyncAlgo
import UCHS.Monad.Algo
import UCHS.Monad.Class
import UCHS.Monad.Extra
import UCHS.Types

import UCHS.Games.SignatureScheme

alwaysNoSch :: SignatureScheme () () Int Int
alwaysNoSch = SignatureScheme
  { sigKey = pure ((), ())
  , sigSign = \_ m -> pure m
  , sigVer = \_ _ _ -> pure False
  }

alwaysYesSch :: SignatureScheme () () Int Int
alwaysYesSch = SignatureScheme
  { sigKey = pure ((), ())
  , sigSign = \_ m -> pure m
  , sigVer = \_ _ _ -> pure True
  }

advGuess :: AdvAlgo () Int Int
advGuess () = M.do
  _ <- call Here 1
  _ <- call Here 2
  pure (3, 3)

advRepeats :: AdvAlgo () Int Int
advRepeats () = M.do
  _ <- call Here 1
  _ <- call Here 2
  pure (2, 2)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "dummy adversaries"
  [ testCase "adversary guessing: yes" $
      liftAlgo (gameEuCma alwaysYesSch advGuess) >>= (@?= True)
  , testCase "adversary guessing: no" $
      liftAlgo (gameEuCma alwaysNoSch advGuess) >>= (@?= False)
  , testCase "repeating adversary: no" $
      liftAlgo (gameEuCma alwaysYesSch advRepeats) >>= (@?= False)
  , testCase "repeating adversary: no" $
      liftAlgo (gameEuCma alwaysNoSch advRepeats) >>= (@?= False)
  ]
