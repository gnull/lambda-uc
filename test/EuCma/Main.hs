module Main where

import Test.Tasty            (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit      (testCase, assertEqual, (@?=))

import LUCk.Syntax
import LUCk.Syntax.Sync
import LUCk.Types

import LUCk.Games.SignatureScheme

alwaysNoSch :: SpSignatureScheme () () Int Int
alwaysNoSch _ = SignatureScheme
  { sigKey = pure ((), ())
  , sigSign = \_ m -> pure m
  , sigVer = \_ _ _ -> False
  }

alwaysYesSch :: SpSignatureScheme () () Int Int
alwaysYesSch _ = SignatureScheme
  { sigKey = pure ((), ())
  , sigSign = \_ m -> pure m
  , sigVer = \_ _ _ -> True
  }

advGuess :: SpAdvAlgo () Int Int
advGuess _ () = do
  _ <- call Here 1
  _ <- call Here 2
  pure (3, 3)

advRepeats :: SpAdvAlgo () Int Int
advRepeats _ () = do
  _ <- call Here 1
  _ <- call Here 2
  pure (2, 2)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "dummy adversaries"
  [ testCase "adversary guessing: yes" $
      runIO (gameEuCma 0 alwaysYesSch advGuess) >>= (@?= True)
  , testCase "adversary guessing: no" $
      runIO (gameEuCma 0 alwaysNoSch advGuess) >>= (@?= False)
  , testCase "repeating adversary: no" $
      runIO (gameEuCma 0 alwaysYesSch advRepeats) >>= (@?= False)
  , testCase "repeating adversary: no" $
      runIO (gameEuCma 0 alwaysNoSch advRepeats) >>= (@?= False)
  ]
