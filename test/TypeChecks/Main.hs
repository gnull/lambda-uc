{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}

module Main where

import Test.Tasty            (TestTree, defaultMain)
import Test.Tasty.HUnit      (testCase, assertEqual)
import Test.ShouldNotTypecheck (shouldNotTypecheck)

import Control.Monad.UCHS.Async
import Types

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testCase "split" $ do
    shouldNotTypecheck $ sendWithoutWt
  where
    sendWithoutWt :: Chan String String l -> AsyncAlgo ('AsyncPars pr ra e l) False False ()
    sendWithoutWt ch = send ch "hey"
