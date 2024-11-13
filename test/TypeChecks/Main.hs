{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}

module Main where

import Test.Tasty            (TestTree, defaultMain)
import Test.Tasty.HUnit      (testCase, assertEqual)
import Test.ShouldNotTypecheck (shouldNotTypecheck)

import LUCk.Syntax
import LUCk.Types

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testCase "split" $ do
    shouldNotTypecheck $ sendWithoutWt
  where
    sendWithoutWt :: PortInList String String ach -> AsyncT ach NextRecv NextRecv ()
    sendWithoutWt ch = send ch "hey"
