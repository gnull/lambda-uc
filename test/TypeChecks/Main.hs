{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}

module Main where

import Test.Tasty            (TestTree, defaultMain)
import Test.Tasty.HUnit      (testCase, assertEqual)
import Test.ShouldNotTypecheck (shouldNotTypecheck)

import MachineMonad
import Types

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testCase "split" $ do
    shouldNotTypecheck $ sendWithoutWt
  where
    sendWithoutWt :: InList (String, String) l -> CryptoMonad m l False False ()
    sendWithoutWt ch = send ch "hey"
