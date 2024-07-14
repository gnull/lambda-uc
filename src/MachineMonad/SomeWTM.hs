module MachineMonad.SomeWTM where

import MachineMonad

import Control.XMonad
import qualified Control.XMonad.Do as M

-- data ContFromAnyWT pr ra l bef aft a b
--   = ContFromAnyWT ((a -> forall i. CryptoMonad pr ra l i aft b) -> CryptoMonad pr ra l bef aft b)
data ContFromAnyWT pr ra l bef aft a b
  -- = forall i. ContFromAnyWT (CryptoMonad pr ra l i aft a)
  = ContFromAnyWT ((forall i. a -> CryptoMonad pr ra l i aft b) -> CryptoMonad pr ra l bef aft b)

-- |Like @SomeWT@, but lets you do some monadic computations before you decide
-- what state to leave the monad in.
type SomeWT pr ra l bef a = forall aft b. ContFromAnyWT pr ra l bef aft a b

dispatchSomeWT :: ContFromAnyWT pr ra l bef aft a b
                -> (forall i. a -> CryptoMonad pr ra l i aft b)
                -> CryptoMonad pr ra l bef aft b
dispatchSomeWT (ContFromAnyWT x) = x
