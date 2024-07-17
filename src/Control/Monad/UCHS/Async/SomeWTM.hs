module Control.Monad.UCHS.Async.SomeWTM where

import Control.Monad.UCHS.Async

import Control.XMonad
import qualified Control.XMonad.Do as M

-- data ContFromAnyWT st bef aft a b
--   = ContFromAnyWT ((a -> forall i. AsyncAlgo pr ra l i aft b) -> AsyncAlgo pr ra l bef aft b)
data ContFromAnyWT st bef aft a b
  -- = forall i. ContFromAnyWT (AsyncAlgo pr ra l i aft a)
  = ContFromAnyWT ((forall i. a -> AsyncAlgo st i aft b) -> AsyncAlgo st bef aft b)

-- |Like @SomeWT@, but lets you do some monadic computations before you decide
-- what state to leave the monad in.
type SomeWT st bef a = forall aft b. ContFromAnyWT st bef aft a b

dispatchSomeWT :: ContFromAnyWT st bef aft a b
                -> (forall i. a -> AsyncAlgo st i aft b)
                -> AsyncAlgo st bef aft b
dispatchSomeWT (ContFromAnyWT x) = x
