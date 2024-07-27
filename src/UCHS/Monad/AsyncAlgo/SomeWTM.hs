module UCHS.Monad.AsyncAlgo.SomeWTM where

import UCHS.Types
import UCHS.Monad.SyncAlgo

-- import Control.XMonad
-- import qualified Control.XMonad.Do as M

-- data ContFromAnyWT st bef aft a b
--   = ContFromAnyWT ((a -> forall i. SyncAlgo pr ra l i aft b) -> SyncAlgo pr ra l bef aft b)
data ContFromAnyWT st bef aft a b
  -- = forall i. ContFromAnyWT (SyncAlgo pr ra l i aft a)
  = ContFromAnyWT ((forall i. KnownBool i => a -> SyncAlgo st i aft b) -> SyncAlgo st bef aft b)

-- |Like @SomeWT@, but lets you do some monadic computations before you decide
-- what state to leave the monad in.
type SomeWT st bef a = forall aft b. ContFromAnyWT st bef aft a b

dispatchSomeWT :: ContFromAnyWT st bef aft a b
                -> (forall i. KnownBool i => a -> SyncAlgo st i aft b)
                -> SyncAlgo st bef aft b
dispatchSomeWT (ContFromAnyWT x) = x
