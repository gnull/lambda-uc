module MachineMonad.SomeWTM where

import MachineMonad

import Control.XMonad
import qualified Control.XMonad.Do as M

-- |Allows you to express computations that may leave write token in either of
-- the two states. But the decision on which state to leave the monad in must
-- not be based on side-effects.
data SomeWT pr ra l bef x = forall aft. SomeWT (CryptoMonad pr ra l bef aft x)

-- |Like @SomeWT@, but lets you do some monadic computations before you decide
-- what state to leave the monad in.
data SomeWTM pr ra l bef x = forall i. SomeWTM (CryptoMonad pr ra l bef i (SomeWT pr ra l i x))

-- |Make a decision inside @SomeWTM@ computation.
decided :: CryptoMonad pr ra l i aft a -> CryptoMonad pr ra l i i (SomeWT pr ra l i a)
decided = xreturn . SomeWT

-- |Consume a @SomeWTM@ computation.
dispatchSomeWTM :: SomeWTM pr ra l bef x -> (forall i. x -> CryptoMonad pr ra l i aft a) -> CryptoMonad pr ra l bef aft a
dispatchSomeWTM (SomeWTM w) cont = M.do
  (SomeWT x) <- w
  x >>=: cont
