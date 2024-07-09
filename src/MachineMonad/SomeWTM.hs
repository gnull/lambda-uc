module MachineMonad.SomeWTM where

import MachineMonad

import Control.XMonad
import qualified Control.XMonad.Do as M

-- |Allows you to express computations that may leave write token in either of
-- the two states. But the decision on which state to leave the monad in must
-- not be based on side-effects.
data SomeWT m l bef x = forall aft. SomeWT (CryptoMonad m l bef aft x)

-- |Like @SomeWT@, but lets you do some monadic computations before you decide
-- what state to leave the monad in.
data SomeWTM m l bef x = forall i. SomeWTM (CryptoMonad m l bef i (SomeWT m l i x))

-- |Make a decision inside @SomeWTM@ computation.
decided :: CryptoMonad m l i aft a -> CryptoMonad m l i i (SomeWT m l i a)
decided = xreturn . SomeWT

-- |Consume a @SomeWTM@ computation.
dispatchSomeWTM :: SomeWTM m l bef x -> (forall i. x -> CryptoMonad m l i aft a) -> CryptoMonad m l bef aft a
dispatchSomeWTM (SomeWTM w) cont = M.do
  (SomeWT x) <- w
  x >>=: cont
