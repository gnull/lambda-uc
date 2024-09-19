{-# LANGUAGE QuantifiedConstraints #-}

module LUCk.Monad.Extra
  (
  -- * Relaxing monad type
  --
  -- $intro
    liftAlgo
  , liftInterT
  -- , liftAsyncAlgo
  )
  where

import Control.XFreer.Join
import qualified Control.Monad.Free as F
import Control.XMonad

import LUCk.Types
import LUCk.Monad.Class

import qualified LUCk.Monad.Algo as L
import qualified LUCk.Monad.InterT as S

import qualified Control.XMonad.Do as M

-- $intro
--
-- The following functions convert a concrete (local or interactive) monad
-- syntax into any monad that implements the same operations. The main use
-- of these is casting any monad to a more powerful (less restricting)
-- context. Below are a few ways you may want to specialize this function.
--
-- @
-- -- Moving to less restricting version of `L.Algo`
-- `liftAlgo` :: `L.Algo` True False a -> `L.Algo` True True a
--
-- -- Moving to an interactive monad
-- `liftAlgo` :: `L.Algo` pr ra a -> `S.InterT` ('S.InterPars (`L.Algo` pr ra) ex up down) b b a
--
-- -- Moving to IO to actually interpret an `L.Algo`
-- `liftAlgo` :: `L.Algo` pr ra a -> `IO` a
-- @
--
--
-- These functions additionally demonstrate what combination of typeclasses
-- each of `L.Algo`, `S.InterT` and `A.AsyncAlgo` is equivalent to.
-- Conversion in the other direction (from polymorphic monad to concrete
-- syntax) is done automatically.

liftAlgo :: ( IfThenElse pr Print Empty m
            , IfThenElse ra Rand Empty m
            , Monad m
            -- , Throw m ex
            )
           => L.Algo pr ra a
           -> m a
liftAlgo (L.Algo (F.Pure v)) = pure v
liftAlgo (L.Algo (F.Free v)) =
  case v of
    L.PrintAction s r -> debugPrint s >> (liftAlgo $ L.Algo r)
    L.RandAction cont -> rand >>= (\b -> liftAlgo $ L.Algo $ cont b)

liftInterT :: ( IfThenElse pr (forall b. Print (m b b)) (forall b. Empty (m b b))
                , IfThenElse ra (forall b. Rand (m b b)) (forall b. Empty (m b b))
                , (forall b. Monad (m b b))
                , XThrow m ex
                , Async m up
                , Sync m down
                )
               => (SBool pr, SBool ra)
               -- ^An argument that helps GHC evaluate constraints
               -> S.InterT ('S.InterPars (L.Algo pr ra) ex up down) bef aft a
               -> m bef aft a
liftInterT _ (S.InterT (Pure v)) = xreturn v
liftInterT h (S.InterT (Join v)) =
    case v of
      S.SendAction m r -> sendMess m >>: liftInterT h (S.InterT r)
      S.RecvAction cont -> recvAny >>=: liftInterT h . S.InterT . cont
      S.CallAction i m cont -> call i m >>=: liftInterT h . S.InterT . cont
      S.ThrowAction i e -> xthrow i e
      S.LiftAction (L.Algo m) cont -> case m of
        F.Pure r -> liftInterT h $ S.InterT $ cont r
        F.Free (L.PrintAction s r) -> M.do
          debugPrint s
          r' <- liftInterT h $ S.lift $ L.Algo r
          liftInterT h $ S.InterT $ cont r'
        F.Free (L.RandAction contInner) -> M.do
          x <- rand
          r' <- liftInterT h $ S.lift $ L.Algo $ contInner x
          liftInterT h $ S.InterT $ cont r'
