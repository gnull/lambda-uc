{-# LANGUAGE QuantifiedConstraints #-}

module LUCk.Syntax.Extra
  (
  -- * Relaxing monad type
  --
  -- $intro
    generalizeAlgo
  , generalizeAsyncT
  -- , liftAsyncAlgo
  )
  where

import Control.XFreer.Join
import qualified Control.Monad.Free as F
import Control.XMonad

import LUCk.Types
import LUCk.Syntax.Class

import qualified LUCk.Syntax.Algo as L
import qualified LUCk.Syntax.Async as S

import qualified Control.XMonad.Do as M
import Control.XMonad.Trans

-- $intro
--
-- The following functions convert a concrete (local or interactive) monad
-- syntax into any monad that implements the same operations. The main use
-- of these is casting any monad to a more powerful (less restricting)
-- context. Below are a few ways you may want to specialize this function.
--
-- @
-- -- Moving to less restricting version of `L.Algo`
-- `generalizeAlgo` :: `L.Algo` True False a -> `L.Algo` True True a
--
-- -- Moving to an interactive monad
-- `generalizeAlgo` :: `L.Algo` pr ra a -> `S.AsyncExT` ('S.InterPars (`L.Algo` pr ra) ex up down) b b a
--
-- -- Moving to IO to actually interpret an `L.Algo`
-- `generalizeAlgo` :: `L.Algo` pr ra a -> `IO` a
-- @
--
--
-- These functions additionally demonstrate what combination of typeclasses
-- each of `L.Algo` and `S.AsyncExT` are equivalent to.  Conversion in the
-- other direction (from polymorphic monad to concrete syntax) is done
-- automatically.

generalizeAlgo :: ( IfThenElse pr Print Empty m
            , IfThenElse ra Rand Empty m
            , Monad m
            -- , Throw m ex
            )
           => L.Algo pr ra a
           -> m a
generalizeAlgo (L.Algo (F.Pure v)) = pure v
generalizeAlgo (L.Algo (F.Free v)) =
  case v of
    L.PrintAction s r -> debugPrint s >> (generalizeAlgo $ L.Algo r)
    L.RandAction cont -> rand >>= (\b -> generalizeAlgo $ L.Algo $ cont b)

-- |Generalizes a concrete action in `@S.AsyncExT@ ex up (@L.Algo@ pr ra)`, to
-- any monad that implements the same typeclasses.
--
-- From practical perspective, this lets you interpret the `S.AsyncT` syntax
-- in something like `IO`. Or you can use this to move actions to a less
-- restrictive monad (`S.AsyncT` with more permissive parameters).
--
-- From abstract perspective, the signature of this function fully
-- characterizes the actions that `S.AsyncT` may do with the given parameters.
generalizeAsyncT :: ( IfThenElse pr (forall b. Print (m b b)) (forall b. Empty (m b b))
                , IfThenElse ra (forall b. Rand (m b b)) (forall b. Empty (m b b))
                , (forall b. Monad (m b b))
                , XThrow m ex
                , Async m up
                )
               => (SBool pr, SBool ra)
               -- ^An argument that helps GHC evaluate constraints
               -> S.AsyncExT ex up (L.Algo pr ra) bef aft a
               -> m bef aft a
generalizeAsyncT _ (S.AsyncExT (Pure v)) = xreturn v
generalizeAsyncT h (S.AsyncExT (Join v)) =
    case v of
      S.SendAction m r -> sendMess m >>: generalizeAsyncT h (S.AsyncExT r)
      S.RecvAction cont -> recvAny >>=: generalizeAsyncT h . S.AsyncExT . cont
      S.ThrowAction i e -> xthrow i e
      S.LiftAction (L.Algo m) cont -> case m of
        F.Pure r -> generalizeAsyncT h $ S.AsyncExT $ cont r
        F.Free (L.PrintAction s r) -> M.do
          debugPrint s
          r' <- generalizeAsyncT h $ xlift $ L.Algo r
          generalizeAsyncT h $ S.AsyncExT $ cont r'
        F.Free (L.RandAction contInner) -> M.do
          x <- rand
          r' <- generalizeAsyncT h $ xlift $ L.Algo $ contInner x
          generalizeAsyncT h $ S.AsyncExT $ cont r'
