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

import qualified LUCk.Syntax.Algo as L
import LUCk.Syntax.Algo (Rand(..), Print(..))
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

-- |Generalizes a concrete action in `@S.AsyncExT@ ex ports (@L.Algo@ pr ra)`,
-- to an `S.AsyncExT` that may potentially allow more operations (due to more
-- permissive parameters).
generalizeAsyncT :: ( IfThenElse pr (Print m) (Empty m)
                    , IfThenElse ra (Rand m) (Empty m)
                    )
                => S.AsyncT ports (L.Algo pr ra) bef aft a
                -> S.AsyncT ports m bef aft a
generalizeAsyncT (S.AsyncT (Pure v)) = xreturn v
generalizeAsyncT (S.AsyncT (Join v)) =
    case v of
      S.SendAction m r -> S.sendMess m >>: generalizeAsyncT (S.AsyncT r)
      S.RecvAction cont -> S.recvAny >>=: generalizeAsyncT . S.AsyncT . cont
      S.LiftAction (L.Algo m) cont -> case m of
        F.Pure r -> generalizeAsyncT $ S.AsyncT $ cont r
        F.Free (L.PrintAction s r) -> M.do
          debugPrint s
          r' <- generalizeAsyncT $ xlift $ L.Algo r
          generalizeAsyncT $ S.AsyncT $ cont r'
        F.Free (L.RandAction contInner) -> M.do
          x <- rand
          r' <- generalizeAsyncT $ xlift $ L.Algo $ contInner x
          generalizeAsyncT $ S.AsyncT $ cont r'
