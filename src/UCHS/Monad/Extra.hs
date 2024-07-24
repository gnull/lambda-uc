-- {-# LANGUAGE QuantifiedConstraints #-}

-- module UCHS.Monad.Extra
--   (
--   -- * Relaxing monad type
--   --
--   -- $intro
--     liftAlgo
--   , liftSyncAlgo
--   , liftAsyncAlgo
--   )
--   where

-- import Control.XFreer.Join
-- import qualified Control.Monad.Free as F
-- import Control.XMonad

-- import UCHS.Types
-- import UCHS.Monad.Class

-- import qualified UCHS.Monad.Algo as L
-- import qualified UCHS.Monad.SyncAlgo as S
-- import qualified UCHS.Monad.AsyncAlgo as A

-- -- $intro
-- --
-- -- The following functions convert a concrete (local or interactive) monad
-- -- syntax into any monad that implements the same operations. The main use
-- -- of these is casting any monad to a more powerful (less restricting)
-- -- context.
-- --
-- -- Say, if you want to run probabilistic computation
-- -- `x :: Algo False True Data.Void.Void a` in a context
-- -- `L.Algo True True Data.Void.Void a` that additionally permits printing or
-- -- interactive probabilistic context `S.SyncAlgo ('S.SyncPars False True ex chans) b b a`,
-- -- you can use `liftAlgo`.
-- --
-- -- These functions additionally demonstrate what combination of typeclasses
-- -- each of `L.Algo`, `S.SyncAlgo` and `A.AsyncAlgo` is equivalent to.
-- -- Conversion in the other direction (from polymorphic monad to concrete
-- -- syntax) is done automatically.

-- liftAlgo :: ( IfThenElse pr Print Empty m
--             , IfThenElse ra Rand Empty m
--             , Monad m
--             -- , Throw m ex
--             )
--            => L.Algo pr ra a
--            -> m a
-- liftAlgo (L.Algo (F.Pure v)) = pure v
-- liftAlgo (L.Algo (F.Free v)) =
--   case v of
--     L.PrintAction s r -> debugPrint s >> (liftAlgo $ L.Algo r)
--     L.RandAction cont -> rand >>= (\b -> liftAlgo $ L.Algo $ cont b)

-- liftSyncAlgo :: ( IfThenElse pr (forall b. Print (m b b)) (forall b. Empty (m b b))
--                 , IfThenElse ra (forall b. Rand (m b b)) (forall b. Empty (m b b))
--                 , (forall b. Monad (m b b))
--                 , XThrow m ex
--                 , SyncUp m up
--                 , SyncDown m down
--                 )
--                => S.SyncAlgo ('S.SyncPars (L.Algo pr ra) ex (Just '(up, down))) bef aft a
--                -> m bef aft a
-- liftSyncAlgo (S.SyncAlgo (Pure v)) = xreturn v
-- liftSyncAlgo (S.SyncAlgo (Join v)) =
--   case v of
--     S.YieldAction m r -> yield m >>: liftSyncAlgo (S.SyncAlgo r)
--     S.AcceptAction cont -> accept >>=: liftSyncAlgo . S.SyncAlgo . cont
--     S.CallAction i m cont -> call i m >>=: liftSyncAlgo . S.SyncAlgo . cont
--     S.GetWTAction cont -> getWT >>=: liftSyncAlgo . S.SyncAlgo . cont
--     S.ThrowAction i e -> xthrow i e
--     S.SyncLiftAction m cont -> liftAlgo m >>=: liftSyncAlgo . S.SyncAlgo . cont

--     -- S.lift m >>=: liftSyncAlgo . S.SyncAlgo . cont

-- liftAsyncAlgo :: ( IfThenElse pr (forall b. Print (m b b)) (forall b. Empty (m b b))
--                 , IfThenElse ra (forall b. Rand (m b b)) (forall b. Empty (m b b))
--                 , XThrow m ex
--                 , Async m chans
--                 )
--                => A.AsyncAlgo ('A.AsyncPars (L.Algo pr ra) ex chans) bef aft a
--                -> m bef aft a
-- liftAsyncAlgo (A.AsyncAlgo (Pure v)) = xreturn v
-- liftAsyncAlgo (A.AsyncAlgo (Join v)) =
--   case v of
--     A.RecvAction cont -> recvAny >>=: liftAsyncAlgo . A.AsyncAlgo . cont
--     A.SendAction m r -> sendMess m >>: liftAsyncAlgo (A.AsyncAlgo r)
--     A.GetWTAction cont -> getWT >>=: liftAsyncAlgo . A.AsyncAlgo . cont
--     A.ThrowAction i e -> xthrow i e
