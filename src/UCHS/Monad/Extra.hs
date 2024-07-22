module UCHS.Monad.Extra
  (
  -- * Abstracting monad type
  -- The following functions convert a concrete (local or interactive) monad
  -- syntax into any monad that implements the same operations. The main use of
  -- these is to demonstrate what combination of typeclasses each of `L.Algo`,
  -- `S.SyncAlgo` and `A.AsyncAlgo` is equivalent to.
  --
  -- Conversion in the other direction (from polymorphic monad to concrete
  -- syntax) is done automatically.
    liftAlgo
  , liftSyncAlgo
  , liftAsyncAlgo
  )
  where

import Control.XFreer.Join
import Control.XMonad

import UCHS.Types
import UCHS.Monad.Class

import qualified UCHS.Monad.Algo as L
import qualified UCHS.Monad.SyncAlgo as S
import qualified UCHS.Monad.AsyncAlgo as A

liftAlgo :: ( IfThenElse pr Print Empty m
            , IfThenElse ra Rand Empty m
            , Throw m ex
            )
           => L.Algo pr ra ex a
           -> m a
liftAlgo (L.Algo (S.SyncAlgo (Pure v))) = pure v
liftAlgo (L.Algo (S.SyncAlgo (Join v))) =
  case v of
    S.PrintAction s r -> debugPrint s >> (liftAlgo $ L.Algo $ S.SyncAlgo r)
    S.RandAction cont -> rand >>= (\b -> liftAlgo $ L.Algo $ S.SyncAlgo $ cont b)
    S.ThrowAction Here e -> throw e
    S.ThrowAction (There contra) _ -> case contra of {}

liftSyncAlgo :: ( IfThenElse pr (forall b. Print (m b b)) (forall b. Empty (m b b))
                , IfThenElse ra (forall b. Rand (m b b)) (forall b. Empty (m b b))
                , XThrow m ex
                , SyncUp m up
                , SyncDown m down
                )
               => S.SyncAlgo ('S.SyncPars pr ra ex (Just '(up, down))) bef aft a
               -> m bef aft a
liftSyncAlgo (S.SyncAlgo (Pure v)) = xreturn v
liftSyncAlgo (S.SyncAlgo (Join v)) =
  case v of
    S.YieldAction m r -> yield m >>: liftSyncAlgo (S.SyncAlgo r)
    S.AcceptAction cont -> accept >>=: liftSyncAlgo . S.SyncAlgo . cont
    S.CallAction i m cont -> call i m >>=: liftSyncAlgo . S.SyncAlgo . cont
    S.GetWTAction cont -> getWT >>=: liftSyncAlgo . S.SyncAlgo . cont
    S.PrintAction s r -> debugPrint s >>: liftSyncAlgo (S.SyncAlgo r)
    S.RandAction cont -> rand >>=: liftSyncAlgo . S.SyncAlgo . cont
    S.ThrowAction i e -> xthrow i e

liftAsyncAlgo :: ( IfThenElse pr (forall b. Print (m b b)) (forall b. Empty (m b b))
                , IfThenElse ra (forall b. Rand (m b b)) (forall b. Empty (m b b))
                , XThrow m ex
                , Async m chans
                )
               => A.AsyncAlgo ('A.AsyncPars pr ra ex chans) bef aft a
               -> m bef aft a
liftAsyncAlgo (A.AsyncAlgo (Pure v)) = xreturn v
liftAsyncAlgo (A.AsyncAlgo (Join v)) =
  case v of
    A.RecvAction cont -> recvAny >>=: liftAsyncAlgo . A.AsyncAlgo . cont
    A.SendAction m r -> sendMess m >>: liftAsyncAlgo (A.AsyncAlgo r)
    A.GetWTAction cont -> getWT >>=: liftAsyncAlgo . A.AsyncAlgo . cont
    A.PrintAction s r -> debugPrint s >>: liftAsyncAlgo (A.AsyncAlgo r)
    A.RandAction cont -> rand >>=: liftAsyncAlgo . A.AsyncAlgo . cont
    A.ThrowAction i e -> xthrow i e
