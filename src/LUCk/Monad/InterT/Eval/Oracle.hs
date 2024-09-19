module LUCk.Monad.InterT.Eval.Oracle (
  -- * Execution with Oracle
  -- $eval
    runWithOracles
  , OracleCaller
  , OracleWrapper(..)
  , Oracle
  , OracleReq(..)
  , runWithOracles1
  , runWithOracles2
  ) where

-- import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad
import Data.Functor
import Data.Functor.Identity

import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad
import qualified Control.XMonad.Do as M

import LUCk.Types
import LUCk.Monad.Class
import LUCk.Monad.InterT

import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad (MonadPlus(..))
import qualified Control.Monad.Trans.Class as Trans

-- $eval
--
-- The following are definitions related to running an algorithm with an given
-- oracle. The `runWithOracles` executes an algorithm with an oracle, while
-- `OracleCaller` and `OracleWrapper` are convenient type synonyms
-- for the interactive algorithms that define the oracle caller and oracle
-- respectively.
--
-- The oracle is expected to terminate and produce the result `s` right after
-- receiving special request `OracleReqHalt`, but not before then. If the
-- oracle violates this condition, the `runWithOracles` fails with `mzero`. To
-- differentiate between service `OracleReqHalt` and the regular queries from
-- the algorithm, we wrap the latter in `OracleReq` type.

-- |An algorithm with no parent and with access to child oracles given by
-- `down`.
type OracleCaller m down = SyncT m down

-- |An algorithm serving oracle calls from parent, but not having access to
-- any oracles of its own.
type Oracle (m :: Type -> Type) (up :: (Type, Type)) =
  AsyncT m '[ '(Snd up, OracleReq (Fst up))] NextRecv NextSend

-- |Version of `Oracle` that's wrapped in newtype, convenient for use with `HList2`.
newtype OracleWrapper (m :: Type -> Type) (up :: (Type, Type)) (ret :: Type) =
  OracleWrapper
    { runOracleWrapper
      :: Oracle m up ret
    }

data OracleReq a = OracleReqHalt | OracleReq a

-- |Given main algorithm `top` and a list of oracle algorithms `bot`,
-- `runWithOracles top bot` will run them together (`top` querying any oracle
-- the oracles in `bot`) and return their results.
--
-- The `top` returns its result directly when terminating, then a special
-- `OracleReqHalt` message is sent to all of `bot` to ask them to terminate and
-- return their results.
--
-- We throw a `mzero` error in case an oracle does not follow the termination
-- condition: terminates before receiving `OracleReqHalt` or tries to respond
-- to `OracleReqHalt` instead of terminating.
--
-- Note that `runWithOracles` passes all the messages between the running
-- interactive algorithms, therefore its result is a non-interactive algorithm.
runWithOracles :: forall m (down :: [(Type, Type)]) (rets :: [Type]) a.
               (Monad m, SameLength down rets)
               => OracleCaller m down a
               -- ^The oracle caller algorithm
               -> HList2 (OracleWrapper m) down rets
               -- ^The implementations of oracles available to caller
               -> MaybeT m (a, HList Identity rets)
               -- ^The outputs of caller and oracle. Fails with `mzero` if
               -- the oracle terminates before time or doesn't terminate when
               -- requested
runWithOracles = \top bot -> Trans.lift (runTillSend top) >>= \case
    SrSend (SomeFstMessage contra _) _ -> case contra of {}
    SrHalt r -> do
      s <- haltAll bot
      pure (r, s)
    SrCall i m cont -> do
      (bot', r) <- forIthFst i bot $ oracleCall m
      runWithOracles (cont r) bot'
  where
    oracleCall :: x
               -> OracleWrapper m '(x, y) s
               -> MaybeT m (OracleWrapper m '(x, y) s, y)
    oracleCall m (OracleWrapper bot) = Trans.lift (runTillRecv bot) >>= \case
      RrCall contra _ _ -> case contra of {}
      RrRecv cont -> Trans.lift (runTillSend $ cont $ SomeSndMessage Here (OracleReq m)) >>= \case
        SrCall contra _ _ -> case contra of {}
        SrHalt _ -> mzero
        SrSend r bot' -> case r of
            SomeFstMessage Here r' -> pure (OracleWrapper bot', r')
            SomeFstMessage (There contra) _ -> case contra of {}
          
    halt :: OracleWrapper m up x
         -> MaybeT m x
    halt (OracleWrapper bot) = Trans.lift (runTillRecv bot) >>= \case
      RrCall contra _ _ -> case contra of {}
      RrRecv cont -> Trans.lift (runTillSend $ cont $ SomeSndMessage Here OracleReqHalt) >>= \case
        SrCall contra _ _ -> case contra of {}
        SrHalt s -> pure s
        SrSend _ _ -> mzero

    haltAll :: forall (down' :: [(Type, Type)]) (rets' :: [Type]).
               HList2 (OracleWrapper m) down' rets'
            -> MaybeT m (HList Identity rets')
    haltAll = \case
      HNil2 -> pure HNil
      HCons2 x xs -> do
        x' <- halt x
        xs' <- haltAll xs
        pure $ HCons (Identity x') xs'

-- |Version of `runWithOracles` that accepts only one oracle
runWithOracles1 :: Monad m
                => OracleCaller m '[ '(x, y) ] a
                -> OracleWrapper m '(x, y) b
                -> MaybeT m (a, b)
runWithOracles1 top bot = runWithOracles top (HList2Match1 bot) <&>
  \(a, HListMatch1 (Identity b)) -> (a, b)

-- |Version of `runWithOracles` that accepts two oracles
runWithOracles2 :: Monad m
                => OracleCaller m '[ '(x, y), '(x', y') ] a
                -> OracleWrapper m '(x, y) b
                -> OracleWrapper m '(x', y') b'
                -> MaybeT m (a, b, b')
runWithOracles2 top bot bot' = runWithOracles top (HList2Match2 bot bot') <&>
  \(a, HListMatch2 (Identity b) (Identity b')) -> (a, b, b')
