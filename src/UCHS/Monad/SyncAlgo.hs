{-# LANGUAGE DerivingVia #-}

module UCHS.Monad.SyncAlgo (
  -- * Interactive Algorithm Monad
  -- $monad
    SyncAlgo(..)
  , SyncPars(..)
  , xfreeSync
  , lift
  -- , catch
  -- * Syntax
  -- $actions
  , SyncActions(..)
  -- * Evaluation
  -- $eval
  , runTillYield
  , YieldRes(..)
  , deliver
  , DeliverRes(..)
  , runWithOracle
  , OracleCallerWrapper
  , OracleWrapper
  , OracleReq(..)
) where

-- import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad
import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad
-- import qualified Control.XMonad.Do as M

-- import Data.Type.Equality ((:~:)(Refl))

import UCHS.Types
import UCHS.Monad.Class

import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad (MonadPlus(..))
import qualified Control.Monad.Trans.Class as Trans

-- |The parameters of @SyncAlgo@ that do not change throughout the execution
data SyncPars = SyncPars
  { stInner :: Type -> Type
  -- ^The inner monad where the local computations happen
  , stEx :: [(Type, Bool)]
  -- ^Type of exceptions we throw and contexts (use @[]@ to disable exceptions)
  , stUp :: (Type, Type)
  -- ^The upstream interface to our parent
  , stDown :: [(Type, Type)]
  -- ^The downstream interfaces to children
  }

-- $actions
--
-- Actions are given in Free monad syntax.


-- |Defines actions for:
--
-- - @bef@ and @aft@ are the states before and after the given action.
data SyncActions (st :: SyncPars) (bef :: Bool) (aft :: Bool) a where
  -- |Accept an oracle call from parent
  AcceptAction :: (y -> a) -> SyncActions ('SyncPars m ex '(x, y) down) False True a
  -- |Yield the result of an oracle call from the parent
  YieldAction :: x -> a -> SyncActions ('SyncPars m ex '(x, y) down) True False a
  -- |Perform a call to a child, immediately getting the result
  CallAction :: Chan x y down -> x -> (y -> a) -> SyncActions ('SyncPars m ex up down) b b a
  -- |Get the current state of write token
  GetWTAction :: (SBool b -> a) -> SyncActions ('SyncPars m ex up down) b b a
  -- |Throw an exception.
  ThrowAction :: InList '(e, b) ex -> e -> SyncActions ('SyncPars m ex up down) b b' a

  -- |Run a local action in the inner monad.
  SyncLiftAction :: m x -> (x -> a) -> SyncActions ('SyncPars m ex up down) b b a

instance Functor (SyncActions st bef aft) where
  fmap f (AcceptAction cont) = AcceptAction $ f . cont
  fmap f (YieldAction m r) = YieldAction m $ f r
  fmap f (CallAction i m cont) = CallAction i m $ f . cont
  fmap f (GetWTAction cont) = GetWTAction $ f . cont
  fmap _ (ThrowAction i e) = ThrowAction i e
  fmap f (SyncLiftAction m cont) = SyncLiftAction m $ f . cont

-- $monad

-- |The monad for expressing cryptographic algorithms.
--
-- By instantiating @SyncAlgo@ with different parameters, you can finely
-- control what side-effects you allow:
--
-- - @bef@ and @aft@ specify whether this action consumes and/or produces the Write Token.
newtype SyncAlgo
                 (st :: SyncPars)
                 (bef :: Bool) -- ^State before an action
                 (aft :: Bool) -- ^State after an action
                 a -- ^Returned value
    = SyncAlgo { fromSyncAlgo :: XFree (SyncActions st) bef aft a }

  deriving (Functor) via (XFree (SyncActions st) bef aft)
  deriving (XApplicative, XMonad) via (XFree (SyncActions st))

instance Applicative (SyncAlgo st bef bef) where
  f <*> m = SyncAlgo $ fromSyncAlgo f <*> fromSyncAlgo m
  pure = SyncAlgo . pure

instance Monad (SyncAlgo st bef bef) where
  m >>= f = SyncAlgo $ fromSyncAlgo m Monad.>>= (fromSyncAlgo . f)

xfreeSync :: SyncActions st bef aft a -> SyncAlgo st bef aft a
xfreeSync = SyncAlgo . xfree

-- Sync

lift :: m a -> SyncAlgo ('SyncPars m ex up down) b b a
lift m = xfreeSync $ SyncLiftAction m id

instance Print m => Print (SyncAlgo ('SyncPars m ex up down) b b) where
  debugPrint = lift . debugPrint

instance Rand m => Rand (SyncAlgo ('SyncPars m ex up down) b b) where
  rand = lift $ rand

instance XThrow (SyncAlgo ('SyncPars m ex up down)) ex where
  xthrow i ex = xfreeSync $ ThrowAction i ex

instance XCatch
    (SyncAlgo ('SyncPars m ex up down))
    ex
    (SyncAlgo ('SyncPars m ex' up down))
  where
    xcatch (SyncAlgo a) h = SyncAlgo $ xcatch' a $ \i e -> fromSyncAlgo (h i e)
      where
        xcatch' :: XFree (SyncActions ('SyncPars m ex up down)) bef aft a
                -> (forall e b. InList '(e, b) ex -> e -> XFree (SyncActions ('SyncPars m ex' up down)) b aft a)
                -> XFree (SyncActions ('SyncPars m ex' up down)) bef aft a
        xcatch' (Pure x) _ = xreturn x
        xcatch' (Join a) h' = case a of
            AcceptAction cont -> Join $ AcceptAction $ (`xcatch'` h') . cont
            YieldAction x r -> Join $ YieldAction x $ r `xcatch'` h'
            CallAction i m cont -> Join $ CallAction i m $ (`xcatch'` h') . cont
            GetWTAction cont -> Join $ GetWTAction $ (`xcatch'` h') . cont
            ThrowAction i e -> h' i e
            SyncLiftAction m cont -> Join $ SyncLiftAction m $ (`xcatch'` h') . cont

instance GetWT (SyncAlgo ('SyncPars m ex up down)) where
  getWT = xfreeSync $ GetWTAction id

instance SyncUp (SyncAlgo ('SyncPars m ex '(x, y) down)) '(x, y) where
  accept = xfreeSync $ AcceptAction id
  yield x = xfreeSync $ YieldAction x ()

instance SyncDown (SyncAlgo ('SyncPars m ex up down)) down where
  call i x = xfreeSync $ CallAction i x id

-- $eval

-- |The result of `runTillYield`
data YieldRes m up down aft a where
  -- |Algorithm called `yield`.
  YRYield :: Fst up
          -> SyncAlgo ('SyncPars m '[] up down) False aft a
          -> YieldRes m up down aft a
  -- |Algorithm has called a child oracle via `call`
  YRCall :: Chan x y down
         -> x
         -> (y -> SyncAlgo ('SyncPars m '[] up down) True aft a)
         -> YieldRes m up down aft a
  -- |Algorithm halted without sending anything
  YRHalt :: a -> YieldRes m up down True a

-- |Given `SyncAlgo` action starting in `True` state (holding write token), run
-- it until it does `call`, `yield` or halts.
runTillYield :: Monad m
            => SyncAlgo ('SyncPars m '[] up down) True b a
            -> m (YieldRes m up down b a)
runTillYield (SyncAlgo (Pure v)) = pure $ YRHalt v
runTillYield (SyncAlgo (Join v)) = case v of
  YieldAction x r -> pure $ YRYield x $ SyncAlgo r
  CallAction i x cont -> pure $ YRCall i x $ SyncAlgo . cont
  GetWTAction cont -> runTillYield $ SyncAlgo $ cont STrue
  ThrowAction contra _ -> case contra of {}
  SyncLiftAction m cont -> m >>= runTillYield . SyncAlgo . cont

-- |The result of `deliver`
data DeliverRes m up down aft a where
  -- |Algorithm ran `accept`
  DRAccept :: SyncAlgo ('SyncPars m '[] up down) True aft a
           -> DeliverRes m up down aft a
  -- |Algorithm issued an oracle call to a child via `call`
  DRCall :: Chan x y down
         -> x
         -> (y -> SyncAlgo ('SyncPars m '[] up down) False aft a)
         -> DeliverRes m up down aft a
  -- |Algorithm has halter without accepting a call
  DRHalt :: a
         -> DeliverRes m up down False a

-- |Given an action that starts in a `False` state (no write token), deliver
-- the oracle call from its parent (running it until it receives the write
-- token via `accept`).
deliver :: Monad m
        => Snd up
        -> SyncAlgo ('SyncPars m '[] up down) False b a
        -> m (DeliverRes m up down b a)
deliver _ (SyncAlgo (Pure v)) = pure $ DRHalt v
deliver m (SyncAlgo (Join v)) = case v of
  AcceptAction cont ->pure $ DRAccept $ SyncAlgo $ cont m
  CallAction i x cont -> pure $ DRCall i x $ SyncAlgo . cont
  GetWTAction cont -> deliver m $ SyncAlgo $ cont SFalse
  ThrowAction contra _ -> case contra of {}
  SyncLiftAction a cont -> a >>= deliver m . SyncAlgo . cont

-- |An algorithm with no parent and with access to child oracles given by
-- `down`. Starts and finished holding the write token
type OracleCallerWrapper m down a =
  SyncAlgo ('SyncPars m '[] '(Void, Void) down) True True a

-- |An algorithm serving oracle calls from parent, but not having access to
-- any oracles of its own and not returning any result. It exposes the `up`
-- interface as the last argument for use with `HList`.
type OracleWrapper m a up =
  SyncAlgo ('SyncPars m '[] '(Snd up, OracleReq (Fst up)) '[]) False True a

data OracleReq a = OracleReqHalt | OracleReq a

-- |Given main algorithm `top` and an oracle algorithm `bot`, run them together
-- and return the result of `top`. Note that `runWithOracles` passes all the
-- messages between the running interactive algorithms, therefore its result is
-- a non-interactive algorithm.
--
-- The `forall aft` part in the type of child oracle ensures that oracles do
-- not terminate in-between handling the requests.
runWithOracle :: Monad m
               => OracleCallerWrapper m '[ '(x, y) ] a
               -- ^The oracle caller algorithm
               -> (OracleWrapper m s '(x, y))
               -- ^The oracle
               -> MaybeT m (a, s)
               -- ^The outputs of caller and oracle. Fails with `mzero` if
               -- the oracle terminates before time or doesn't terminate when
               -- requested
runWithOracle top bot = Trans.lift (runTillYield top) >>= \case
    YRYield contra _ -> case contra of {}
    YRHalt r -> do
      s <- oracleHalt bot
      pure (r, s)
    YRCall (There contra) _ _ -> case contra of {}
    YRCall Here m cont -> do
      (r, bot') <- oracleCall bot m
      runWithOracle (cont r) bot'
  where
    oracleCall :: Monad m
               => OracleWrapper m s '(x, y)
               -> x
               -> MaybeT m (y, OracleWrapper m s '(x, y))
    oracleCall bot m = Trans.lift (deliver (OracleReq m) bot) >>= \case
      DRCall contra _ _ -> case contra of {}
      DRAccept cont -> Trans.lift (runTillYield cont) >>= \case
        YRCall contra _ _ -> case contra of {}
        YRHalt _ -> mzero
        YRYield r bot' -> pure (r, bot')
    oracleHalt :: Monad m
               => OracleWrapper m s '(x, y)
               -> MaybeT m s
    oracleHalt bot = Trans.lift (deliver OracleReqHalt bot) >>= \case
      DRCall contra _ _ -> case contra of {}
      DRAccept cont -> Trans.lift (runTillYield cont) >>= \case
        YRCall contra _ _ -> case contra of {}
        YRHalt s -> pure s
        YRYield _ _ -> mzero
