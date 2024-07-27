{-# LANGUAGE DerivingVia #-}

module UCHS.Monad.InterT (
  -- * Interactive Algorithm Monad
  -- $monad
    InterT(..)
  , InterPars(..)
  , xfreeSync
  , lift
  -- , catch
  -- * Syntax
  -- $actions
  , InterActions(..)
  -- * Evaluation
  -- $eval
  , runTillSend
  , SendRes(..)
  , runTillRecv
  , RecvRes(..)
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
import qualified Control.XMonad.Do as M

-- import Data.Type.Equality ((:~:)(Refl))

import UCHS.Types
import UCHS.Monad.Class

import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad (MonadPlus(..))
import qualified Control.Monad.Trans.Class as Trans

-- |The parameters of @InterT@ that do not change throughout the execution
data InterPars = InterPars
  { stInner :: Type -> Type
  -- ^The inner monad where the local computations happen
  , stEx :: [(Type, Bool)]
  -- ^Type of exceptions we throw and contexts (use @[]@ to disable exceptions)
  , stAsync :: [(Type, Type)]
  -- ^Asynchronous channels
  , stSync :: [(Type, Type)]
  -- ^Syncronous channels
  }

-- $actions
--
-- Actions are given in Free monad syntax.


-- |Defines actions for:
--
-- - @bef@ and @aft@ are the states before and after the given action.
data InterActions (st :: InterPars) (bef :: Bool) (aft :: Bool) a where
  RecvAction :: (SomeSndMessage ach -> a) -> InterActions ('InterPars m ex ach sch) False True a
  SendAction :: SomeFstMessage ach -> a -> InterActions ('InterPars m ex ach sch) True False a
  -- |Perform a call to a child, immediately getting the result
  CallAction :: Chan x y sch -> x -> (y -> a) -> InterActions ('InterPars m ex ach sch) b b a
  -- |Throw an exception.
  ThrowAction :: InList '(e, b) ex -> e -> InterActions ('InterPars m ex ach sch) b b' a

  -- |Run a local action in the inner monad.
  LiftAction :: m x -> (x -> a) -> InterActions ('InterPars m ex ach sch) b b a

instance Functor (InterActions st bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m r) = SendAction m $ f r
  fmap f (CallAction i m cont) = CallAction i m $ f . cont
  fmap _ (ThrowAction i e) = ThrowAction i e
  fmap f (LiftAction m cont) = LiftAction m $ f . cont

-- $monad

-- |The monad for expressing cryptographic algorithms.
--
-- By instantiating @InterT@ with different parameters, you can finely
-- control what side-effects you allow:
--
-- - @bef@ and @aft@ specify whether this action consumes and/or produces the Write Token.
newtype InterT (st :: InterPars)
              (bef :: Bool) -- ^State before an action
              (aft :: Bool) -- ^State after an action
              a -- ^Returned value
    = InterT { fromSyncAlgo :: XFree (InterActions st) bef aft a }

  deriving (Functor) via (XFree (InterActions st) bef aft)
  deriving (XApplicative, XMonad) via (XFree (InterActions st))

instance Applicative (InterT st bef bef) where
  f <*> m = InterT $ fromSyncAlgo f <*> fromSyncAlgo m
  pure = InterT . pure

instance Monad (InterT st bef bef) where
  m >>= f = InterT $ fromSyncAlgo m Monad.>>= (fromSyncAlgo . f)

xfreeSync :: InterActions st bef aft a -> InterT st bef aft a
xfreeSync = InterT . xfree

-- Sync

lift :: m a -> InterT ('InterPars m ex up down) b b a
lift m = xfreeSync $ LiftAction m id

instance Print m => Print (InterT ('InterPars m ex up down) b b) where
  debugPrint = lift . debugPrint

instance Rand m => Rand (InterT ('InterPars m ex up down) b b) where
  rand = lift $ rand

instance XThrow (InterT ('InterPars m ex up down)) ex where
  xthrow i ex = xfreeSync $ ThrowAction i ex

instance XCatch
    (InterT ('InterPars m ex up down))
    ex
    (InterT ('InterPars m ex' up down))
  where
    xcatch (InterT a) h = InterT $ xcatch' a $ \i e -> fromSyncAlgo (h i e)
      where
        xcatch' :: XFree (InterActions ('InterPars m ex up down)) bef aft a
                -> (forall e b. InList '(e, b) ex -> e -> XFree (InterActions ('InterPars m ex' up down)) b aft a)
                -> XFree (InterActions ('InterPars m ex' up down)) bef aft a
        xcatch' (Pure x) _ = xreturn x
        xcatch' (Join a') h' = case a' of
            RecvAction cont -> Join $ RecvAction $ (`xcatch'` h') . cont
            SendAction x r -> Join $ SendAction x $ r `xcatch'` h'
            CallAction i m cont -> Join $ CallAction i m $ (`xcatch'` h') . cont
            ThrowAction i e -> h' i e
            LiftAction m cont -> Join $ LiftAction m $ (`xcatch'` h') . cont

instance GetWT (InterT ('InterPars m ex up down)) where
  getWT = pure $ getSBool

instance Async (InterT ('InterPars m ex ach sch)) ach where
  sendMess m = xfreeSync $ SendAction m ()
  recvAny = xfreeSync $ RecvAction id

instance Sync (InterT ('InterPars m ex ach sch)) sch where
  call i x = xfreeSync $ CallAction i x id

-- $eval

-- |The result of `runTillSend`
data SendRes (m :: Type -> Type) (ach :: [(Type, Type)]) (sch :: [(Type, Type)]) (aft :: Bool) a where
  -- |Algorithm called `yield`.
  SrSend :: SomeFstMessage ach
         -> InterT ('InterPars m '[] ach sch) False aft a
         -> SendRes m ach sch aft a
  -- |Algorithm has called a child oracle via `call`
  SrCall :: Chan x y sch
         -> x
         -> (y -> InterT ('InterPars m '[] ach sch) True aft a)
         -> SendRes m ach sch aft a
  -- |Algorithm halted without sending anything
  SrHalt :: a -> SendRes m ach sch True a

-- |Given `InterT` action starting in `True` state (holding write token), run
-- it until it does `call`, `send` or halts.
runTillSend :: Monad m
            => InterT ('InterPars m '[] up down) True b a
            -> m (SendRes m up down b a)
runTillSend (InterT (Pure v)) = pure $ SrHalt v
runTillSend (InterT (Join v)) = case v of
  SendAction x r -> pure $ SrSend x $ InterT r
  CallAction i x cont -> pure $ SrCall i x $ InterT . cont
  ThrowAction contra _ -> case contra of {}
  LiftAction m cont -> m >>= runTillSend . InterT . cont

-- |The result of `runTillRecv`.
data RecvRes m up down aft a where
  -- |Algorithm ran `accept`
  RrRecv :: InterT ('InterPars m '[] up down) True aft a
           -> RecvRes m up down aft a
  -- |Algorithm issued an oracle call to a child via `call`
  RrCall :: Chan x y down
         -> x
         -> (y -> InterT ('InterPars m '[] up down) False aft a)
         -> RecvRes m up down aft a
  -- |Algorithm has halter without accepting a call
  RrHalt :: a
         -> RecvRes m up down False a

-- |Given an action that starts in a `False` state (no write token),
-- runTillRecv the oracle call from its parent (running it until it receives
-- the write token via `recvAny`).
runTillRecv :: Monad m
        => SomeSndMessage ach
        -> InterT ('InterPars m '[] ach sch) False b a
        -> m (RecvRes m ach sch b a)
runTillRecv _ (InterT (Pure v)) = pure $ RrHalt v
runTillRecv m (InterT (Join v)) = case v of
  RecvAction cont -> pure $ RrRecv $ InterT $ cont m
  CallAction i x cont -> pure $ RrCall i x $ InterT . cont
  ThrowAction contra _ -> case contra of {}
  LiftAction a cont -> a >>= runTillRecv m . InterT . cont

-- |An algorithm with no parent and with access to child oracles given by
-- `down`. Starts and finished holding the write token.
type OracleCallerWrapper m down a =
  InterT ('InterPars m '[] '[] down) True True a

-- |An algorithm serving oracle calls from parent, but not having access to
-- any oracles of its own and not returning any result. It exposes the `up`
-- interface as the last argument for use with `HList`.
type OracleWrapper m a up =
  InterT ('InterPars m '[] '[ '(Snd up, OracleReq (Fst up))] '[]) False True a

data OracleReq a = OracleReqHalt | OracleReq a

-- |Given main algorithm `top` and an oracle algorithm `bot`, run them together
-- and return their results. The `top` returns its result directly when
-- terminating, then a special `OracleReqHalt` message is sent to the `bot` to
-- ask it to terminate and return its result.
--
-- We throw a `mzero` error in case the oracle does not follow the termination
-- condition: terminates before receiving `OracleReqHalt` or tries to respond
-- to `OracleReqHalt` instead of terminating.
--
-- Note that `runWithOracles` passes all the messages between the running
-- interactive algorithms, therefore its result is a non-interactive algorithm.
runWithOracle :: Monad m
               => OracleCallerWrapper m '[ '(x, y) ] a
               -- ^The oracle caller algorithm
               -> OracleWrapper m s '(x, y)
               -- ^The oracle
               -> MaybeT m (a, s)
               -- ^The outputs of caller and oracle. Fails with `mzero` if
               -- the oracle terminates before time or doesn't terminate when
               -- requested
runWithOracle top bot = Trans.lift (runTillSend top) >>= \case
    SrSend (SomeFstMessage contra _) _ -> case contra of {}
    SrHalt r -> do
      s <- oracleHalt bot
      pure (r, s)
    SrCall (There contra) _ _ -> case contra of {}
    SrCall Here m cont -> do
      (r, bot') <- oracleCall bot m
      runWithOracle (cont r) bot'
  where
    oracleCall :: Monad m
               => OracleWrapper m s '(x, y)
               -> x
               -> MaybeT m (y, OracleWrapper m s '(x, y))
    oracleCall bot' m = Trans.lift (runTillRecv (SomeSndMessage Here (OracleReq m)) bot') >>= \case
      RrCall contra _ _ -> case contra of {}
      RrRecv cont -> Trans.lift (runTillSend cont) >>= \case
        SrCall contra _ _ -> case contra of {}
        SrHalt _ -> mzero
        SrSend r bot'' -> case r of
            SomeFstMessage Here r' -> pure (r', bot'')
            SomeFstMessage (There contra) _ -> case contra of {}
          
    oracleHalt :: Monad m
               => OracleWrapper m s '(x, y)
               -> MaybeT m s
    oracleHalt bot' = Trans.lift (runTillRecv (SomeSndMessage Here OracleReqHalt) bot') >>= \case
      RrCall contra _ _ -> case contra of {}
      RrRecv cont -> Trans.lift (runTillSend cont) >>= \case
        SrCall contra _ _ -> case contra of {}
        SrHalt s -> pure s
        SrSend _ _ -> mzero
