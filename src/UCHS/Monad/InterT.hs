{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCHS.Monad.InterT (
  -- * Interactive Algorithm Monad
  -- $monad
    InterT(..)
  , Index
  , InterPars(..)
  , xfreeSync
  , lift
  -- , catch
  -- * Syntax
  -- $actions
  , InterActions(..)
  -- * Derived Definitions
  , AsyncT
  , AsyncExT
  , SyncT
  , SyncExT
  -- * Step-by-step Execution
  -- $step
  , runTillSend
  , SendRes(..)
  , runTillRecv
  , RecvRes(..)
  , runTillHaltAsync
  -- ** Helper lemmas
  -- $lemmas
  , mayOnlyRecvVoidPrf
  , mayOnlyRecvWTPrf
  , mayOnlySendWTPrf
  , cannotEscapeNothingPrf
  , justUnreachableFromNothingPrf
) where

-- import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad
import Data.Functor
import Data.Functor.Identity

import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad
import qualified Control.XMonad.Do as M

import Unsafe.Coerce (unsafeCoerce)

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
  , stEx :: [(Type, Index)]
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
-- -
--
-- @bef@ and @aft@ are the states before and after the given action. The
-- meaning of possible states is as follows:
data InterActions (st :: InterPars) (bef :: Index) (aft :: Index) a where
  RecvAction :: (SomeSndMessage ach -> a) -> InterActions ('InterPars m ex ach sch) (On NextRecv) (On NextSend) a
  SendAction :: SomeFstMessage ach -> a -> InterActions ('InterPars m ex ach sch) (On NextSend) (On NextRecv) a
  SendFinalAction :: SomeFstMessage ach -> a -> InterActions ('InterPars m ex ach sch) (On NextSend) Off a
  -- |Perform a call to a child, immediately getting the result
  CallAction :: Chan x y sch -> x -> (y -> a) -> InterActions ('InterPars m ex ach sch) b b a
  -- |Throw an exception.
  ThrowAction :: InList '(e, b) ex -> e -> InterActions ('InterPars m ex ach sch) b b' a

  -- |Run a local action in the inner monad.
  LiftAction :: m x -> (x -> a) -> InterActions ('InterPars m ex ach sch) b b a

instance Functor (InterActions st bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m r) = SendAction m $ f r
  fmap f (SendFinalAction m r) = SendFinalAction m $ f r
  fmap f (CallAction i m cont) = CallAction i m $ f . cont
  fmap _ (ThrowAction i e) = ThrowAction i e
  fmap f (LiftAction m cont) = LiftAction m $ f . cont

-- $monad

-- |The monad for expressing interactive algorithms.
--
-- By instantiating `InterT` with different parameters, you can finely
-- control what side-effects you allow:
--
-- - Local computations in Monad @stInner st@.
-- - Syncronous calls to oracle interfaces in @stSync st@.
-- - Asynchronous communcation over interfaces defined in @stAsync st@.
--
--   Asynchronous communcation depends on the `Index` state of `InterT`. There
--   are three possible index states which are interpreted as follows.
--
--   - `Off` means that asyncronous communcation is disabled.
--   - @`On` `NextSend`@ means that it's our turn to send.
--   - @`On` `NextRecv`@ means that it's our turn to receive (we currently have one
--     message in our inbox).
--
--   The states @`On` `NextSend`@ and @`On` `NextRecv`@ are toggled with `send` and
--   `recvAny`. The state `Off` is reached via `sendFinal` and stays
--   this way until the algorithm terminates. Any asyncronous algorithm will
--   alternate between `send` and `recvAny` some number of times, until it
--   terminates or calls `sendFinal` (and then terninates).
--
-- - @bef@ and @aft@ specify whether this action consumes and/or produces the Write Token.
newtype InterT (st :: InterPars)
              (bef :: Index) -- ^State before an action
              (aft :: Index) -- ^State after an action
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
            SendFinalAction x r -> Join $ SendFinalAction x $ r `xcatch'` h'
            CallAction i m cont -> Join $ CallAction i m $ (`xcatch'` h') . cont
            ThrowAction i e -> h' i e
            LiftAction m cont -> Join $ LiftAction m $ (`xcatch'` h') . cont

instance Async (InterT ('InterPars m ex ach sch)) ach where
  sendMess m = xfreeSync $ SendAction m ()
  sendMessFinal m = xfreeSync $ SendFinalAction m ()
  recvAny = xfreeSync $ RecvAction id

instance Sync (InterT ('InterPars m ex ach sch)) sch where
  call i x = xfreeSync $ CallAction i x id

-- $derived
-- The following definitions specialize `InterT` for narrower use-cases. These
-- definitions should suffice for most of the programs you'd want to write.

-- |Indexed transformer that adds asyncronous `send`/`recvAny` (channels
-- given by @ach@) to monad @m@, as well as throwing exceptions defined by the
-- list @ex@.
type AsyncExT m ex ach = InterT ('InterPars m ex ach '[])

-- |Same as `AsyncExT`, but with exceptions off.
type AsyncT m ach = AsyncExT m '[] ach

-- |Non-indexed transformer that adds syncronous `call` (channels given by
-- @ach@) to monad @m@, as well as throwing exceptions defined by the list
-- @ex@.
--
-- `SyncExT` does not handle asynchronous interaction, therefore it does not
-- need to be indexed.
type SyncExT m ex sch = InterT ('InterPars m ex '[] sch) (On NextSend) (On NextSend)

-- |Same as `SyncExT`, but with exceptions off.
type SyncT m sch = SyncExT m '[] sch

-- $step
--
-- The following functions let you evaluate an interactive algorithm
-- step-by-step. An algorithm in `True` state can be ran until it sends
-- something (or halts, or does an oracle call) via `runTillSend`, and an
-- algorithm in `False` state can be executed until it reqests a message for
-- reception (or halts, or does an oracle call) via `runTillRecv`.

-- |The result of `runTillSend`
data SendRes (m :: Type -> Type) (ach :: [(Type, Type)]) (sch :: [(Type, Type)]) (aft :: Index) a where
  -- |Algorithm called `send` or `yield`.
  SrSend :: SomeFstMessage ach
         -> InterT ('InterPars m '[] ach sch) (On NextRecv) aft a
         -> SendRes m ach sch aft a
  -- |Algorithm called `sendFinal`.
  SrSendFinal :: SomeFstMessage ach
              -> InterT ('InterPars m '[] ach sch) Off aft a
              -> SendRes m ach sch aft a
  -- |Algorithm has called an oracle via `call`
  SrCall :: Chan x y sch
         -> x
         -> (y -> InterT ('InterPars m '[] ach sch) (On NextSend) aft a)
         -> SendRes m ach sch aft a
  -- |Algorithm halted without sending anything
  SrHalt :: a -> SendRes m ach sch (On NextSend) a

-- |Given `InterT` action starting in `True` state (holding write token), run
-- it until it does `call`, `send` or halts.
runTillSend :: Monad m
            => InterT ('InterPars m '[] up down) (On NextSend) b a
            -> m (SendRes m up down b a)
runTillSend (InterT (Pure v)) = pure $ SrHalt v
runTillSend (InterT (Join v)) = case v of
  SendAction x r -> pure $ SrSend x $ InterT r
  SendFinalAction x r -> pure $ SrSendFinal x $ InterT r
  CallAction i x cont -> pure $ SrCall i x $ InterT . cont
  ThrowAction contra _ -> case contra of {}
  LiftAction m cont -> m >>= runTillSend . InterT . cont

-- |The result of `runTillRecv`.
data RecvRes m up down aft a where
  -- |Algorithm ran `accept`
  RrRecv :: InterT ('InterPars m '[] up down) (On NextSend) aft a
         -> RecvRes m up down aft a
  -- |Algorithm issued an oracle call to a child via `call`
  RrCall :: Chan x y down
         -> x
         -> (y -> InterT ('InterPars m '[] up down) (On NextRecv) aft a)
         -> RecvRes m up down aft a
  -- |Algorithm has halter without accepting a call
  RrHalt :: a
         -> RecvRes m up down (On NextRecv) a

-- |Given an action that starts in a `False` state (no write token),
-- runTillRecv the oracle call from its parent (running it until it receives
-- the write token via `recvAny`).
runTillRecv :: Monad m
        => SomeSndMessage ach
        -> InterT ('InterPars m '[] ach sch) (On NextRecv) b a
        -> m (RecvRes m ach sch b a)
runTillRecv _ (InterT (Pure v)) = pure $ RrHalt v
runTillRecv m (InterT (Join v)) = case v of
  RecvAction cont -> pure $ RrRecv $ InterT $ cont m
  CallAction i x cont -> pure $ RrCall i x $ InterT . cont
  ThrowAction contra _ -> case contra of {}
  LiftAction a cont -> a >>= runTillRecv m . InterT . cont

-- |Run an action until it terminates, return its result.
--
-- The action has no sync channels and runs with `Off` index value, i.e. has
-- its async communication disabled at runtime.
runTillHaltAsync :: Monad m
            => InterT ('InterPars m '[] ach '[]) Off b' a
            -> m a
runTillHaltAsync (InterT (Pure x)) = pure x
runTillHaltAsync (InterT (Join cont)) = case cont of
  CallAction contra _ _ -> case contra of {}
  ThrowAction contra _ -> case contra of {}
  LiftAction m cont' -> do
    v <- m
    runTillHaltAsync $ InterT $ cont' v

-- $lemmas
--
-- These lemmas make it easier to extract the contents of `RecvRes` and
-- `SendRes` in cases when types guarrantee that these values can be
-- deconstructed in only one way (i.e. there is only one value constrctor that
-- could have produces the value of this type).
--
-- These helpers allow (when applicable) you to write a sequence of
-- `runTillRecv` and `runTillSend` in a linear fashion. You can do
--
-- @
-- do
--   x \<- `mayOnlyRecvVoidPrf` \<$> `runTillRecv` _ _
--   (y, cont) \<- `mayOnlySendWTPrf` \<$> `runTillSend` _
--   _
-- @
--
-- instead of manually proving that some constructors are impossible as below.
--
-- @
-- do
--   `runTillRecv` _ _ `>>=` \case
--     `RrCall` contra _ _ -> case contra of {}
--     `RrHalt` contra -> case contra of {}
--     `RrRecv` x -> do
--       `runTillSend` _ `>>=` \case
--         `SrCall` contra _ _ -> case contra of {}
--         `SrSend` y cont -> do
--           _
-- @

-- |Proof: an interactive computation that starts in `Off` state and does
-- not use exceptions, must finish in `Off` state (unless it diverges).
--
-- The proof uses `unsafeCoerce`, Haskell can't verify this for us. So make
-- sure it's proven correctly on paper.
cannotEscapeNothingPrf :: InterT ('InterPars m '[] ach sch) Off aft a
                       -> aft :~: Off
cannotEscapeNothingPrf (InterT i) = case i of
  Pure v -> Refl
  Join (CallAction _ _ _) -> unsafeCoerce $ Refl @()
  Join (ThrowAction contra _) -> case contra of {}
  Join (LiftAction _ _) -> unsafeCoerce $ Refl @()
  -- ^Here, we know by induction that the programmer can't escape
  -- `Off`. But I don't think I can express this induction (over a sequance
  -- of nested lambdas) in Haskell, therefore the `unsafeCoerce`.

-- |Proof: A program with sync channels and return type `Void` may not
-- terminate; if it starts from `On NextRecv` state, it will inevitably request
-- an rx message.
mayOnlyRecvVoidPrf :: RecvRes m ach '[] (On NextRecv) Void
                   -> InterT ('InterPars m '[] ach '[]) (On NextSend) (On NextRecv) Void
mayOnlyRecvVoidPrf = \case
  RrCall contra _ _ -> case contra of {}
  RrHalt contra -> case contra of {}
  RrRecv x -> x

-- |Proof: a program with no sync channels that must terminate in `(On NextSend)`
-- state but starts in `(On NextRecv)` state will inevitably request an rx
-- message.
mayOnlyRecvWTPrf :: RecvRes m ach '[] (On NextSend) a
                 -> InterT ('InterPars m '[] ach '[]) (On NextSend) (On NextSend) a
mayOnlyRecvWTPrf = \case
  RrCall contra _ _ -> case contra of {}
  RrRecv x -> x

-- |Proof: a program with no sync channels that must terminate in `On NextRecv`
-- state that starts from `On NextSend` state will inevitable produce a tx
-- message.
mayOnlySendWTPrf :: SendRes m ach '[] (On NextRecv) a
       -> (SomeFstMessage ach, InterT ('InterPars m '[] ach '[]) (On NextRecv) (On NextRecv) a)
mayOnlySendWTPrf = \case
  SrCall contra _ _ -> case contra of {}
  SrSendFinal _ cont -> case cannotEscapeNothingPrf cont of {}
  SrSend x cont -> (x, cont)

-- |Proof: `On aft` being reachable from `Off` is a cotradiction.
--
-- We use the class constraint to derive a contradiction here, and the `InterT`
-- is given merely to capture the monad indices. In a way, this statement is
-- dual to `cannotEscapeNothingPrf` which proves the same contradiction from
-- the perspective of someone consuming the expressions of type `InterT`.
justUnreachableFromNothingPrf :: forall ps aft a. IndexReachable Off (On aft)
                              => InterT ps Off (On aft) a
justUnreachableFromNothingPrf = case getIndexReachablePrf @Off @(On aft) of {}
