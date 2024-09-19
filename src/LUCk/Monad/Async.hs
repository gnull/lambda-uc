{-# LANGUAGE ScopedTypeVariables #-}

module LUCk.Monad.Async (
  -- * Interactive Algorithm Monad
  -- $monad
    AsyncExT(..)
  , AsyncT
  , Index
  , xfreeAsync
  , lift
  -- * Syntax
  -- $actions
  , AsyncActions(..)
  -- * Step-by-step Execution
  -- $step
  , runTillSend
  , SendRes(..)
  , runTillRecv
  , RecvRes(..)
  -- ** Helper lemmas
  -- $lemmas
  , mayOnlyRecvVoidPrf
  , mayOnlyRecvWTPrf
  , mayOnlySendWTPrf
) where

-- import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad
import Data.Functor
import Data.Functor.Identity

import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad
import qualified Control.XMonad.Do as M

-- import Data.Type.Equality ((:~:)(Refl))

import LUCk.Types
import LUCk.Monad.Class

import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad (MonadPlus(..))
import qualified Control.Monad.Trans.Class as Trans

-- $actions
--
-- Actions are given in Free monad syntax.


-- |@bef@ and @aft@ are the states before and after the given action. The
-- meaning of possible states is as follows:
data AsyncActions (m :: Type -> Type) (ex :: [(Type, Index)]) (ach :: [(Type, Type)])
                  (bef :: Index) (aft :: Index) (a :: Type) where
  RecvAction :: (SomeSndMessage ach -> a)
             -> AsyncActions m ex ach NextRecv NextSend a
  SendAction :: SomeFstMessage ach
             -> a
             -> AsyncActions m ex ach NextSend NextRecv a
  -- |Throw an exception.
  ThrowAction :: InList '(e, b) ex
              -> e
              -> AsyncActions m ex ach b b' a

  -- |Run a local action in the inner monad.
  LiftAction :: m x
             -> (x -> a)
             -> AsyncActions m ex ach b b a

instance Functor (AsyncActions m ex ach bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m r) = SendAction m $ f r
  fmap _ (ThrowAction i e) = ThrowAction i e
  fmap f (LiftAction m cont) = LiftAction m $ f . cont

-- $monad

-- |The monad for expressing interactive algorithms.
--
-- By instantiating `AsyncExT` with different parameters, you can finely
-- control what side-effects you allow:
--
-- - Local computations in Monad @`stInner` st@.
-- - Asynchronous (`send` and `recvAny`) communcation over
--   interfaces defined in @`stAsync` st@.
--
-- Asynchronous communcation depends on the `Index` state of `AsyncExT`. There
-- are two possible index states which are interpreted as follows.
--
-- - `NextSend` means that it's our turn to send.
-- - `NextRecv` means that it's our turn to receive (we currently have one
--   message in our inbox).
--
-- The states `NextSend` and `NextRecv` are toggled with `send` and
-- `recvAny`. Any asyncronous algorithm will alternate between `send` and
-- `recvAny` some number of times, until it terminates. Such algorithm's
-- indices tell which of the two operations must be first and last (effectively
-- telling the parity of the number of alternations).
--
-- The `AsyncExT` also implements Index-aware exceptions, configured with @`stEx`
-- st@. Each exception is defined by a type of value thrown and `Index` from
-- which it is thrown.
--
-- All three types of side-effects are optional and can be disabled on-demand
-- by setting the fields of `InterPars`. We provide type-synonyms for such
-- monads that allow only part of `AsyncExT`'s full functionality:
--
-- - `AsyncExT` provides only asyncronous `send` and `recvAny`, as well as allows thowing excetpions.
-- - `AsyncT` is a special version of `AsyncExT` where exceptions are disabled.
newtype AsyncExT m ex ach bef aft a
    = AsyncExT { runInterT :: XFree (AsyncActions m ex ach) bef aft a }
  deriving (Functor)

instance Applicative (AsyncExT m ex ach bef bef) where
  f <*> m = AsyncExT $ runInterT f <*> runInterT m
  pure = AsyncExT . pure

instance Monad (AsyncExT m ex ach bef bef) where
  m >>= f = AsyncExT $ runInterT m Monad.>>= (runInterT . f)

instance XApplicative (AsyncExT m ex ach) where
  xpure = AsyncExT . xpure
  f <*>: x = AsyncExT $ runInterT f <*>: runInterT x

instance XMonad (AsyncExT m ex ach) where
  m >>=: f = AsyncExT $ runInterT m >>=: (runInterT . f)

xfreeAsync :: AsyncActions m ex ach bef aft a -> AsyncExT m ex ach bef aft a
xfreeAsync = AsyncExT . xfree

-- Sync

lift :: m a -> AsyncExT m ex ach b b a
lift m = xfreeAsync $ LiftAction m id

instance Print m => Print (AsyncExT m ex ach b b) where
  debugPrint = lift . debugPrint

instance Rand m => Rand (AsyncExT m ex ach b b) where
  rand = lift $ rand

instance XThrow (AsyncExT m ex ach) ex where
  xthrow i ex = xfreeAsync $ ThrowAction i ex

instance XCatch
    (AsyncExT m ex ach)
    ex
    (AsyncExT m ex' ach)
  where
    xcatch (AsyncExT a) h = AsyncExT $ xcatch' a $ \i e -> runInterT (h i e)
      where
        xcatch' :: XFree (AsyncActions m ex ach) bef aft a
                -> (forall e b. InList '(e, b) ex -> e -> XFree (AsyncActions m ex' ach) b aft a)
                -> XFree (AsyncActions m ex' ach) bef aft a
        xcatch' (Pure x) _ = xreturn x
        xcatch' (Join a') h' = case a' of
            RecvAction cont -> Join $ RecvAction $ (`xcatch'` h') . cont
            SendAction x r -> Join $ SendAction x $ r `xcatch'` h'
            ThrowAction i e -> h' i e
            LiftAction m cont -> Join $ LiftAction m $ (`xcatch'` h') . cont

instance Async (AsyncExT m ex ach) ach where
  sendMess m = xfreeAsync $ SendAction m ()
  recvAny = xfreeAsync $ RecvAction id

-- $derived
-- The following definitions specialize `AsyncExT` for narrower use-cases. These
-- definitions should suffice for most of the programs you'd want to write.

-- |Same as `AsyncExT`, but with exceptions off.
type AsyncT m ach = AsyncExT m '[] ach

-- $step
--
-- The following functions let you evaluate an interactive algorithm
-- step-by-step. An algorithm in `True` state can be ran until it sends
-- something (or halts, or does an oracle call) via `runTillSend`, and an
-- algorithm in `False` state can be executed until it reqests a message for
-- reception (or halts, or does an oracle call) via `runTillRecv`.

-- |The result of `runTillSend`
data SendRes m ach aft a where
  -- |Algorithm called `send`.
  SrSend :: SomeFstMessage ach
         -> AsyncT m ach NextRecv aft a
         -> SendRes m ach aft a
  -- |Algorithm called `sendFinal`.
  SrHalt :: a -> SendRes m ach NextSend a

-- |Given `AsyncExT` action starting in `True` state (holding write token), run
-- it until it does `call`, `send` or halts.
runTillSend :: Monad m
            => AsyncT m ach NextSend b a
            -> m (SendRes m ach b a)
runTillSend (AsyncExT (Pure v)) = pure $ SrHalt v
runTillSend (AsyncExT (Join v)) = case v of
  SendAction x r -> pure $ SrSend x $ AsyncExT r
  ThrowAction contra _ -> case contra of {}
  LiftAction m cont -> m >>= runTillSend . AsyncExT . cont

-- |The result of `runTillRecv`.
data RecvRes m ach aft a where
  -- |Algorithm ran `recvAny`.
  RrRecv :: (SomeSndMessage ach -> AsyncT m ach NextSend aft a)
         -> RecvRes m ach aft a
  -- |Algorithm has halted without accepting a call
  RrHalt :: a
         -> RecvRes m ach NextRecv a

-- |Given an action that starts in a `False` state (no write token),
-- runTillRecv the oracle call from its parent (running it until it receives
-- the write token via `recvAny`).
runTillRecv :: Monad m
        => AsyncT m ach NextRecv b a
        -> m (RecvRes m ach b a)
runTillRecv (AsyncExT (Pure v)) = pure $ RrHalt v
runTillRecv (AsyncExT (Join v)) = case v of
  RecvAction cont -> pure $ RrRecv $ AsyncExT . cont
  ThrowAction contra _ -> case contra of {}
  LiftAction a cont -> a >>= runTillRecv . AsyncExT . cont

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

-- |Proof: A program with sync channels and return type `Void` may not
-- terminate; if it starts from `On NextRecv` state, it will inevitably request
-- an rx message.
mayOnlyRecvVoidPrf :: RecvRes m ach NextRecv Void
                   -> SomeSndMessage ach
                   -> AsyncT m ach NextSend NextRecv Void
mayOnlyRecvVoidPrf = \case
  RrHalt contra -> case contra of {}
  RrRecv x -> x

-- |Proof: a program with no sync channels that must terminate in `NextSend`
-- state but starts in `NextRecv` state will inevitably request an rx
-- message.
mayOnlyRecvWTPrf :: RecvRes m ach NextSend a
                 -> SomeSndMessage ach
                 -> AsyncT m ach NextSend NextSend a
mayOnlyRecvWTPrf (RrRecv x) = x

-- |Proof: a program with no sync channels that must terminate in `On NextRecv`
-- state that starts from `On NextSend` state will inevitable produce a tx
-- message.
mayOnlySendWTPrf :: SendRes m ach NextRecv a
       -> (SomeFstMessage ach, AsyncT m ach NextRecv NextRecv a)
mayOnlySendWTPrf (SrSend x cont) = (x, cont)
