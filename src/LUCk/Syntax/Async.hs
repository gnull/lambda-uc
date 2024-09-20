{-# LANGUAGE ScopedTypeVariables #-}

module LUCk.Syntax.Async (
  -- * Interactive Algorithm Monad
  -- $monad
    AsyncExT(..)
  , AsyncT
  , Index
  , xfreeAsync
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
  , mayOnlySendVoidPrf
) where

-- import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad

import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad
import Control.XMonad.Trans
-- import qualified Control.XMonad.Do as M

-- import Data.Type.Equality ((:~:)(Refl))

import LUCk.Types
import LUCk.Syntax.Class

-- $actions
--
-- Actions are given in Free monad syntax.


-- |@bef@ and @aft@ are the states before and after the given action. The
-- meaning of possible states is as follows:
data AsyncActions (ex :: [(Type, Index)]) (ach :: [(Type, Type)]) (m :: Type -> Type)
                  (bef :: Index) (aft :: Index) (a :: Type) where
  RecvAction :: (SomeSndMessage ach -> a)
             -> AsyncActions ex ach m NextRecv NextSend a
  SendAction :: SomeFstMessage ach
             -> a
             -> AsyncActions ex ach m NextSend NextRecv a
  -- |Throw an exception.
  ThrowAction :: InList '(e, b) ex
              -> e
              -> AsyncActions ex ach m b b' a

  -- |Run a local action in the inner monad.
  LiftAction :: m x
             -> (x -> a)
             -> AsyncActions ex ach m b b a

instance Functor (AsyncActions ex ach m bef aft) where
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
-- `AsyncT` is a special version of `AsyncExT` where exceptions are disabled.
newtype AsyncExT ex ach m bef aft a
    = AsyncExT { runInterT :: XFree (AsyncActions ex ach m) bef aft a }
  deriving (Functor)

instance bef ~ aft => Applicative (AsyncExT ex ach m bef aft) where
  f <*> m = AsyncExT $ runInterT f <*> runInterT m
  pure = AsyncExT . pure

instance bef ~ aft => Monad (AsyncExT ex ach m bef aft) where
  m >>= f = AsyncExT $ runInterT m Monad.>>= (runInterT . f)

instance XApplicative (AsyncExT ex ach m) where
  xpure = AsyncExT . xpure
  f <*>: x = AsyncExT $ runInterT f <*>: runInterT x

instance XMonad (AsyncExT ex ach m) where
  m >>=: f = AsyncExT $ runInterT m >>=: (runInterT . f)

xfreeAsync :: AsyncActions ex ach m bef aft a -> AsyncExT ex ach m bef aft a
xfreeAsync = AsyncExT . xfree

instance XMonadTrans (AsyncExT ex ach) where
  xlift m = xfreeAsync $ LiftAction m id

-- Haskell can't derive these for us when there are ambiguous types in M.do notation:
--
-- @
--   debugPring "hey"
--   b <- rand
-- @

instance XThrow (AsyncExT ex ach m) ex where
  xthrow i ex = xfreeAsync $ ThrowAction i ex

instance XCatch
    (AsyncExT ex ach m)
    ex
    (AsyncExT ex' ach m)
  where
    xcatch (AsyncExT a) h = AsyncExT $ xcatch' a $ \i e -> runInterT (h i e)
      where
        xcatch' :: XFree (AsyncActions ex ach m) bef aft a
                -> (forall e b. InList '(e, b) ex -> e -> XFree (AsyncActions ex' ach m) b aft a)
                -> XFree (AsyncActions ex' ach m) bef aft a
        xcatch' (Pure x) _ = xreturn x
        xcatch' (Join a') h' = case a' of
            RecvAction cont -> Join $ RecvAction $ (`xcatch'` h') . cont
            SendAction x r -> Join $ SendAction x $ r `xcatch'` h'
            ThrowAction i e -> h' i e
            LiftAction m cont -> Join $ LiftAction m $ (`xcatch'` h') . cont

instance Async (AsyncExT ex ach m) ach where
  sendMess m = xfreeAsync $ SendAction m ()
  recvAny = xfreeAsync $ RecvAction id

-- $derived
-- The following definitions specialize `AsyncExT` for narrower use-cases. These
-- definitions should suffice for most of the programs you'd want to write.

-- |Same as `AsyncExT`, but with exceptions off.
type AsyncT = AsyncExT '[]

-- $step
--
-- The following functions let you evaluate an interactive algorithm
-- step-by-step. An algorithm in `NextSend` state can be ran until it sends
-- something (or halts, or does an oracle call) via `runTillSend`, and an
-- algorithm in `NextRecv` state can be executed until it reqests a message for
-- reception (or halts, or does an oracle call) via `runTillRecv`.
--
-- Functions `runTillSend` and `runTillRecv` correspond to activation of an
-- Interactive Turing Machine.

-- |The result of `runTillSend`
data SendRes ach m aft a where
  -- |Algorithm called `send`.
  SrSend :: SomeFstMessage ach
         -> AsyncT ach m NextRecv aft a
         -> SendRes ach m aft a
  -- |Algorithm called `sendFinal`.
  SrHalt :: a -> SendRes ach m NextSend a

-- |Given `AsyncExT` action starting in `NextSend` state (holding write token),
-- run it until it does `send` or halts.
runTillSend :: Monad m
            => AsyncT ach m NextSend b a
            -> m (SendRes ach m b a)
runTillSend (AsyncExT (Pure v)) = pure $ SrHalt v
runTillSend (AsyncExT (Join v)) = case v of
  SendAction x r -> pure $ SrSend x $ AsyncExT r
  ThrowAction contra _ -> case contra of {}
  LiftAction m cont -> m >>= runTillSend . AsyncExT . cont

-- |The result of `runTillRecv`.
data RecvRes ach m aft a where
  -- |Algorithm ran `recvAny`.
  RrRecv :: (SomeSndMessage ach -> AsyncT ach m NextSend aft a)
         -> RecvRes ach m aft a
  -- |Algorithm has halted without accepting a message
  RrHalt :: a
         -> RecvRes ach m NextRecv a

-- |Given an action that starts in a `NextRecv` state (no write token), run it
-- until it receives the write token via `recvAny` or halts.
runTillRecv :: Monad m
        => AsyncT ach m NextRecv b a
        -> m (RecvRes ach m b a)
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
--   (y, cont) \<- `mayOnlySendVoidPrf` \<$> `runTillSend` _
--   _
-- @
--
-- instead of manually proving that some constructors are impossible as below.
--
-- @
-- do
--   `runTillRecv` _ _ `>>=` \case
--     `RrHalt` contra -> case contra of {}
--     `RrRecv` x -> do
--       `runTillSend` _ `>>=` \case
--         `SrHalt` contra -> case contra of {}
--         `SrSend` y cont -> do
--           _
-- @

-- |Proof: A program with sync channels and return type `Void` may not
-- terminate; if it starts from `NextRecv` state, it will inevitably request
-- an rx message.
mayOnlyRecvVoidPrf :: RecvRes ach m aft Void
                   -> SomeSndMessage ach
                   -> AsyncT ach m NextSend aft Void
mayOnlyRecvVoidPrf = \case
  RrHalt contra -> case contra of {}
  RrRecv x -> x

-- |Proof: A program with sync channels and return type `Void` may not
-- terminate; if it starts from `NextSend` state, it will inevitably request to
-- send a message.
mayOnlySendVoidPrf :: SendRes ach m aft Void
                   -> (SomeFstMessage ach, AsyncT ach m NextRecv aft Void)
mayOnlySendVoidPrf = \case
  SrHalt contra -> case contra of {}
  SrSend m cont -> (m, cont)
