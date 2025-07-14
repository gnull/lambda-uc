{-# LANGUAGE ScopedTypeVariables #-}

module LambdaUC.Syntax.Async (
  -- * Interactive Algorithm Monad
  -- $monad
    AsyncT
  , AsyncExT(..)
  , Exception(..)
  , Index
  , escapeAsyncT
  , xfreeAsync
  -- * Syntax
  -- $actions
  , AsyncActions(..)
  -- * Interactive Computations
  -- $interactive
  -- , Index
  -- , xthrow
  -- , xcatch
  -- ** Asynchronous Interaction
  -- $async
  , send
  , sendMess
  , recvAny
  , xlift
  , xthrow
  , xcatch
  , asyncGetIndex
  , asyncGuard
  -- $derived
  , recvOneEx
  , recvOne
  , sendOne
  -- , ExBadSender(..)
  -- , recv
  -- , sendSync
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
  -- , toMonadRandAsyncT
) where

-- import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad

import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad
import qualified Control.XMonad.Do as M
-- import Control.XMonad.Trans
-- import qualified Control.XMonad.Do as M

import qualified LambdaUC.Syntax.PrAlgo as L

import Data.Kind
import Data.HList
import Data.Type.Equality
import LambdaUC.Types

-- import Data.Type.Equality ((:~:)(Refl))

data Exception = Type :@ Index

-- $actions
--
-- Actions are given in Free monad syntax.

-- |@bef@ and @aft@ are the states before and after the given action. The
-- meaning of possible states is as follows:
data AsyncActions (ex :: [Exception]) (ports :: [Port])
                  (bef :: Index) (aft :: Index) (a :: Type) where
  -- |Receive a message from some channel
  RecvAction :: (SomeRxMess ports -> a)
             -> AsyncActions ex ports NextRecv NextSend a
  -- |Send a message to the chosen channel
  SendAction :: SomeTxMess ports
             -> a
             -> AsyncActions ex ports NextSend NextRecv a
  -- |Run a local action in the inner monad.
  LiftAction :: L.PrAlgo x
             -> (x -> a)
             -> AsyncActions ex ports b b a

  -- |Throw one of the allowed exceptions
  ThrowAction :: InList ex (e :@ i)
              -> e
              -> AsyncActions ex ports i j a

instance Functor (AsyncActions ex ports bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m r) = SendAction m $ f r
  fmap f (LiftAction m cont) = LiftAction m $ f . cont
  fmap _ (ThrowAction i e) = ThrowAction i e

-- $monad

-- |The monad for expressing interactive algorithms.
--
-- By instantiating `AsyncT` with different parameters, you can finely
-- control what side-effects you allow:
--
-- - Asynchronous (`send` and `recvAny`) communcation over
--   interfaces defined in @ports@.
--
-- Asynchronous communcation depends on the `Index` state of `AsyncT`. There
-- are two possible index states which are interpreted as follows.
--
-- - `NextSend` means that it's our turn to send.
-- - `NextRecv` means that it's our turn to receive (we currently have one
--   message in our inbox).
--
-- The states `NextSend` and `NextRecv` are toggled with `send` and
-- `recvAny`. Any asyncronous algorithm will alternate between `send` and
-- `recvAny` some number of times, until it terminates. Such algorithm's
-- indices tell which of the two operations must be first and last.
--
-- Additionally, you may sample random values in `AsyncT` using @`L.rand`@.
newtype AsyncExT ex ports bef aft a
    = AsyncExT { runInterT :: XFree (AsyncActions ex ports) bef aft a }
  deriving (Functor)

instance bef ~ aft => Applicative (AsyncExT ex ports bef aft) where
  f <*> m = AsyncExT $ runInterT f <*> runInterT m
  pure = AsyncExT . pure

instance bef ~ aft => Monad (AsyncExT ex ports bef aft) where
  m >>= f = AsyncExT $ runInterT m Monad.>>= (runInterT . f)

instance XApplicative (AsyncExT ex ports) where
  xpure = AsyncExT . xpure
  f <*>: x = AsyncExT $ runInterT f <*>: runInterT x

instance XMonad (AsyncExT ex ports) where
  m >>=: f = AsyncExT $ runInterT m >>=: (runInterT . f)

instance L.MonadRand (AsyncExT ex ports i i) where
  rand = xlift L.rand

xfreeAsync :: AsyncActions ex ports bef aft a -> AsyncExT ex ports bef aft a
xfreeAsync = AsyncExT . xfree

-- instance XMonadTrans (AsyncT ports) where
xlift :: L.PrAlgo a -> AsyncExT ex ports i i a
xlift m = xfreeAsync $ LiftAction m id

type AsyncT = AsyncExT '[]

-- |Interactive action with no free ports can be interpreted as local.
--
-- Apply this function once you've bound all the free ports to run the execution.
escapeAsyncT :: AsyncT '[] NextSend NextSend a
             -> L.PrAlgo a
escapeAsyncT cont = runTillSend cont >>= \case
  SrSend (SomeTxMess contra _) _ -> case contra of {}
  SrHalt res -> pure res

-- $async
--
-- Side-effects of an asynchronous interactive algorithm. Such an algorithm can:
--
-- 1. send a message to a chosen recepient,
-- 2. receive message from a receiver.
--
-- Note that sending a message does not require the recepient to respond (now
-- or later). When receiving a message, we must be ready that it can arrive
-- from anyone — as the exact order of messages can not be predicted at compile
-- time.

-- |Send a message to the port it is marked with.
sendMess :: SomeTxMess ports -> AsyncExT ex ports NextSend NextRecv ()
sendMess m = xfreeAsync $ SendAction m ()

-- |Curried version of `sendMess`.
send :: InList ports p -> PortTxType p -> AsyncExT ex ports NextSend NextRecv ()
send i m = sendMess $ SomeTxMess i m

-- |Receive the next message which can arrive from any of `port` ports.
recvAny :: AsyncExT ex ports NextRecv NextSend (SomeRxMess ports)
recvAny = xfreeAsync $ RecvAction id

xthrow :: InList ex (e :@ i)
       -> e
       -> AsyncExT ex ports i j a
xthrow i e = xfreeAsync $ ThrowAction i e

xcatch :: forall ex ex' ports bef aft a.
         AsyncExT ex ports bef aft a
      -- ^The computation that may throw an exception
      -> (forall e b. InList ex (e :@ b) -> e -> AsyncExT ex' ports b aft a)
      -- ^How to handle the exception
      -> AsyncExT ex' ports bef aft a
xcatch (AsyncExT a) h = AsyncExT $ xcatch' a $ \i e -> runInterT (h i e)
  where
    xcatch' :: XFree (AsyncActions ex ports) bef' aft a
            -> (forall e b. InList ex (e :@ b) -> e -> XFree (AsyncActions ex' ports) b aft a)
            -> XFree (AsyncActions ex' ports) bef' aft a
    xcatch' (Pure x) _ = xreturn x
    xcatch' (Join a') h' = case a' of
        RecvAction cont -> Join $ RecvAction $ (`xcatch'` h') . cont
        SendAction x r -> Join $ SendAction x $ r `xcatch'` h'
        ThrowAction i e -> h' i e
        LiftAction m cont -> Join $ LiftAction m $ (`xcatch'` h') . cont

-- $derived
-- The following definitions specialize `AsyncT` for narrower use-cases. These
-- definitions should suffice for most of the programs you'd want to write.

-- $interactive
--
-- Side-effects available to both syncronous and asynchronous interactive
-- algorithms: reading the current state of the write token, throwing
-- write-token-aware exceptions.

-- |Wrapper around `getSIndex` that tells you what context you're in.
asyncGetIndex :: (XMonad m, KnownIndex b) => m b b (SIndex b)
asyncGetIndex = xreturn getSIndex

asyncGuard :: XMonad m
           => SIndex b
           -> m b b ()
asyncGuard _ = xreturn ()

-- $derived
--
-- Some convenient shorthand operations built from basic ones.

recvOne :: AsyncExT ex '[x :> y] NextRecv NextSend y
recvOne = M.do
  recvAny >>=: \case
    SomeRxMess Here m -> xpure m
    SomeRxMess (There contra) _ -> case contra of {}

sendOne :: x -> AsyncExT ex '[x :> y] NextSend NextRecv ()
sendOne = send Here

recvOneEx :: InList ex (e :@ NextSend)
          -> e
          -> PortInList x y ports
          -> AsyncExT ex ports NextRecv NextSend y
recvOneEx i e j =
  recvAny >>=: \case
    SomeRxMess j' m -> case testEquality j j' of
      Just Refl -> xreturn m
      Nothing -> xthrow i e

-- -- |An exception thrown if a message does not arrive from the expected sender.
-- data ExBadSender = ExBadSender

-- -- |Receive from a specific port. If an unexpected message arrives from
-- -- another port, throw the `ExBadSender` exception.
-- recv :: InList ex '(ExBadSender, NextSend)
--      -> PortInList x y l
--      -> AsyncT l m NextRecv NextSend y
-- recv e i = M.do
--   SomeRxMess j m <- recvAny
--   case testEquality i j of
--     Just Refl -> xreturn m
--     Nothing -> M.do
--       xthrow e ExBadSender

-- -- |Send message to a given port and wait for a response. If some other
-- -- message arrives before the expected response, throw the `ExBadSender`
-- -- exception.
-- sendSync :: InList ex '(ExBadSender, NextSend)
--          -> x
--          -> PortInList x y l -> AsyncT ex l m NextSend NextSend y
-- sendSync e m port = M.do
--   send port m
--   (SomeRxMess i y) <- recvAny
--   case testEquality i port of
--     Just Refl -> xreturn y
--     Nothing -> xthrow e ExBadSender

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
data SendRes ports aft a where
  -- |Algorithm called `send`.
  SrSend :: SomeTxMess ports
         -> AsyncT ports NextRecv aft a
         -> SendRes ports aft a
  -- |Algorithm called `sendFinal`.
  SrHalt :: a -> SendRes ports NextSend a

-- |Given `AsyncT` action starting in `NextSend` state (holding write token),
-- run it until it does `send` or halts.
runTillSend :: AsyncT ports NextSend b a
            -> L.PrAlgo (SendRes ports b a)
runTillSend (AsyncExT (Pure v)) = pure $ SrHalt v
runTillSend (AsyncExT (Join v)) = case v of
  SendAction x r -> pure $ SrSend x $ AsyncExT r
  LiftAction m cont -> m >>= runTillSend . AsyncExT . cont
  ThrowAction contra _ -> case contra of {}

-- |The result of `runTillRecv`.
data RecvRes ports aft a where
  -- |Algorithm ran `recvAny`.
  RrRecv :: (SomeRxMess ports -> AsyncT ports NextSend aft a)
         -> RecvRes ports aft a
  -- |Algorithm has halted without accepting a message
  RrHalt :: a
         -> RecvRes ports NextRecv a

-- |Given an action that starts in a `NextRecv` state (no write token), run it
-- until it receives the write token via `recvAny` or halts.
runTillRecv :: AsyncT ports NextRecv b a
            -> L.PrAlgo (RecvRes ports b a)
runTillRecv (AsyncExT (Pure v)) = pure $ RrHalt v
runTillRecv (AsyncExT (Join v)) = case v of
  RecvAction cont -> pure $ RrRecv $ AsyncExT . cont
  LiftAction a cont -> a >>= runTillRecv . AsyncExT . cont
  ThrowAction contra _ -> case contra of {}

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

-- |Proof: A program with sync ports and return type `Void` may not
-- terminate; if it starts from `NextRecv` state, it will inevitably request
-- an rx message.
mayOnlyRecvVoidPrf :: RecvRes ports aft Void
                   -> SomeRxMess ports
                   -> AsyncT ports NextSend aft Void
mayOnlyRecvVoidPrf = \case
  RrHalt contra -> case contra of {}
  RrRecv x -> x

-- |Proof: A program with sync ports and return type `Void` may not
-- terminate; if it starts from `NextSend` state, it will inevitably request to
-- send a message.
mayOnlySendVoidPrf :: SendRes ports aft Void
                   -> (SomeTxMess ports, AsyncT ports NextRecv aft Void)
mayOnlySendVoidPrf = \case
  SrHalt contra -> case contra of {}
  SrSend m cont -> (m, cont)

-- toMonadRandAsyncT :: L.MonadRand m
--                  => AsyncT ports bef aft a
--                  -> AsyncT ports bef aft a
-- toMonadRandAsyncT (AsyncT (Pure v)) = xreturn v
-- toMonadRandAsyncT (AsyncT (Join v)) =
--     case v of
--       SendAction m r -> sendMess m >>: toMonadRandAsyncT (AsyncT r)
--       RecvAction cont -> recvAny >>=: toMonadRandAsyncT . AsyncT . cont
--       LiftAction m cont -> xlift (L.toMonadRand m) >>=: toMonadRandAsyncT . AsyncT . cont
