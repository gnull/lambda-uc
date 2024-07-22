{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Monad.UCHS.Classes
  (
  -- * Local Computations
  -- $local
    Print(..)
  , Rand(..)
  , Throw(..)
  -- * Interactive Computations
  -- $interactive
  , GetWT(..)
  , XThrow(..)
  -- ** Synchronous Interaction
  -- $sync
  , SyncUp(..)
  , SyncDown(..)
  -- ** Asynchronous Interaction
  -- $async
  , Async(..)
  -- $derived
  , ExBadSender(..)
  , recv
  , sendSync
  -- * Abstracting monad type
  -- $lifting
  , liftAlgo
  , liftSyncAlgo
  , liftAsyncAlgo
  ) where

import Data.Kind
import Data.HList

import Control.XMonad
import Control.XFreer.Join
import qualified Control.XMonad.Do as M
import Data.Type.Equality ((:~:)(Refl))

import Types

import qualified Control.Monad.UCHS.Local as L
import qualified Control.Monad.UCHS.Sync as S
import qualified Control.Monad.UCHS.Async as A

-- $local
--
-- A local (non-interactive) algorithm may perform the following side-effects:
-- throwing exceptions, sampling random bits, printing debug messages.
--
-- These side effects are also compatible with interactive algorithms.

class Monad m => Print (m :: Type -> Type) where
  -- |Print debug info.
  --
  -- This has no effect on the algorithm definition, i.e. all `debugPrint`
  -- calls are ignored when your protocol is converted into a real-world
  -- implementation. But you may use print statements to illustrate your
  -- algorithms in toy executions.
  debugPrint :: String -> m ()

class Monad m => Rand (m :: Type -> Type) where
  -- |Sample a random value.
  rand :: (Bounded a, Enum a) => m a

class Monad m => Throw (m :: Type -> Type) (e :: Type) | m -> e where
  -- |Throw an exception.
  throw :: e -> m a

-- $interactive
--
-- Side-effects available to both syncronous and asynchronous interactive
-- algorithms: reading the current state of the write token, throwing
-- write-token-aware exceptions.

class XMonad m => GetWT m where
  getWT :: m b b (SBool b)

class XMonad m => XThrow (m :: Bool -> Bool -> Type -> Type) (ex :: [(Type, Bool)]) | m -> ex where
  xthrow :: InList '(e, b) ex -> e -> m b b' a

-- $sync
--
-- Side-effects of a syncronous interactive algorithm. Such an algorithm can:
--
-- 1. handle oracle calls from its parent (`SyncUp`),
-- 2. issue oracle calls to its children (`SyncDown`).
--
-- Oracle calls are synchronous: calling algorithm is put to sleep until its
-- child responds to the call. An algorithm may implement one of `SyncUp` and
-- `SyncDown` or both depending on whether it is supposed to provide and/or
-- call oracle interfaces.

class GetWT m => SyncUp (m :: Bool -> Bool -> Type -> Type) (up :: (Type, Type)) | m -> up where
  -- |Accept an oracle call from parent.
  accept :: m False True (Snd up)
  -- |Yield the response to the previosly accepted oracle call from parent.
  yield :: (Fst up) -> m True False ()

class GetWT m => SyncDown (m :: Bool -> Bool -> Type -> Type) (down :: [(Type, Type)]) | m -> down where
  -- |Perform an oracle call to a child. The call waits for the child to
  -- respond (putting caller to sleep until then).
  call :: Chan x y down -> x -> m b b y

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

class GetWT m => Async (m :: Bool -> Bool -> Type -> Type) (chans :: [(Type, Type)]) | m -> chans where
  -- |Send message to the channel it is marked with.
  sendMess :: SomeFstMessage chans -> m True False ()

  -- |Curried version of `sendMess`.
  send :: Chan x y chans -> x -> m True False ()
  send i m = sendMess $ SomeFstMessage i m

  -- |Receive the next message which can arrive from any of `chan` channels.
  recvAny :: m False True (SomeSndMessage chans)

-- $lifting
--
-- The following functions convert a concrete (local or interactive) monad
-- syntax into any monad that implements the same operations. The main use of
-- these is to demonstrate what combination of typeclasses each of `L.Algo`,
-- `S.SyncAlgo` and `A.AsyncAlgo` is equivalent to.
--
-- Conversion in the other direction (from polymorphic monad to concrete
-- syntax) is done automatically.

-- Local

instance Print (L.Algo True ra ex) where
  debugPrint = L.Algo . debugPrint

instance Rand (L.Algo pr True ex) where
  rand = L.Algo rand

instance Throw (L.Algo pr ra e) e where
  throw = L.Algo . throw

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

-- Sync

instance Print (S.SyncAlgo ('S.SyncPars True ra ex chans) b b) where
  debugPrint s = S.xfreeSync $ S.PrintAction s ()

instance Rand (S.SyncAlgo ('S.SyncPars pr True ex chans) b b) where
  rand = S.xfreeSync $ S.RandAction id

instance Throw (S.SyncAlgo ('S.SyncPars pr ra '[ '(ex, b)] chans) b b) ex where
  throw = xthrow Here

instance XThrow (S.SyncAlgo ('S.SyncPars pr ra ex chans)) ex where
  xthrow i ex = S.xfreeSync $ S.ThrowAction i ex

instance GetWT (S.SyncAlgo ('S.SyncPars pr ra ex (Just '(up, down)))) where
  getWT = S.xfreeSync $ S.GetWTAction id

instance SyncUp (S.SyncAlgo ('S.SyncPars pr ra ex (Just '( '(x, y), down)))) '(x, y) where
  accept = S.xfreeSync $ S.AcceptAction id
  yield x = S.xfreeSync $ S.YieldAction x ()

instance SyncDown (S.SyncAlgo ('S.SyncPars pr ra ex (Just '(up, down)))) down where
  call i x = S.xfreeSync $ S.CallAction i x id

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

-- Async

instance Print (A.AsyncAlgo ('A.AsyncPars True ra ex chans) b b) where
  debugPrint s = A.xfreeAsync $ A.PrintAction s ()

instance Rand (A.AsyncAlgo ('A.AsyncPars pr True ex chans) b b) where
  rand = A.xfreeAsync $ A.RandAction id

instance Throw (A.AsyncAlgo ('A.AsyncPars pr ra '[ '(ex, b)] chans) b b) ex where
  throw = xthrow Here

instance XThrow (A.AsyncAlgo ('A.AsyncPars pr ra ex chans)) ex where
  xthrow i ex = A.xfreeAsync $ A.ThrowAction i ex

instance GetWT (A.AsyncAlgo ('A.AsyncPars pr ra ex chans)) where
  getWT = A.xfreeAsync $ A.GetWTAction id

instance Async (A.AsyncAlgo ('A.AsyncPars pr ra ex chans)) chans where
  sendMess m = A.xfreeAsync $ A.SendAction m ()
  recvAny = A.xfreeAsync $ A.RecvAction id

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


-- $derived
--
-- Some convenient shorthand operations built from basic ones.

-- |An exception thrown if a message does not arrive from the expected sender.
data ExBadSender = ExBadSender

-- |Receive from a specific channel. If an unexpected message arrives from
-- another channel, throw the `()` exception.
recv :: (XThrow m '[ '(ExBadSender, True)], Async m l)
     => Chan x y l
     -> m False True y
recv i = M.do
  SomeSndMessage j m <- recvAny
  case testEquality i j of
    Just Refl -> xreturn m
    Nothing -> M.do
      xthrow Here ExBadSender

-- |Send message to a given channel and wait for a response. If some other
-- message arrives before the expected response, throw the `()` exception.
sendSync :: (XThrow m '[ '(ExBadSender, True)], Async m l)
         => x -> Chan x y l -> m True True y
sendSync m chan = M.do
  send chan m
  (SomeSndMessage i y) <- recvAny
  case testEquality i chan of
    Just Refl -> xreturn y
    Nothing -> xthrow Here ExBadSender
