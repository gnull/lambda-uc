{-# LANGUAGE MultiParamTypeClasses #-}

module UCHS.Monad.Class
  (
  -- * Local Computations
  -- $local
    Print(..)
  , Rand(..)
  , UniformDist(..)
  , Throw(..)
  , Catch(..)
  -- * Interactive Computations
  -- $interactive
  , GetWT(..)
  , XThrow(..)
  , XCatch(..)
  -- ** Synchronous Interaction
  -- $sync
  , Sync(..)
  -- ** Asynchronous Interaction
  -- $async
  , Async(..)
  -- $derived
  , accept
  , yield
  , ExBadSender(..)
  , recv
  , sendSync
  ) where

import Data.Kind
import Data.HList

import Control.XMonad
import Control.XApplicative
import qualified Control.XMonad.Do as M

import Control.XMonad
import Data.Type.Equality ((:~:)(Refl))
import UCHS.Types

import qualified System.Random as Random
import qualified Control.Monad.Trans.Class as Trans

-- $local
--
-- A local (non-interactive) algorithm may perform the following side-effects:
-- throwing exceptions, sampling random bits, printing debug messages.
--
-- Implemented by both local `UCHS.Monad.Algo.Algo` and interactive
-- `UCHS.Monad.InterT.InterT`.

class Monad m => Print (m :: Type -> Type) where
  -- |Print debug info.
  --
  -- This has no effect on the algorithm definition, i.e. all `debugPrint`
  -- calls are ignored when your protocol is converted into a real-world
  -- implementation. But you may use print statements to illustrate your
  -- algorithms in toy executions.
  debugPrint :: String -> m ()

instance Print IO where
  debugPrint = putStrLn

instance (Trans.MonadTrans t, Print m) => Print (t m) where
  debugPrint = Trans.lift . debugPrint

class Monad m => Rand (m :: Type -> Type) where
  -- |Sample a random value.
  rand :: m Bool

instance (Trans.MonadTrans t, Rand m) => Rand (t m) where
  rand = Trans.lift $ rand

instance Rand IO where
  rand = Random.randomIO

class UniformDist s where
  -- |Sample a uniformly random value from `s`
  uniformDist :: forall m. Rand m => m s

class Monad m => Throw (m :: Type -> Type) (e :: Type) | m -> e where
  -- |Throw an exception.
  throw :: e -> m a

class (Throw m e, Monad m') => Catch m e m' | m -> e where
  -- |Catch an exception.
  catch :: m a -> (e -> m' a) -> m' a

-- $interactive
--
-- Side-effects available to both syncronous and asynchronous interactive
-- algorithms: reading the current state of the write token, throwing
-- write-token-aware exceptions.

class XMonad m => GetWT m where
  getWT :: KnownBool b => m b b (SBool b)

class XMonad m => XThrow (m :: Bool -> Bool -> Type -> Type) (ex :: [(Type, Bool)]) | m -> ex where
  -- |Throw a context-aware exception. The list of possible exceptions `ex`
  -- contains types annotated with the write-token state from which they can be
  -- thrown.
  xthrow :: InList '(e, b) ex -> e -> m b b' a

class (XThrow m ex, XMonad m') => XCatch m ex m' where
  -- |Can an exception (like one ones thrown by `xthrow`). The handler
  -- must bring write token to the `aft` state, the same as the one where
  -- computation would end up if no exception occurred.
  xcatch :: m bef aft a
        -- ^The computation that may throw an exception
        -> (forall e b. InList '(e, b) ex -> e -> m' b aft a)
        -- ^How to handle the exception
        -> m' bef aft a

-- $sync
--
-- Side-effects of a syncronous interactive algorithm. Such an algorithm can:
--
-- 1. issue oracle calls to its children (`Sync`).
--
-- Oracle calls are synchronous: calling algorithm is put to sleep until its
-- child responds to the call. An algorithm may implement one of `Syncp` and
-- `Sync` or both depending on whether it is supposed to provide and/or
-- call oracle interfaces.

class GetWT m => Sync (m :: Bool -> Bool -> Type -> Type) (down :: [(Type, Type)]) | m -> down where
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

-- $derived
--
-- Some convenient shorthand operations built from basic ones.


accept :: Async m '[ '(x, y)]
       => m False True y
accept = M.do
  recvAny >>=: \case
    SomeSndMessage Here m -> xpure m
    SomeSndMessage (There contra) _ -> case contra of {}

yield :: Async m '[ '(x, y)]
      => x -> m True False ()
yield = send Here

-- |An exception thrown if a message does not arrive from the expected sender.
data ExBadSender = ExBadSender

-- |Receive from a specific channel. If an unexpected message arrives from
-- another channel, throw the `ExBadSender` exception.
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
-- message arrives before the expected response, throw the `ExBadSender`
-- exception.
sendSync :: (XThrow m '[ '(ExBadSender, True)], Async m l)
         => x -> Chan x y l -> m True True y
sendSync m chan = M.do
  send chan m
  (SomeSndMessage i y) <- recvAny
  case testEquality i chan of
    Just Refl -> xreturn y
    Nothing -> xthrow Here ExBadSender
