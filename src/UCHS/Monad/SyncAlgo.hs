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
) where

import Prelude hiding ((>>=), return)
import qualified Control.Monad as Monad
import Control.XFreer.Join
import Control.XApplicative
import Control.XMonad
-- import qualified Control.XMonad.Do as M

-- import Data.Type.Equality ((:~:)(Refl))

import UCHS.Types
import UCHS.Monad.Class

-- |The parameters of @SyncAlgo@ that do not change throughout the execution
data SyncPars = SyncPars
  { stInner :: Type -> Type
  -- ^The inner monad where the local computations happen
  , stEx :: [(Type, Bool)]
  -- ^Type of exceptions we throw and contexts (use @[]@ to disable exceptions)
  , stChans :: Maybe ((Type, Type), [(Type, Type)])
  -- ^The upstream interface to our parent and downstream interfaces to children.
  -- Using @Nothing@ here disables both types of interfaces
  }

-- $actions
--
-- Actions are given in Free monad syntax.


-- |Defines actions for:
--
-- - @bef@ and @aft@ are the states before and after the given action.
data SyncActions (st :: SyncPars) (bef :: Bool) (aft :: Bool) a where
  -- |Accept an oracle call from parent
  AcceptAction :: (y -> a) -> SyncActions ('SyncPars m ex (Just '( '(x, y), down))) False True a
  -- |Yield the result of an oracle call from the parent
  YieldAction :: x -> a -> SyncActions ('SyncPars m ex (Just '( '(x, y), down))) True False a
  -- |Perform a call to a child, immediately getting the result
  CallAction :: Chan x y down -> x -> (y -> a) -> SyncActions ('SyncPars m ex (Just '( up, down))) b b a
  -- |Get the current state of write token
  GetWTAction :: (SBool b -> a) -> SyncActions ('SyncPars m ex (Just '(up, down))) b b a
  -- |Throw an exception.
  ThrowAction :: InList '(e, b) ex -> e -> SyncActions ('SyncPars m ex chans) b b' a

  -- |Run a local action in the inner monad.
  SyncLiftAction :: m x -> (x -> a) -> SyncActions ('SyncPars m ex chans) b b a

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

lift :: m a -> SyncAlgo ('SyncPars m ex chans) b b a
lift m = xfreeSync $ SyncLiftAction m id

instance Print m => Print (SyncAlgo ('SyncPars m ex chans) b b) where
  debugPrint = lift . debugPrint

instance Rand m => Rand (SyncAlgo ('SyncPars m ex chans) b b) where
  rand = lift $ rand

-- instance Throw (SyncAlgo ('SyncPars m '[ '(ex, b)] chans) b b) ex where
--   throw = xthrow Here

-- instance Catch
--     (SyncAlgo ('SyncPars m '[ '(ex, b)] chans) b b)
--     ex
--     (SyncAlgo ('SyncPars m '[ '(ex', b)] chans) b b)
--   where
--     catch x h = xcatch x $ \case
--       Here -> h
--       There contra -> case contra of {}

instance XThrow (SyncAlgo ('SyncPars m ex chans)) ex where
  xthrow i ex = xfreeSync $ ThrowAction i ex

instance XCatch
    (SyncAlgo ('SyncPars m ex chans))
    ex
    (SyncAlgo ('SyncPars m ex' chans))
  where
    xcatch (SyncAlgo a) h = SyncAlgo $ xcatch' a $ \i e -> fromSyncAlgo (h i e)
      where
        xcatch' :: XFree (SyncActions ('SyncPars m ex chans)) bef aft a
                -> (forall e b. InList '(e, b) ex -> e -> XFree (SyncActions ('SyncPars m ex' chans)) b aft a)
                -> XFree (SyncActions ('SyncPars m ex' chans)) bef aft a
        xcatch' (Pure x) _ = xreturn x
        xcatch' (Join a) h' = case a of
            AcceptAction cont -> Join $ AcceptAction $ (`xcatch'` h') . cont
            YieldAction x r -> Join $ YieldAction x $ r `xcatch'` h'
            CallAction i m cont -> Join $ CallAction i m $ (`xcatch'` h') . cont
            GetWTAction cont -> Join $ GetWTAction $ (`xcatch'` h') . cont
            ThrowAction i e -> h' i e
            SyncLiftAction m cont -> Join $ SyncLiftAction m $ (`xcatch'` h') . cont

instance GetWT (SyncAlgo ('SyncPars m ex (Just '(up, down)))) where
  getWT = xfreeSync $ GetWTAction id

instance SyncUp (SyncAlgo ('SyncPars m ex (Just '( '(x, y), down)))) '(x, y) where
  accept = xfreeSync $ AcceptAction id
  yield x = xfreeSync $ YieldAction x ()

instance SyncDown (SyncAlgo ('SyncPars m ex (Just '(up, down)))) down where
  call i x = xfreeSync $ CallAction i x id

-- -------------

-- -- Shuffles the order of arguments around
-- data OracleUpWrapper m up =
--   HListUpWrapper (SyncAlgo ('SyncPars m '[] ('Just '( ChanSwap up, '[]))) False False ())

-- type OracleDownWrapper m down a =
--   SyncAlgo ( 'SyncPars m '[] (Just '( '(Void, Void) , down ))) True False a

-- data IterationResult m up down a
--   = IterationYield (Fst up) ()
--   | IterationCall (SomeFstMessage down)
--   | IterationHalt a

-- runTillSend :: SyncAlgo ('SyncPars m '[] (Just '( '(x, y), down))) True b a
--             -> (Either x (SomeSndMessage down), SyncAlgo ('SyncPars m '[] (Just '( '(x, y), down))) False b a)

-- runWithOracles :: OracleDownWrapper False ra down a
--                -> HList (OracleUpWrapper False ra') down
--                -> SyncAlgo ('SyncPars False (Or ra ra') ex Nothing) True True a
-- runWithOracles top bot = case fromSyncAlgo top of
--   Join (YieldAction contra _) -> case contra of {}
--   Join (CallAction i x cont) -> _
--   Join (GetWTAction cont) -> cont
--   Join (PrintAction x r) -> _
--   Join (RandAction cont) -> _
--   Join (ThrowAction i e) -> _

