{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Monad.UCHS.Classes where

import Data.Kind
import Data.HList

import Control.XMonad
import Control.XFreer.Join

import qualified Control.Monad.UCHS.Local as L
import qualified Control.Monad.UCHS.Sync as S

class Monad m => Print (m :: Type -> Type) where
  debugPrint :: String -> m ()

class Monad m => Rand (m :: Type -> Type) where
  rand :: m Bool

class Monad m => Throw (m :: Type -> Type) (e :: Type) | m -> e where
  throw :: e -> m a

class XMonad m => XThrow (m :: Bool -> Bool -> Type -> Type) (ex :: [(Type, Bool)]) | m -> ex where
  xthrow :: InList '(e, b) ex -> e -> m b b' a

type Fst :: (Type, Type) -> Type
type family Fst p where
  Fst '(x, _) = x

type Snd :: (Type, Type) -> Type
type family Snd p where
  Snd '(_, y) = y

class XMonad m => SyncUp (m :: Bool -> Bool -> Type -> Type) (up :: (Type, Type)) | m -> up where
  accept :: m False True (Snd up)
  yield :: (Fst up) -> m True False ()

class XMonad m => SyncDown (m :: Bool -> Bool -> Type -> Type) (down :: [(Type, Type)]) | m -> down where
  call :: Chan x y down -> x -> m b b y

-- $local

instance Print (L.Algo True ra ex) where
  debugPrint = L.Algo . S.debugPrint

instance Rand (L.Algo pr True ex) where
  rand = L.Algo S.rand

instance Throw (L.Algo pr ra e) e where
  throw = L.Algo . S.throw Here

-- |Type-level if-then-else, we use it to choose constraints conditionally
type IfThenElse :: forall a. Bool -> a -> a -> a
type family IfThenElse c t f where
  IfThenElse True t _ = t
  IfThenElse False _ f = f

-- |Empty constraint
class Empty x
instance Empty x

liftAlgo :: ( IfThenElse pr Print Empty m
            , IfThenElse ra Rand Empty m
            , Throw m ex
            )
           => L.Algo pr ra ex a
           -> m a
liftAlgo (L.Algo (S.SyncAlgo (Pure v))) = pure v
liftAlgo (L.Algo (S.SyncAlgo (Join v))) =
  case v of
    S.YieldAction contra _ -> case contra of {}
    S.CallAction contra _ _ -> case contra of {}
    S.PrintAction s r -> debugPrint s >> (liftAlgo $ L.Algo $ S.SyncAlgo r)
    S.RandAction cont -> rand >>= (\b -> liftAlgo $ L.Algo $ S.SyncAlgo $ cont b)
    S.ThrowAction Here e -> throw e
    S.ThrowAction (There contra) _ -> case contra of {}

-- $sync

instance Print (S.SyncAlgo ('S.SyncPars True ra ex up down) b b) where
  debugPrint = S.debugPrint

instance Rand (S.SyncAlgo ('S.SyncPars pr True ex up down) b b) where
  rand = S.rand

instance Throw (S.SyncAlgo ('S.SyncPars pr ra '[ '(ex, b)] up down) b b) ex where
  throw = S.throw Here

instance XThrow (S.SyncAlgo ('S.SyncPars pr ra ex up down)) ex where
  xthrow = S.throw

instance SyncUp (S.SyncAlgo ('S.SyncPars pr ra ex '(x, y) down)) '(x, y) where
  accept = S.accept
  yield = S.yield

instance SyncDown (S.SyncAlgo ('S.SyncPars pr ra ex up down)) down where
  call = S.call

liftSyncAlgo :: ( IfThenElse pr (forall b. Print (m b b)) (forall b. Empty (m b b))
                , IfThenElse ra (forall b. Rand (m b b)) (forall b. Empty (m b b))
                , XThrow m ex
                , SyncUp m up
                , SyncDown m down
                )
               => S.SyncAlgo ('S.SyncPars pr ra ex up down) bef aft a
               -> m bef aft a
liftSyncAlgo (S.SyncAlgo (Pure v)) = xreturn v
liftSyncAlgo (S.SyncAlgo (Join v)) =
  case v of
    S.YieldAction m r -> yield m >>: liftSyncAlgo (S.SyncAlgo r)
    S.AcceptAction cont -> accept >>=: liftSyncAlgo . S.SyncAlgo . cont
    S.CallAction i m cont -> call i m >>=: liftSyncAlgo . S.SyncAlgo . cont
    S.PrintAction s r -> debugPrint s >>: liftSyncAlgo (S.SyncAlgo r)
    S.RandAction cont -> rand >>=: liftSyncAlgo . S.SyncAlgo . cont
    S.ThrowAction i e -> xthrow i e

-- $async

