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
           => InList '(ex, b) exs
           -> L.Algo pr ra ex a
           -> m a
liftAlgo _ (L.Algo (S.SyncAlgo (Pure v))) = pure v
liftAlgo i (L.Algo (S.SyncAlgo (Join v))) =
  case v of
    S.YieldAction contra _ -> case contra of {}
    S.CallAction contra _ _ -> case contra of {}
    S.PrintAction s r -> debugPrint s >> (liftAlgo i $ L.Algo $ S.SyncAlgo r)
    S.RandAction cont -> rand >>= (\b -> liftAlgo i $ L.Algo $ S.SyncAlgo $ cont b)
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

-- $async

