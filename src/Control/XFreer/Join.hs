{-# LANGUAGE QuantifiedConstraints #-}

module Control.XFreer.Join
  ( XFree (..),
    xfree,
  )
where

-- This module is based on Control.Freer from freer-indexed, but changes the
-- internal respresentaiton to Join-based instead of Bind-based.

import Control.XApplicative
import Control.XMonad
import qualified Control.XMonad.Do as M

-- | 'XFree' is the freer indexed monad that wraps an (algebraic, non-composable) effect
-- to provide 'Functor', 'XApplicative' and 'XMonad' (indexed applicative and monad) for free.
data XFree f p q a where
  Pure :: a -> XFree f p p a
  Join :: f p q (XFree f q r a) -> XFree f p r a

-- | Function to convert an indexed effect to 'XFree' monad (see example above)
xfree :: Functor (f p q) => f p q a -> XFree f p q a
xfree fa = Join $ Pure <$> fa

instance (forall p q. Functor (f p q)) => Functor (XFree f p q) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Join x) = Join $ fmap (fmap f) x

instance (forall p q. Functor (f p q)) => XApplicative (XFree f) where
  xpure = Pure
  f <*>: x = M.do
    f' <- f
    x' <- x
    xpure $ f' x'

instance (forall p q. Functor (f p q)) => XMonad (XFree f) where
  Pure x >>=: f = f x
  Join x >>=: f = Join $ fmap (>>=: f) x
    -- Free g >>= f = Free $ fmap (>>= f) g

-- | @'XFree' (f p p)@ is a normal Applicative, it supports 'forever', 'traverse', 'sequenceA', etc.
instance (forall p q. Functor (f p q)) => Applicative (XFree f p p) where
  pure = xpure
  (<*>) = (<*>:)

-- | @'XFree' (f p p)@ is a normal Monad, it supports 'mapM', 'forM', 'sequence', etc.
instance (forall p q. Functor (f p q)) => Monad (XFree f p p) where
  (>>=) = (>>=:)
