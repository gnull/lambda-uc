module Control.XMonad.XWriter where

import Data.Kind
import Control.Arrow

import Control.XApplicative
import Control.XMonad

-- |Indexed Writer monad that uses @i -> j@ as the indexed monoid.
--
-- Roughly along the lines of <https://mail.haskell.org/pipermail/haskell-cafe/2015-March/118793.html>
type XWriter :: Type -> Type -> Type -> Type
data XWriter i j a = XWriter
  { runXWriter :: (i -> j, a)
  }

instance Functor (XWriter i j) where
  fmap f x = XWriter $ second f $ runXWriter x

instance XApplicative XWriter where
  xpure x = XWriter (id, x)
  (XWriter (fw, f)) <*>: (XWriter (xw, x)) = XWriter (xw . fw, f x)

instance XMonad XWriter where
  (XWriter (mw, m)) >>=: f = XWriter (fw . mw, fv)
    where
      XWriter (fw, fv) = f m

tell :: (i -> j) -> XWriter i j ()
tell f = XWriter (f, ())
