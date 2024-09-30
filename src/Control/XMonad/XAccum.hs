module Control.XMonad.XAccum where

import Data.Kind
import Control.Arrow

import Control.XApplicative
import Control.XMonad

-- |Indexed Accumulator monad.
--
-- This is an indexed version of mtl's
-- [MonadAccum](https://hackage.haskell.org/package/mtl-2.3.1/docs/Control-Monad-Accum.html#t:MonadAccum).
-- Accumulator can be seen as a Writer with the extra capability of reading the
-- result of previus `tell`s. Or as State where modifications are limited to appends.
--
-- We fix the internal indexed monoid here to `->` for simplicity, as this is
-- the only one we need.
type XAccum :: Type -> Type -> Type -> Type
data XAccum i j a = XAccum
  { runXAccum :: i -> (j, a)
  }

instance Functor (XAccum i j) where
  fmap f x = XAccum $ \i -> second f $ runXAccum x i

instance XApplicative XAccum where
  xpure x = XAccum $ \i -> (i, x)
  f <*>: x = XAccum $ \i ->
    let (j, f') = runXAccum f i
        (k, x') = runXAccum x j
    in (k, f' x')

instance XMonad XAccum where
  m >>=: f = XAccum $ \i ->
    let (j, m') = runXAccum m i
        (k, f') = runXAccum (f m') j
    in (k, f')

add :: (i -> j) -> XAccum i j ()
add f = XAccum $ \i -> (f i, ())

look :: XAccum i i i
look = XAccum $ \i -> (i, i)
