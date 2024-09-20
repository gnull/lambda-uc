{-# LANGUAGE QuantifiedConstraints #-}

module Control.XMonad.Trans where

-- |Indexed monad transformer.
--
-- The inner monad @m@ is not indexed. See
-- [indexed](https://hackage.haskell.org/package/indexed-0.1.3/docs/src/Control-Monad-Indexed-Trans.html#IxMonadTrans)
-- for an analogous definition.
class (forall m i. Monad m => Monad (t m i i)) => XMonadTrans t where
  xlift :: Monad m => m a -> t m i i a 
