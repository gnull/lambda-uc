{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ExistentialQuantification #-}

module GADTApproach where

import Data.Kind (Type)
import Data.Void (Void)

type family Not (t :: Bool) where
  Not True = False
  Not False = True

type family ToType (t :: Bool) where
  ToType True = ()
  ToType False = Void

data Free (bef :: Bool) (aft :: Bool) (f :: Bool -> Bool -> Type -> Type) (a :: Type) where
  Pure :: a -> Free x x f a
  Free :: f bef x (Free x aft f a) -> Free bef aft f a

data CryptoActions (bef :: Bool) (aft :: Bool) (a :: Type) where
  RecvAction :: (String -> a) -> CryptoActions True False a
  SendAction :: String -> a -> CryptoActions False True a
  RandAction :: (Bool -> a) -> CryptoActions bef aft a

instance Functor (CryptoActions bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m x) = SendAction m $ f x
  fmap f (RandAction cont) = RandAction $ f . cont

type CryptoMonad bef aft = Free bef aft CryptoActions

bind :: CryptoMonad bef x a -> (a -> CryptoMonad x aft b) -> CryptoMonad bef aft b
bind (Pure a) f = f a
bind (Free g) f = Free $ fmap (`bind` f) g

liftF :: CryptoActions bef aft a -> CryptoMonad bef aft a
liftF f = Free $ Pure <$> f

instance Functor (CryptoMonad bef aft) where
  fmap f (Pure x) = Pure $ f x
  fmap f (Free x) = Free $ fmap (fmap f) x
