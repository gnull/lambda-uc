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
{-# LANGUAGE QualifiedDo #-}

module GADTApproach where

import Prelude hiding ((>>=), return)
import Control.XFreer
import Control.XMonad
import qualified Control.XMonad.Do as M

import Data.Kind (Type)

data CryptoActions (bef :: Bool) (aft :: Bool) (a :: Type) where
  RecvAction :: (String -> a) -> CryptoActions False True a
  SendAction :: String -> a -> CryptoActions True False a
  RandAction :: (Bool -> a) -> CryptoActions bef aft a

instance Functor (CryptoActions bef aft) where
  fmap f (RecvAction cont) = RecvAction $ f . cont
  fmap f (SendAction m x) = SendAction m $ f x
  fmap f (RandAction cont) = RandAction $ f . cont

type CryptoMonad bef aft = XFree CryptoActions bef aft

recv :: CryptoMonad False True String
recv = xfree $ RecvAction id

send :: String -> CryptoMonad True False ()
send m = xfree $ SendAction m ()

test :: String -> CryptoMonad True True String
test s = M.do
  send s
  recv

data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

data UnknownAfter bef a = forall b. UnknownAfter (SBool b) (CryptoMonad bef b a)

-- maybeSends :: Bool -> (forall b. CryptoMonad True b (SBool b) -> a) -> a
-- maybeSends True cont = cont $ send "hello" >>: xreturn SFalse
-- maybeSends False cont = cont $ xreturn STrue

maybeSends :: Bool -> UnknownAfter True ()
maybeSends True = UnknownAfter SFalse $ send "hello"
maybeSends False = UnknownAfter STrue $ pure ()

-- testFail :: CryptoMonad False False ()
-- testFail = send "hey"

hey :: IO ()
hey = putStrLn "hello"
