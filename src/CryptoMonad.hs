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

module CryptoMonad where

-- free monads

import Control.Monad (ap)
import Data.Void (Void)
data Free f a =
    Pure a
    | Free (f (Free f a))
    deriving Functor

instance Functor f => Applicative (Free f) where
    pure = Pure
    (<*>) = ap

instance Functor f => Monad (Free f) where
    Pure a >>= f = f a
    Free g >>= f = Free $ fmap (>>= f) g

liftF :: Functor f => f a -> Free f a
liftF f = Free $ pure <$> f

-- heterogenous lists

data HeteroList f (types :: [*]) where
    HNil :: HeteroList f '[]
    HCons :: f t -> HeteroList f ts -> HeteroList f (t : ts)

data InList x xs where
    Here :: InList x (x : xs)
    There :: InList x xs -> InList x (y : xs)

heteroListGet :: HeteroList f types -> InList x types -> f x
heteroListGet (HCons x xs) Here = x
heteroListGet (HCons x xs) (There t) = heteroListGet xs t

data SomeIndex xs where
    SomeIndex :: InList x xs -> SomeIndex xs

-- domain-specific definitions

data SomeMessage xs where
  SomeMessage :: InList x xs -> x -> SomeMessage xs

data CryptoActions (send :: [*]) (receive :: [*]) a where
    ReceiveAction :: (SomeMessage receive -> a) -> CryptoActions send receive a
    SendAction :: InList b send -> b -> a -> CryptoActions send receive a

instance Functor (CryptoActions send receive) where
    fmap f (ReceiveAction g) = ReceiveAction (f . g)
    fmap f (SendAction i b a) = SendAction i b $ f a

-- wrappers

type CryptoMonad send receive = Free (CryptoActions send receive)

-- receiveAny :: CryptoMonad send receive (SomeMessage receive)
-- receiveAny = undefined

receive :: CryptoMonad send receive (SomeMessage receive)
receive = liftF (ReceiveAction id)

send :: InList b send -> b -> CryptoMonad send receive ()
send i b = liftF (SendAction i b ())

alice = Here

bob = There Here

charlie = There $ There Here

-- usage

data BobAlgo = BobAlgo (CryptoMonad [Int, Void, BobAlgo] [Bool, Void, String] Bool)

alg1 :: CryptoMonad [Int, Void, BobAlgo] [Bool, Void, String] Bool
alg1 = do str <- receive charlie
          send alice $ length str
          send charlie $ BobAlgo alg1
          receive alice

-- zipped version for when there's exactly one interface per person

type family MapFst xs where
    MapFst '[] = '[]
    MapFst ((,) a b : xs) = a : MapFst xs

type family MapSnd xs where
    MapSnd '[] = '[]
    MapSnd ((,) a b : xs) = b : MapSnd xs

type CryptoMonad' people = CryptoMonad (MapFst people) (MapSnd people)

alg1' :: CryptoMonad' [(Int, Bool), (Void, Void), (BobAlgo, String)] Bool
alg1' = alg1

-- the original idea

class InteractWithBob m v | m -> v where
    receiveBob :: m v
    sendBob :: v -> m ()

instance InteractWithBob (CryptoMonad (alice : v : xs) (alice' : v : xs')) v where
    receiveBob = receive bob
    sendBob = send bob
