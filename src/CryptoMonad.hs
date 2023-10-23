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

module CryptoMonad where

import Data.Kind (Type)

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

data HeteroList f (types :: [Type]) where
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

data SomeMessage xs where
  SomeMessage :: InList x xs -> x -> SomeMessage xs

-- domain-specific definitions

data CryptoActions (send :: [Type]) (recv :: [Type]) a where
    ReceiveAnyAction :: (SomeMessage recv -> a) -> CryptoActions send recv a
    ReceiveAction :: InList b recv -> (b -> a) -> CryptoActions send recv a
    SendAction :: InList b send -> b -> a -> CryptoActions send recv a

instance Functor (CryptoActions send recv) where
    fmap f (ReceiveAnyAction g) = ReceiveAnyAction (f . g)
    fmap f (ReceiveAction i g) = ReceiveAction i (f . g)
    fmap f (SendAction i b a) = SendAction i b $ f a

-- wrappers

type CryptoMonad send recv = Free (CryptoActions send recv)

recvAny :: CryptoMonad send recv (SomeMessage recv)
recvAny = liftF (ReceiveAnyAction id)

recv :: InList b recv -> CryptoMonad send recv b
recv i = liftF (ReceiveAction i id)

send :: InList b send -> b -> CryptoMonad send recv ()
send i b = liftF (SendAction i b ())

pattern Alice :: () => (xs ~ (x : xs1)) => InList x xs
pattern Alice = Here
pattern Bob :: () => (xs ~ (y : xs1), xs1 ~ (x : xs2)) => InList x xs
pattern Bob = There Here
pattern Charlie :: () => (xs ~ (y1 : xs1), xs1 ~ (y2 : xs2), xs2 ~ (x : xs3)) => InList x xs
pattern Charlie = There (There Here)

-- usage

data BobAlgo = BobAlgo (CryptoMonad [Int, Void, BobAlgo] [Bool, Void, String] Bool)

-- | Keep running an operation until it becomes a 'Just', then return the value
--   inside the 'Just' as the result of the overall loop.
untilJustM :: Monad m => m (Maybe a) -> m a
untilJustM act = do
    res <- act
    case res of
        Just r  -> pure r
        Nothing -> untilJustM act

alg1 :: CryptoMonad [Int, Void, BobAlgo] [Bool, Void, String] Bool
alg1 = do str <- recv Charlie
          send Alice $ length str
          send Charlie $ BobAlgo alg1
          recv Alice

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

-- This is not a good idea. I must add an extra constructor for CryptoActions
-- if I want to hide parties in a clean way
hidingRecvParty :: CryptoMonad send recv a -> CryptoMonad send (x:recv) a
hidingRecvParty (Pure x) = Pure x
hidingRecvParty (Free (ReceiveAnyAction f))
  = Free
  $ ReceiveAnyAction
  $ \(SomeMessage (There i) x) -> hidingRecvParty $ f (SomeMessage i x)
hidingRecvParty (Free (ReceiveAction i f))
  = Free
  $ ReceiveAction (There i) (hidingRecvParty . f)
hidingRecvParty (Free (SendAction i m a))
  = Free
  $ SendAction i m
  $ hidingRecvParty a

-- the original idea

class InteractWithBob m v | m -> v where
    recvBob :: m v
    sendBob :: v -> m ()

-- instance InteractWithBob (CryptoMonad (Alice : v : xs) (Alice : v : xs')) v where
--     recvBob = recv bob
--     sendBob = send bob
