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

-- data HeteroList f (types :: [*]) where
--     HNil :: HeteroList f '[]
--     HCons :: f t -> HeteroList f ts -> HeteroList f (t : ts)

data InList x xs where
    Here :: InList x (x : xs)
    There :: InList x xs -> InList x (y : xs)

-- heteroListGet :: HeteroList f types -> InList x types -> f x
-- heteroListGet (HCons x xs) Here = x
-- heteroListGet (HCons x xs) (There t) = heteroListGet xs t

-- data SomeIndex xs where
--     SomeIndex :: InList x xs -> SomeIndex xs

-- domain-specific definitions

data SomeMessage xs where
  SomeMessage :: InList x xs -> x -> SomeMessage xs

data CryptoActions (send :: [*]) (receive :: [*]) a where
    ReceiveAction :: (SomeMessage receive -> a) -> CryptoActions send receive a
    ReceiveOneAction :: InList b receive -> (b -> a) -> CryptoActions send receive a
    SendAction :: InList b send -> b -> a -> CryptoActions send receive a

instance Functor (CryptoActions send receive) where
    fmap f (ReceiveAction g) = ReceiveAction (f . g)
    fmap f (ReceiveOneAction i g) = ReceiveOneAction i (f . g)
    fmap f (SendAction i b a) = SendAction i b $ f a

-- wrappers

type CryptoMonad send receive = Free (CryptoActions send receive)

-- receiveAny :: CryptoMonad send receive (SomeMessage receive)
-- receiveAny = undefined

receive :: CryptoMonad send receive (SomeMessage receive)
receive = liftF (ReceiveAction id)

receiveOne :: InList b receive -> CryptoMonad send receive b
receiveOne i = liftF (ReceiveOneAction i id)

send :: InList b send -> b -> CryptoMonad send receive ()
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
alg1 = do str <- untilJustM $
            receive >>= \case
              SomeMessage Charlie x -> pure $ Just x
              SomeMessage _ _ -> pure Nothing
          send Alice $ (length :: String -> Int) str
          send Charlie $ BobAlgo alg1
          untilJustM $
            receive >>= \case
              SomeMessage Alice x -> pure $ Just x
              SomeMessage _ _ -> pure $ Nothing

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

-- instance InteractWithBob (CryptoMonad (Alice : v : xs) (Alice : v : xs')) v where
--     receiveBob = receive bob
--     sendBob = send bob
