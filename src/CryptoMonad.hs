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

module CryptoMonad where

import Data.Kind (Type)

import Data.Functor.Identity (Identity)

import qualified Control.Concurrent.STM.TChan as STM
import qualified Control.Concurrent.Async as A
import Control.Monad (msum)
import qualified Control.Monad.STM as STM --also supplies instance MonadPlus STM

import Data.Type.Equality ((:~:)(Refl))

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

areInListEqual :: InList x xs -> InList y xs -> Maybe (x :~: y)
areInListEqual Here Here = Just Refl
areInListEqual (There a) (There b) = areInListEqual a b
areInListEqual _ _ = Nothing

heteroListGet :: HeteroList f types -> InList x types -> f x
heteroListGet (HCons x _) Here = x
heteroListGet (HCons _ xs) (There t) = heteroListGet xs t
heteroListGet HNil contra = case contra of

homogenize
  :: (forall x. InList x types -> f x -> a)
  -> HeteroList f types
  -> [a]
homogenize _ HNil = []
homogenize g (HCons x xs) = g Here x : homogenize (g . There) xs

data SomeIndex xs where
    SomeIndex :: InList x xs -> SomeIndex xs

data SomeMessage xs where
  SomeMessage :: InList x xs -> x -> SomeMessage xs

-- domain-specific definitions

data CryptoActions (send :: [Type]) (recv :: [Type]) a where
    RecvAction :: (SomeMessage recv -> a) -> CryptoActions send recv a
    SendAction :: InList b send -> b -> a -> CryptoActions send recv a

instance Functor (CryptoActions send recv) where
    fmap f (RecvAction g) = RecvAction (f . g)
    fmap f (SendAction i b a) = SendAction i b $ f a

-- wrappers

type CryptoMonad send recv = Free (CryptoActions send recv)

recvAny :: CryptoMonad send recv (SomeMessage recv)
recvAny = liftF (RecvAction id)

-- |Waits for message from this specific party. Until it arrives, collect all
-- the messages from all other parties.
recvCollecting :: InList b recv -> CryptoMonad send recv ([SomeMessage recv], b)
recvCollecting i = do
  m@(SomeMessage j x) <- recvAny
  case areInListEqual i j of
    Nothing -> do
      (ms, res) <- recvCollecting i
      pure (m : ms, res)
    Just Refl -> pure ([], x)

-- |Same as @recvCollecting@, but drops the messages from other parties.
recvDropping :: InList b recv -> CryptoMonad send recv b
recvDropping i = snd <$> recvCollecting i

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
alg1 = do str <- recvDropping Charlie
          send Alice $ length str
          send Charlie $ BobAlgo alg1
          recvDropping Alice

-- zipped version for when there's exactly one interface per person

type family MapFst xs where
    MapFst '[] = '[]
    MapFst ((,) a b : xs) = a : MapFst xs

type family MapSnd xs where
    MapSnd '[] = '[]
    MapSnd ((,) a b : xs) = b : MapSnd xs

type family Swap p where
    Swap ((,) x y) = (,) y x

type CryptoMonad' people = CryptoMonad (MapFst people) (MapSnd people)

type PartyMonad e f parties = CryptoMonad' (e:f:parties)

alg1' :: CryptoMonad' [(Int, Bool), (Void, Void), (BobAlgo, String)] Bool
alg1' = alg1

-- |Returns @Left (x, f)@ if the underlying monad has received message x
-- intended for the hidden party. The f returned is the remaining computation
-- tail. You can handle the x yourself and then continues executing the
-- remaining f if you wish to.
--
-- Returns @Right a@ if the simulated computation exited successfully (and all
-- arrived messages were ok) with result @a@.
hidingRecvParty
  :: CryptoMonad send recv a
  -> CryptoMonad send (x:recv) (Either (x, CryptoMonad send recv a) a)
hidingRecvParty (Pure x) = Pure $ Right x
hidingRecvParty y@(Free (RecvAction f))
  = Free
  $ RecvAction
  $ \case
    (SomeMessage Here x) -> Pure $ Left (x, y)
    (SomeMessage (There i) x) -> hidingRecvParty $ f (SomeMessage i x)
hidingRecvParty (Free (SendAction i m a))
  = Free
  $ SendAction i m
  $ hidingRecvParty a

-- Interpretation of the CryptoMonad

runSTM :: HeteroList STM.TChan send
    -> HeteroList STM.TChan receive
    -> CryptoMonad send receive a
    -> IO a
runSTM s r = \case
  Pure x -> pure x
  Free (RecvAction f) -> do
    let chans = homogenize (\i c -> SomeMessage i <$> STM.readTChan c) r
    m <- STM.atomically $ msum chans
    runSTM s r $ f m
  Free (SendAction i m a) -> do
    STM.atomically $ STM.writeTChan (heteroListGet s i) m
    runSTM s r a

test :: String -> String -> IO (Int, String)
test a b = do
    aToBChan <- STM.newTChanIO
    bToAChan <- STM.newTChanIO
    let aToB = HCons aToBChan HNil
    let bToA = HCons bToAChan HNil
    aliceA <- A.async $ runSTM aToB bToA alice
    bobA <- A.async $ runSTM bToA aToB bob
    A.waitBoth aliceA bobA
  where
    alice :: CryptoMonad' '[(String, Int)] Int
    alice = do
      send Here a
      recvAny >>= \case
        SomeMessage Here x -> pure x
        SomeMessage (There contra) _ -> case contra of
    bob :: CryptoMonad' '[(Int, String)] String
    bob = do
      s <- recvDropping Here
      send Here $ length s
      pure $ "got from Alice " ++ show s ++ " while my input is " ++ show b
