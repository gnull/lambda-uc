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

module CryptoMonad where

import Data.Kind (Type)

import Data.Functor ((<&>))

import qualified Control.Concurrent.STM.TChan as STM
import qualified Control.Concurrent.Async as A
import Control.Monad (msum)
import Control.Arrow (second)
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

padMessageIndex :: SomeMessage ts -> SomeMessage (t : ts)
padMessageIndex (SomeMessage i' x') = SomeMessage (There i') x'

-- domain-specific definitions

data CryptoActions (send :: [Type]) (recv :: [Type]) a where
    RecvAction :: (SomeMessage recv -> a) -> CryptoActions send recv a
    SendAction :: SomeMessage send -> a -> CryptoActions send recv a

instance Functor (CryptoActions send recv) where
    fmap f (RecvAction g) = RecvAction (f . g)
    fmap f (SendAction m a) = SendAction m $ f a

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

data HeteroListP2 f a (types :: [Type]) where
    HNilP2 :: HeteroListP2 f a '[]
    HConsP2 :: f t a -> HeteroListP2 f a ts -> HeteroListP2 f a (t : ts)

-- |Allows for cleaner code than pattern-matching over @SomeMessage recv@, or
-- pairwise comparisons using @areInListEqual@
repackMessage :: HeteroListP2 InList recv is -> SomeMessage recv -> Maybe (SomeMessage is)
repackMessage HNilP2 _ = Nothing
repackMessage (HConsP2 i is) m@(SomeMessage j x) = case areInListEqual i j of
    Just Refl -> Just $ SomeMessage Here x
    Nothing -> padMessageIndex <$> repackMessage is m

-- |Same as @recvDropping@, but takes a list of valid senders to get messages from
recvOneOfDropping :: HeteroListP2 InList recv is -> CryptoMonad send recv (SomeMessage is)
recvOneOfDropping i = do
  m <- recvAny
  case repackMessage i m of
    Nothing -> recvOneOfDropping i
    Just m' -> pure m'

sendSomeMess :: SomeMessage send -> CryptoMonad send recv ()
sendSomeMess m = liftF (SendAction m ())

send :: InList b send -> b -> CryptoMonad send recv ()
send i b = sendSomeMess $ SomeMessage i b

-- usage

data BobAlgo = BobAlgo (CryptoMonad [Int, Void, BobAlgo] [Bool, Void, String] Bool)

alg1 :: CryptoMonad [Int, Void, BobAlgo] [Bool, Void, String] Bool
alg1 = do str <- recvDropping charlie
          send alice $ length str
          send charlie $ BobAlgo alg1
          recvDropping alice
  where
    alice = Here
    bob = There Here
    charlie = There (There Here)

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
hidingRecvParty (Free (SendAction m a))
  = Free
  $ SendAction m
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
  Free (SendAction (SomeMessage i m) a) -> do
    STM.atomically $ STM.writeTChan (heteroListGet s i) m
    runSTM s r a

type VoidInterface = (Void, Void)
type AliceBobInterface = (String, Int)

test2 :: String -> String -> IO (Int, String)
test2 a b = do
    aToBChan <- STM.newTChanIO
    bToAChan <- STM.newTChanIO
    voidChan <- STM.newTChanIO
    let aliceSend = HCons voidChan (HCons aToBChan HNil)
    let aliceRecv = HCons voidChan (HCons bToAChan HNil)
    let bobSend = HCons bToAChan (HCons voidChan HNil)
    let bobRecv = HCons aToBChan (HCons voidChan HNil)
    aliceA <- A.async $ runSTM aliceSend aliceRecv alice
    bobA <- A.async $ runSTM bobSend bobRecv bob
    A.waitBoth aliceA bobA
  where
    aliceName = Here
    bobName = There Here
    alice :: CryptoMonad' '[VoidInterface, AliceBobInterface] Int
    alice = do
      send bobName a
      m <- recvOneOfDropping (HConsP2 bobName HNilP2)
      case m of
        SomeMessage Here x -> pure x
        SomeMessage (There contra) _ -> case contra of
    bob :: CryptoMonad' '[Swap AliceBobInterface, VoidInterface] String
    bob = do
      s <- recvDropping aliceName
      send aliceName $ length s
      pure $ "got from Alice " ++ show s ++ " while my input is " ++ show b


-- Single-threaded Cooperative Multitasking Interpretation of the Monad.
--
-- This is defined by the original UC paper

data Thread send recv a
  = ThDone a
  | ThRunning (SomeMessage recv -> Free (CryptoActions send recv) a)

-- |Start a new thread and run it until it terminates or tries to recv. Collect
-- messages that it tries to send.
newThread :: CryptoMonad send recv a
          -> (Thread send recv a, [SomeMessage send])
newThread (Pure x) = (ThDone x, [])
newThread (Free (RecvAction a)) = (ThRunning a, [])
newThread (Free (SendAction m a)) = second (m:) $ newThread a

deliverThread :: SomeMessage recv
              -> Thread send recv a
              -> (Thread send recv a, [SomeMessage send])
deliverThread _ t@(ThDone _) = (t, [])
deliverThread m (ThRunning a) = case a m of
  Pure x -> (ThDone x, [])
  a' -> newThread a'
