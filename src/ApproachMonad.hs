module ApproachMonad where

import Data.Kind (Type)

import Data.Functor ((<&>))

import qualified Control.Concurrent.STM.TChan as STM
import qualified Control.Concurrent.Async as A
import Control.Monad (msum)
import Control.Arrow (second, (***))
import qualified Control.Monad.STM as STM --also supplies instance MonadPlus STM

import Data.Type.Equality ((:~:)(Refl))

import HeterogenousList

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

-- domain-specific definitions

data CryptoActions (l :: [Type]) a where
    RecvAction :: (SomeSndMessage l -> a) -> CryptoActions l a
    SendAction :: SomeFstMessage l -> a -> CryptoActions l a

instance Functor (CryptoActions l) where
    fmap f (RecvAction g) = RecvAction (f . g)
    fmap f (SendAction m a) = SendAction m $ f a

-- wrappers

type CryptoMonad l = Free (CryptoActions l)

recvAny :: CryptoMonad l (SomeSndMessage l)
recvAny = liftF (RecvAction id)

-- |Waits for message from this specific party. Until it arrives, collect all
-- the messages from all other parties.
recvCollecting :: InList (a, b) l -> CryptoMonad l ([SomeSndMessage l], b)
recvCollecting i = do
  m@(SomeSndMessage j x) <- recvAny
  case areInListEqual i j of
    Nothing -> do
      (ms, res) <- recvCollecting i
      pure (m : ms, res)
    Just Refl -> pure ([], x)

-- |Same as @recvCollecting@, but drops the messages from other parties.
recvDropping :: InList (a, b) l -> CryptoMonad l b
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

-- -- |Same as @recvDropping@, but takes a list of valid senders to get messages from
-- recvOneOfDropping :: HeteroListP2 InList l is -> CryptoMonad l (SomeMessage (MapSnd is))
-- recvOneOfDropping i = do
--   m <- recvAny
--   case repackMessage i m of
--     Nothing -> recvOneOfDropping i
--     Just m' -> pure m'

sendSomeMess :: SomeFstMessage l -> CryptoMonad l ()
sendSomeMess m = liftF (SendAction m ())

send :: InList (b, a) l -> b -> CryptoMonad l ()
send i b = sendSomeMess $ SomeFstMessage i b

-- usage

data BobAlgo = BobAlgo (CryptoMonad [(Int, Bool), (Void, Void), (BobAlgo, String)] Bool)

alg1 :: CryptoMonad [(Int, Bool), (Void, Void), (BobAlgo, String)] Bool
alg1 = do str <- recvDropping charlie
          send alice $ length str
          send charlie $ BobAlgo alg1
          recvDropping alice
  where
    alice = Here
    bob = There Here
    charlie = There (There Here)

-- zipped version for when there's exactly one interface per person

type family Fst p where
    Fst (a, b) = a

type family Snd p where
    Snd (a, b) = b

type family MapFst xs where
    MapFst '[] = '[]
    MapFst (p : xs) = Fst p : MapFst xs

type family MapSnd xs where
    MapSnd '[] = '[]
    MapSnd (p : xs) = Snd p : MapSnd xs

type family Swap p where
    Swap ((,) x y) = (,) y x

-- type CryptoMonad' people = CryptoMonad (MapFst people) (MapSnd people)

-- send' :: InList (a, b) l -> a -> CryptoMonad l ()
-- send' i m = send (inListFst i) m

-- heteroListP2mapSnd :: HeteroListP2 InList l is -> HeteroListP2 InList (MapSnd l) (MapSnd is)
-- heteroListP2mapSnd HNilP2 = HNilP2
-- heteroListP2mapSnd (HConsP2 x xs) = HConsP2 (inListSnd x) (heteroListP2mapSnd xs)

-- recvOneOfDropping' :: HeteroListP2 InList l is -> CryptoMonad l (SomeMessage is)
-- recvOneOfDropping' i = recvOneOfDropping $ inListSnd i

-- recvDropping' :: InList (a, b) l -> CryptoMonad l b
-- recvDropping' i = recvDropping $ inListSnd i

inListFst :: InList ((,) a b) l -> InList a (MapFst l)
inListFst Here = Here
inListFst (There x) = There $ inListFst x

inListSnd :: InList ((,) a b) l -> InList b (MapSnd l)
inListSnd Here = Here
inListSnd (There x) = There $ inListSnd x

alg1' :: CryptoMonad [(Int, Bool), (Void, Void), (BobAlgo, String)] Bool
alg1' = alg1

-- |Returns @Left (x, f)@ if the underlying monad has received message x
-- intended for the hidden party. The f returned is the remaining computation
-- tail. You can handle the x yourself and then continues executing the
-- remaining f if you wish to.
--
-- Returns @Right a@ if the simulated computation exited successfully (and all
-- arrived messages were ok) with result @a@.
hidingParty
  :: CryptoMonad l a
  -> CryptoMonad ((x, y):l) (Either (y, CryptoMonad l a) a)
hidingParty (Pure x) = Pure $ Right x
hidingParty y@(Free (RecvAction f))
  = Free
  $ RecvAction
  $ \case
    (SomeSndMessage Here x) -> Pure $ Left (x, y)
    (SomeSndMessage (There i) x) -> hidingParty $ f (SomeSndMessage i x)
hidingParty (Free (SendAction (SomeFstMessage i m) a))
  = Free
  $ SendAction (SomeFstMessage (There i) m)
  $ hidingParty a

-- Interpretation of the CryptoMonad

data TwoChans t where
  TwoChans :: STM.TChan a -> STM.TChan b -> TwoChans (a, b)

runSTM :: HeteroList TwoChans l
    -> CryptoMonad l a
    -> IO a
runSTM l = \case
  Pure x -> pure x
  Free (RecvAction f) -> do
    let chans = homogenize (\i (TwoChans _ r) -> SomeSndMessage i <$> STM.readTChan r) l
    m <- STM.atomically $ msum chans
    runSTM l $ f m
  Free (SendAction (SomeFstMessage i m) a) -> do
    STM.atomically $ do
      let (TwoChans s _) = heteroListGet l i
      STM.writeTChan s m
    runSTM l a

type VoidInterface = (Void, Void)
type AliceBobInterface = (String, Int)

-- aliceName = Here

alice :: InList AliceBobInterface l -> CryptoMonad l Int
alice bobName = do
  -- let bobRecv = inListSnd bobName
  send bobName "alice to bob string"
  recvDropping bobName

bob :: InList (Swap AliceBobInterface) l -> CryptoMonad l String
bob aliceName = do
  s <- recvDropping aliceName
  send aliceName $ length s
  pure $ "got from Alice " ++ show s

test2STM :: IO (Int, String)
test2STM = do
    aToBChan <- STM.newTChanIO
    bToAChan <- STM.newTChanIO
    voidChan <- STM.newTChanIO
    let aliceCh = HCons (TwoChans voidChan voidChan) (HCons (TwoChans aToBChan bToAChan) HNil)
    let bobCh = HCons (TwoChans bToAChan aToBChan) (HCons (TwoChans voidChan voidChan) HNil)
    aliceA <- A.async $ runSTM aliceCh $ alice (There Here)
    bobA <- A.async $ runSTM bobCh $ bob Here
    A.waitBoth aliceA bobA

-- Single-threaded Cooperative Multitasking Interpretation of the Monad.
--
-- This is defined by the original UC paper

data Thread l a
  = ThDone a
  | ThRunning (SomeSndMessage l -> Free (CryptoActions l) a)

-- |Start a new thread and run it until it terminates or tries to recv. Collect
-- messages that it tries to send.
newThread :: CryptoMonad l a
          -> (Thread l a, [SomeFstMessage l])
newThread (Pure x) = (ThDone x, [])
newThread (Free (RecvAction a)) = (ThRunning a, [])
newThread (Free (SendAction m a)) = second (m:) $ newThread a

deliverThread :: SomeSndMessage l
              -> Thread l a
              -> (Thread l a, [SomeFstMessage l])
deliverThread _ t@(ThDone _) = (t, [])
deliverThread m (ThRunning a) = case a m of
  Pure x -> (ThDone x, [])
  a' -> newThread a'

type TransFunc s v = (s -> v -> (s, [v]))

stackMachine :: [v] -> TransFunc s v -> s -> s
stackMachine [] _ s = s
stackMachine (v:vs) f s = stackMachine (vs' ++ vs) f s'
  where
    (s', vs') = f s v

runCoop2PC :: CryptoMonad [(Void, Void), (a, b)] c
           -> CryptoMonad [(b, a), (Void, Void)] d
           -> (Maybe c, Maybe d)
runCoop2PC p1 p2 = (returned *** returned)
                 $ stackMachine (map Left m1 ++ map Right m2) f (t1, t2)
  where
    (t1, m1) = newThread p1
    (t2, m2) = newThread p2

    returned :: Thread l a -> Maybe a
    returned (ThDone a) = Just a
    returned (ThRunning _) = Nothing

    f :: TransFunc (Thread [(Void, Void), (a, b)] c, Thread [(b, a), (Void, Void)] d)
                   (Either (SomeFstMessage [(Void, Void), (a, b)]) (SomeFstMessage [(b, a), (Void, Void)]))
    f (th1, th2) = \case
      Left (SomeFstMessage i m) -> case i of
        There Here -> let
             (th2', ms) = deliverThread (SomeSndMessage Here m) th2
          in ((th1, th2'), map Right ms)
        Here -> case m of
        There (There contra) -> case contra of
      Right (SomeFstMessage i m) -> case i of
        Here -> let
             (th1', ms) = deliverThread (SomeSndMessage (There Here) m) th1
          in ((th1', th2), map Left ms)
        There Here -> case m of
        There (There contra) -> case contra of

test2Coop :: (Maybe Int, Maybe String)
test2Coop = runCoop2PC (alice $ There Here) (bob Here)
