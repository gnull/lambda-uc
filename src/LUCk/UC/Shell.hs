{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module LUCk.UC.Shell where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Control.Arrow

import Control.XMonad.Trans

import LUCk.Syntax
import LUCk.Types

import qualified Data.Map.Strict as Map

type OnlySendPort a = P a Void
type OnlyRecvPort a = P Void a
type PingSendPort = OnlySendPort ()
type PingRecvPort = OnlyRecvPort ()

type Marked :: Type -> Port -> Port
type family Marked u c where
  Marked u p = P (u, PortTxType p) (u, PortRxType p)

type MapMarked :: Type -> [Port] -> [Port]
type family MapMarked u l where
  MapMarked _ '[] = '[]
  MapMarked u (x:xs) = Marked u x : MapMarked u xs

type Pid = String

-- |An interface: send-receive types marked with `Pid`
type Iface sr = Marked Pid sr

-- |Extended SID.
--
-- It consists of two parts: @sid@ that is visible to the functionality itself
-- + @rest@ that encodes the list of sids of all callers, to ensure that each
-- such caller has a unique session of this functionalty.
type ESid sid rest = HList SomeOrd (sid:rest)

-- |A multi-session interface: send-receive pair marked with (E)SID and PID.
type PidSidIface sid sr = Marked (HList SomeOrd (Pid:sid)) sr

type SidIface sid sr = Marked (HList SomeOrd sid) sr

-- |A list of multi-session interfaces like `PidSidIface`
type PidSidIfaceList :: [Type] -> [Type] -> [Port] -> [Port]
type family PidSidIfaceList rest sids down where
  PidSidIfaceList _ '[] '[] = '[]
  PidSidIfaceList rest (s:ss) (p:ds) = PidSidIface (s:rest) p
                                  : PidSidIfaceList rest ss ds
  PidSidIfaceList _ _ _ = '[]

-- |A list of multi-session interfaces like `SidIface`
type SidIfaceList :: [Type] -> [Type] -> [Port] -> [Port]
type family SidIfaceList rest sids down where
  SidIfaceList _ '[] '[] = '[]
  SidIfaceList rest (s:ss) (p:ds) = SidIface (s:rest) p
                                  : SidIfaceList rest ss ds
  SidIfaceList _ _ _ = '[]

type family ZipMapPidMarked sids down where
  ZipMapPidMarked '[] '[] = '[]
  ZipMapPidMarked (s:ss) (p:ds) = Marked (HList SomeOrd '[Pid, s]) p
                             : ZipMapPidMarked ss ds
  ZipMapPidMarked _ _ = '[]

type family ZipMarked sids down where
  ZipMarked '[] '[] = '[]
  ZipMarked (s:ss) (p:ds) = Marked (SomeOrd s) p
                          : ZipMarked ss ds
  ZipMarked _ _ = '[]

data SomeOrd a where
  SomeOrd :: Ord a => a -> SomeOrd a

instance Eq (SomeOrd a) where
  SomeOrd x == SomeOrd y = x == y
instance Ord (SomeOrd a) where
  compare (SomeOrd x) (SomeOrd y) = compare x y

instance Eq (HList SomeOrd l) where
  HNil == HNil = True
  HCons x xs == HCons y ys = x == y && xs == ys
instance Ord (HList SomeOrd l) where
  compare HNil HNil = mempty
  compare (HCons x xs) (HCons y ys) = compare x y <> compare xs ys

-- |An interactive algorithm with that we use for defining ideal
-- functionalities and protocols.
--
-- Has the following interfaces.
--
-- - @up@ interface to its callers,
-- - @down@ interfaces to its subroutines,
-- - a single `PingSendPort` interface to yield control to the environment.
type Proto up down m = AsyncT (PingSendPort : PortSwap up : down) m NextRecv NextRecv Void

-- |A `Proto` where @up@ and @down@ interfaces are appropriately marked
-- with ESID and PID values to handle multiple sessions in one process.
--
-- This is used by `multiSidIdealShell` to implement multiple sessions of
-- `SingleSidIdeal` inside.
type MultSidIdeal rest sid up sids down m =
  Proto (PidSidIface (sid:rest) up) (PidSidIfaceList (sid:rest) sids down) m

-- |A `Proto` that implements a single session. The interface it provides
-- to its caller is maked only with PID values.
--
-- Use this with `multiSidIdealShell` to get a multi-session extension.
type SingleSidIdeal up sids down m =
  Proto (Marked Pid up) (ZipMapPidMarked sids down) m

-- |A `Proto` that implements a single process in a real (multi-session) protocol.
type MultSidReal rest sid up sids down m =
  Proto (SidIface (sid:rest) up) (SidIfaceList (sid:rest) sids down) m

-- |A `Proto` that implements a single process in a real (single-session) protocol.
type SingleSidReal up sids down m =
  Proto up (ZipMarked sids down) m

matchZipMapPidMarked :: KnownLenD sids
                  -> SameLenD sids down
                  -> InList (ZipMapPidMarked sids down) p
                  -> ( forall s x y.
                         PortInList (HList SomeOrd '[Pid, s], x) (HList SomeOrd '[Pid, s], y)
                                    (ZipMapPidMarked sids down)
                      -> P (HList SomeOrd '[Pid, s], x) (HList SomeOrd '[Pid, s], y) :~: p
                      -> a
                     )
                  -> a
matchZipMapPidMarked len lenPrf = \case
  Here -> case (len, lenPrf) of
    (KnownLenS _, SameLenCons _) -> \cont -> cont Here Refl
  There i -> case (len, lenPrf) of
    (KnownLenS j, SameLenCons k) -> \cont -> matchZipMapPidMarked j k i $ cont . There

matchZipMarked :: KnownLenD sids
               -> SameLenD sids down
               -> InList (ZipMarked sids down) p
               -> ( forall s x y.
                      PortInList (SomeOrd s, x) (SomeOrd s, y) (ZipMarked sids down)
                   -> P (SomeOrd s, x) (SomeOrd s, y) :~: p
                   -> a
                  )
               -> a
matchZipMarked len lenPrf = \case
  Here -> case (len, lenPrf) of
    (KnownLenS _, SameLenCons _) -> \cont -> cont Here Refl
  There i -> case (len, lenPrf) of
    (KnownLenS j, SameLenCons k) -> \cont -> matchZipMarked j k i $ cont . There

matchPidSidIfaceList :: forall rest sids down p a.
                     KnownLenD sids
                  -> SameLenD sids down
                  -> InList (PidSidIfaceList rest sids down) p
                  -> ( forall s x y.
                         PortInList (HList SomeOrd (Pid:s:rest), x) (HList SomeOrd (Pid:s:rest), y)
                                    (PidSidIfaceList rest sids down)
                      -> P (HList SomeOrd (Pid:s:rest), x) (HList SomeOrd (Pid:s:rest), y) :~: p
                      -> a
                     )
                  -> a
matchPidSidIfaceList len lenPrf = \case
  Here -> case (len, lenPrf) of
    (KnownLenS _, SameLenCons _) -> \cont -> cont Here Refl
  There i -> case (len, lenPrf) of
    (KnownLenS j, SameLenCons k) -> \cont -> matchPidSidIfaceList j k i $ cont . There

matchSidIfaceList :: forall rest sids down p a.
                     KnownLenD sids
                  -> SameLenD sids down
                  -> InList (SidIfaceList rest sids down) p
                  -> ( forall s x y.
                         PortInList (HList SomeOrd (s:rest), x) (HList SomeOrd (s:rest), y)
                                    (SidIfaceList rest sids down)
                      -> P (HList SomeOrd (s:rest), x) (HList SomeOrd (s:rest), y) :~: p
                      -> a
                     )
                  -> a
matchSidIfaceList len lenPrf = \case
  Here -> case (len, lenPrf) of
    (KnownLenS _, SameLenCons _) -> \cont -> cont Here Refl
  There i -> case (len, lenPrf) of
    (KnownLenS j, SameLenCons k) -> \cont -> matchSidIfaceList j k i $ cont . There

multiSidIdealShell :: forall sid x y sids down m rest.
                 Monad m
              => KnownLenD sids
              -> SameLenD sids down
              -> (sid -> SingleSidIdeal (P x y) sids down m)
              -> MultSidIdeal rest sid (P x y) sids down m
multiSidIdealShell len lenPrf impl = helper Map.empty
  where
    helper :: Map.Map (HList SomeOrd (sid:rest)) (SingleSidIdeal (P x y) sids down m)
           -> MultSidIdeal rest sid (P x y) sids down m
    helper m = M.do
      m' <- recvAny >>=: \case
        SomeRxMess Here contra -> case contra of {}
        SomeRxMess (There Here) (HCons pid (HCons sid rest), mess) -> M.do
          let (SomeOrd sid') = sid
              (SomeOrd pid') = pid
              k = HCons sid rest
              st = Map.findWithDefault (impl sid') k m
          st' <- ($ SomeRxMess (There Here) (pid', mess)) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
          (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
          handleResp k resp
          xreturn $ Map.insert k st'' m
        SomeRxMess (There2 i) mess -> M.do
          matchPidSidIfaceList @(sid:rest) len lenPrf i $ \_ Refl -> M.do
            let ix = There2 $ sidIfaceListToZipMapMarked @down @sids i len lenPrf
                (HCons pid (HCons s (HCons sid rest)), mess') = mess
                (SomeOrd sid') = sid
                k = HCons sid rest
                st = Map.findWithDefault (impl sid') k m
            st' <- ($ SomeRxMess ix (HListMatch2 pid s, mess')) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
            (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
            handleResp k resp
            xreturn $ Map.insert k st'' m
      helper m'

    handleResp :: HList SomeOrd (sid:rest)
               -> SomeTxMess (PingSendPort : Marked Pid (P y x) : ZipMapPidMarked sids down)
               -> AsyncT (PingSendPort : PidSidIface (sid:rest) (P y x) : PidSidIfaceList (sid:rest) sids down)
                         m NextSend NextRecv ()
    handleResp k = \case
      SomeTxMess Here () ->
        send Here ()
      SomeTxMess (There Here) (respPid, respMess) ->
        send (There Here) (HCons (SomeOrd respPid) k, respMess)
      SomeTxMess (There2 i) respMess -> matchZipMapPidMarked len lenPrf i $ \_ Refl ->
        let
          ix = There2 $ zipMapMarkedToSidIfaceList @down @sids i len lenPrf
          (HListMatch2 pid'' s, m') = respMess
        in send ix (HCons pid'' $ HCons s $ k, m')

    zipMapMarkedToSidIfaceList :: forall down' sids' s x' y'.
                                  PortInList (HList SomeOrd '[Pid, s], x') (HList SomeOrd '[Pid, s], y')
                                             (ZipMapPidMarked sids' down')
                               -> KnownLenD sids'
                               -> SameLenD sids' down'
                               -> PortInList (HList SomeOrd (Pid:s:sid:rest), x') (HList SomeOrd (Pid:s:sid:rest), y')
                                             (PidSidIfaceList (sid:rest) sids' down')
    zipMapMarkedToSidIfaceList = \case
      Here -> \case
        KnownLenS _ -> \case
          SameLenCons _ -> Here
      There i -> \case
        KnownLenS j -> \case
          SameLenCons k -> There $ zipMapMarkedToSidIfaceList i j k

    sidIfaceListToZipMapMarked :: forall down' sids' s x' y'.
                                  PortInList (HList SomeOrd (Pid:s:sid:rest), x') (HList SomeOrd (Pid:s:sid:rest), y')
                                             (PidSidIfaceList (sid:rest) sids' down')
                               -> KnownLenD sids'
                               -> SameLenD sids' down'
                               -> PortInList (HList SomeOrd '[Pid, s], x') (HList SomeOrd '[Pid, s], y')
                                             (ZipMapPidMarked sids' down')
    sidIfaceListToZipMapMarked = \case
      Here -> \case
        KnownLenS _ -> \case
          SameLenCons _ -> Here
      There i -> \case
        KnownLenS j -> \case
          SameLenCons k -> There $ sidIfaceListToZipMapMarked i j k

spawnOnDemand :: forall l ports m. (Ord l, Monad m)
              => PortsLenD ports
              -> (l -> AsyncT ports m NextRecv NextRecv Void)
              -> AsyncT (MapMarked l ports) m NextRecv NextRecv Void
spawnOnDemand n impl = helper Map.empty
  where
    helper :: Map.Map l (AsyncT ports m NextRecv NextRecv Void)
           -> AsyncT (MapMarked l ports) m NextRecv NextRecv Void
    helper states = M.do
      (l, m) <- unwrapMess n <$> recvAny
      let st = Map.findWithDefault (impl l) l states
      st' <- ($ m) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
      (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
      sendMess $ wrapMess l resp
      helper $ Map.insert l st'' states

    wrapMess :: forall ports'. l -> SomeTxMess ports'
             -> SomeTxMess (MapMarked l ports')
    wrapMess l (SomeTxMess i m) = SomeTxMess (wrapInList i) (l, m)

    wrapInList :: PortInList x y ports'
               -> PortInList (l, x) (l, y) (MapMarked l ports')
    wrapInList = \case
      Here -> Here
      There i' -> There $ wrapInList i'

    unwrapMess :: forall ports'.
                  PortsLenD ports'
               -> SomeRxMess (MapMarked l ports')
               -> (l, SomeRxMess ports')
    unwrapMess = \case
      PortsLenZ -> \(SomeRxMess contra _) -> case contra of {}
      PortsLenS n -> \(SomeRxMess i lm) -> case i of
        Here -> let (l, m) = lm in (l, SomeRxMess Here m)
        There i' -> second someRxMessThere $ unwrapMess n $ SomeRxMess i' lm

    someRxMessThere :: SomeRxMess ports'
                    -> SomeRxMess (x : ports')
    someRxMessThere (SomeRxMess i m) = SomeRxMess (There i) m

multiSidRealShell :: forall sid x y sids down m rest.
                 Monad m
              => KnownLenD sids
              -> SameLenD sids down
              -> (Pid -> sid -> SingleSidReal (P x y) sids down m)
              -> Pid -> MultSidReal rest sid (P x y) sids down m
multiSidRealShell len lenPrf impl pid = helper Map.empty
  where
    helper :: Map.Map (HList SomeOrd (sid:rest)) (SingleSidReal (P x y) sids down m)
           -> MultSidReal rest sid (P x y) sids down m
    helper m = M.do
      m' <- recvAny >>=: \case
        SomeRxMess Here contra -> case contra of {}
        SomeRxMess (There Here) (k, mess) -> M.do
          let (HCons sid _) = k
              (SomeOrd sid') = sid
              st = Map.findWithDefault (impl pid sid') k m
          st' <- ($ SomeRxMess (There Here) mess) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
          (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
          handleResp k resp
          xreturn $ Map.insert k st'' m
        SomeRxMess (There2 i) mess -> M.do
          matchSidIfaceList @(sid:rest) len lenPrf i $ \_ Refl -> M.do
            let ix = There2 $ sidIfaceListToZipMapMarked @down @sids i len lenPrf
                (HCons s (HCons sid rest), mess') = mess
                (SomeOrd sid') = sid
                k = HCons sid rest
                st = Map.findWithDefault (impl pid sid') k m
            st' <- ($ SomeRxMess ix (s, mess')) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
            (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
            handleResp k resp
            xreturn $ Map.insert k st'' m
      helper m'

    handleResp :: HList SomeOrd (sid:rest)
               -> SomeTxMess (PingSendPort : (P y x) : ZipMarked sids down)
               -> AsyncT (PingSendPort : SidIface (sid:rest) (P y x) : SidIfaceList (sid:rest) sids down)
                         m NextSend NextRecv ()
    handleResp k = \case
      SomeTxMess Here () ->
        send Here ()
      SomeTxMess (There Here) respMess ->
        send (There Here) (k, respMess)
      SomeTxMess (There2 i) respMess -> matchZipMarked len lenPrf i $ \i' Refl ->
        let
          ix = There2 $ zipMapMarkedToSidIfaceList @down @sids i' len lenPrf
          (s, m') = respMess
        in send ix (HCons s $ k, m')

    zipMapMarkedToSidIfaceList :: forall down' sids' s x' y'.
                                  PortInList (SomeOrd s, x') (SomeOrd s, y')
                                             (ZipMarked sids' down')
                               -> KnownLenD sids'
                               -> SameLenD sids' down'
                               -> PortInList (HList SomeOrd (s:sid:rest), x') (HList SomeOrd (s:sid:rest), y')
                                             (SidIfaceList (sid:rest) sids' down')
    zipMapMarkedToSidIfaceList = \case
      Here -> \case
        KnownLenS _ -> \case
          SameLenCons _ -> Here
      There i -> \case
        KnownLenS j -> \case
          SameLenCons k -> There $ zipMapMarkedToSidIfaceList i j k

    sidIfaceListToZipMapMarked :: forall down' sids' s x' y'.
                                  PortInList (HList SomeOrd (s:sid:rest), x') (HList SomeOrd (s:sid:rest), y')
                                             (SidIfaceList (sid:rest) sids' down')
                               -> KnownLenD sids'
                               -> SameLenD sids' down'
                               -> PortInList (SomeOrd s, x') (SomeOrd s, y')
                                             (ZipMarked sids' down')
    sidIfaceListToZipMapMarked = \case
      Here -> \case
        KnownLenS _ -> \case
          SameLenCons _ -> Here
      There i -> \case
        KnownLenS j -> \case
          SameLenCons k -> There $ sidIfaceListToZipMapMarked i j k
