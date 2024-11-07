module LUCk.UC.Shell where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Control.Arrow

import Control.XMonad.Trans

import LUCk.Syntax
import LUCk.Types

import LUCk.UC.Core

import qualified Data.Map.Strict as Map

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
