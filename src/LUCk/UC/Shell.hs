module LUCk.UC.Shell where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Control.Arrow (second)

-- import Control.XMonad.Trans

import LUCk.Syntax
import LUCk.Types

import qualified Data.HList as HList

import LUCk.UC.Core

import qualified Data.Map.Strict as Map

multiSidIdealShell :: forall sid x y sids down rest.
                 KnownLenD sids
              -> SameLenD sids down
              -> (sid -> SingleSidIdeal (x :> y) sids down)
              -> MultSidIdeal rest sid (x :> y) sids down
multiSidIdealShell len lenPrf impl = helper Map.empty
  where
    helper :: Map.Map (HList SomeOrd (sid:rest)) (SingleSidIdeal (x :> y) sids down)
           -> MultSidIdeal rest sid (x :> y) sids down
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
               -> SomeTxMess (PingSendPort : Marked Pid (y :> x) : ZipMapPidMarked sids down)
               -> AsyncT (PingSendPort : PidSidIface (sid:rest) (y :> x) : PidSidIfaceList (sid:rest) sids down)
                         NextSend NextRecv ()
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

type family MapConcat l r ports where
  MapConcat _ _ '[] = '[]
  MapConcat l r ((HListPair SomeOrd lx rx) :> (HListPair SomeOrd ly ry) : ports)
    = (HListPair SomeOrd (Concat l lx) (Concat r rx)) :> (HListPair SomeOrd (Concat l ly) (Concat r ry))
      : MapConcat l r ports

spawnOnDemand :: forall l r ports.
                 KnownHPPortsD SomeOrd ports
              -> KnownLenD l
              -> KnownLenD r
              -> ((HListPair SomeOrd l r) -> AsyncT ports NextRecv NextRecv Void)
              -> AsyncT (MapConcat l r ports) NextRecv NextRecv Void
spawnOnDemand n lLen rLen impl = helper Map.empty
  where
    helper :: Map.Map (HList SomeOrd l, HList SomeOrd r) (AsyncT ports NextRecv NextRecv Void)
           -> AsyncT (MapConcat l r ports) NextRecv NextRecv Void
    helper states = M.do
      (l, m) <- unwrapMess n lLen rLen <$> recvAny
      let st = Map.findWithDefault (impl l) l states
      st' <- ($ m) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
      (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
      sendMess $ wrapMess n l resp
      helper $ Map.insert l st'' states

    wrapMess :: forall ports'. KnownHPPortsD SomeOrd ports'
             -> (HList SomeOrd l, HList SomeOrd r)
             -> SomeTxMess ports'
             -> SomeTxMess (MapConcat l r ports')
    wrapMess len l (SomeTxMess i m) = inListMatch len i $ \Refl ->
      SomeTxMess (wrapInList len i) (l +++ m)

    inListMatch :: KnownHPPortsD SomeOrd ports'
                -> InList ports' p
                -> (forall lx rx ly ry.
                     ((HList SomeOrd lx, HList SomeOrd rx) :> (HList SomeOrd ly, HList SomeOrd ry) :~: p ) -> a)
                -> a
    inListMatch KnownHPPortsZ contra _ = case contra of {}
    inListMatch (KnownHPPortsS n') i cont = case i of
      Here -> cont Refl
      There i' -> inListMatch n' i' $ cont

    wrapInList :: forall ports' lx rx ly ry.
                  KnownHPPortsD SomeOrd ports'
               -> InList ports' ((HList SomeOrd lx, HList SomeOrd rx) :> (HList SomeOrd ly, HList SomeOrd ry))
               -> InList (MapConcat l r ports')
                         ((HList SomeOrd (Concat l lx), HList SomeOrd (Concat r rx))
                           :> (HList SomeOrd (Concat l ly), HList SomeOrd (Concat r ry)))
    wrapInList KnownHPPortsZ = \case {}
    wrapInList (KnownHPPortsS n') = \case
      Here -> Here
      (There i') -> There $ wrapInList n' i'

    unwrapMess :: forall ports'.
                  KnownHPPortsD SomeOrd ports'
               -> KnownLenD l
               -> KnownLenD r
               -> SomeRxMess (MapConcat l r ports')
               -> ((HList SomeOrd l, HList SomeOrd r), SomeRxMess ports')
    unwrapMess len lLen rLen = case len of
      KnownHPPortsZ -> \(SomeRxMess contra _) -> case contra of {}
      KnownHPPortsS n' -> \case
        (SomeRxMess i fs) -> case i of
          Here -> let
              (f, s) = fs
              (fl, fr) = splitHList (knownLenToSplit lLen) f
              (sl, sr) = splitHList (knownLenToSplit rLen) s
            in ((fl, sl), SomeRxMess Here (fr, sr))
          There i' -> second someRxMessThere $ unwrapMess n' lLen rLen $ SomeRxMess i' fs

knownLenToSplit :: KnownLenD p
                -> ListSplitD (Concat p s) p s
knownLenToSplit KnownLenZ = SplitHere
knownLenToSplit (KnownLenS i) = SplitThere $ knownLenToSplit i

splitHList :: ListSplitD l p s
           -> HList f l
           -> (HList f p, HList f s)
splitHList SplitHere l = (HNil, l)
splitHList (SplitThere i) (HCons x xs) = (HCons x p, s)
  where (p, s) = splitHList i xs

someRxMessThere :: SomeRxMess ports'
                -> SomeRxMess (x : ports')
someRxMessThere (SomeRxMess i m) = SomeRxMess (There i) m

-- multiSidRealToIdeal :: forall sids down rest sid x y.
--                        KnownLenD sids
--                     -> SameLenD sids down
--                     -> (Pid -> MultSidReal rest sid (x :> y) sids down)
--                     -> MultSidIdeal rest sid (x :> y) sids down
-- multiSidRealToIdeal len lenPrf impl = helper Map.empty
  -- where
  --   helper :: Map.Map Pid (MultSidReal rest sid (x :> y) sids down)
  --          -> MultSidIdeal rest sid (x :> y) sids down
  --   helper states = M.do
  --     (l, m) <- unwrapMess <$> recvAny
  --     let st = Map.findWithDefault (impl l) l states
  --     st' <- ($ m) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
  --     (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
  --     sendMess $ wrapMess l resp
  --     helper $ Map.insert l st'' states

  --   unwrapMess
  --     :: SomeRxMess
  --            (PingSendPort
  --               : ((HList SomeOrd (Pid : sid : rest), y) :> (HList SomeOrd (Pid : sid : rest), x))
  --               : PidSidIfaceList (sid : rest) sids down)
  --          -> (Pid,
  --              SomeRxMess
  --                (PingSendPort
  --                   : ((HList SomeOrd (sid : rest), y) :> (HList SomeOrd (sid : rest), x))
  --                   : SidIfaceList (sid : rest) sids down))
  --   unwrapMess (SomeRxMess i m) = case i of
  --     Here -> case m of {}
  --     There Here -> case m of
  --       (HCons (SomeOrd pid) sidRest, m') -> (pid, SomeRxMess (There Here) (sidRest, m'))
  --     There2 i' -> second (someRxMessThere . someRxMessThere) $ unwrapPidSidIfaceList i' m

  --   unwrapPidSidIfaceList :: InList (PidSidIfaceList (sid : rest) sids down) p
  --                         -> PortRxType p
  --                         -> (Pid, SomeRxMess (SidIfaceList (sid : rest) sids down))
  --   unwrapPidSidIfaceList = _

  --   wrapMess
  --     :: Pid
  --     -> SomeTxMess
  --          (PingSendPort
  --             : ((HList SomeOrd (sid : rest), y) :> (HList SomeOrd (sid : rest), x))
  --             : SidIfaceList (sid : rest) sids down)
  --     -> SomeTxMess
  --          (PingSendPort
  --             : ((HList SomeOrd (Pid : sid : rest), y) :> (HList SomeOrd (Pid : sid : rest), x))
  --             : PidSidIfaceList (sid : rest) sids down)
  --   wrapMess = _


multiSidRealShell :: forall sid x y sids down rest.
                 KnownLenD sids
              -> SameLenD sids down
              -> (Pid -> sid -> SingleSidReal (x :> y) sids down)
              -> Pid -> MultSidReal rest sid (x :> y) sids down
multiSidRealShell len lenPrf impl pid = helper Map.empty
  where
    helper :: Map.Map (HList SomeOrd (sid:rest)) (SingleSidReal (x :> y) sids down)
           -> MultSidReal rest sid (x :> y) sids down
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
               -> SomeTxMess (PingSendPort : y :> x : ZipMarked sids down)
               -> AsyncT (PingSendPort : SidIface (sid:rest) (y :> x) : SidIfaceList (sid:rest) sids down)
                         NextSend NextRecv ()
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
