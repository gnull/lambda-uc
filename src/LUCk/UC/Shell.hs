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

type OnlySendChan a = '(a, Void)
type OnlyRecvChan a = '(Void, a)
type PingSendChan = OnlySendChan ()
type PingRecvChan = OnlyRecvChan ()

type Marked :: Type -> (Type, Type) -> (Type, Type)
type family Marked u c where
  Marked u p = '( (u, Fst p), (u, Snd p))

type MapMarked :: Type -> [(Type, Type)] -> [(Type, Type)]
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
type SidIface sid sr = Marked (HList SomeOrd (Pid:sid)) sr

-- |A list of multi-session interfaces like `SidIface`
type SidIfaceList :: [Type] -> [Type] -> [(Type, Type)] -> [(Type, Type)]
type family SidIfaceList rest sids down where
  SidIfaceList _ '[] '[] = '[]
  SidIfaceList rest (s:ss) (p:ds) = Marked (HList SomeOrd (Pid:s:rest)) p
                                  : SidIfaceList rest ss ds
  SidIfaceList _ _ _ = '[]

type family ZipMapMarked sids down where
  ZipMapMarked '[] '[] = '[]
  ZipMapMarked (s:ss) (p:ds) = Marked (HList SomeOrd '[Pid, s]) p
                             : ZipMapMarked ss ds
  ZipMapMarked _ _ = '[]

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

-- |An interactive algorithm with that defines an ideal functionality.
--
-- Has the following interfaces.
--
-- - @up@ interface to its callers,
-- - @down@ interfaces to its subroutines,
-- - a single `PingSendChan` interface to yield control to the environment.
type IdealFunc up down m = AsyncT (PingSendChan : ChanSwap up : down) m NextRecv NextRecv Void

-- |An `IdealFunc` where @up@ and @down@ interfaces are appropriately marked
-- with ESID and PID values to handle multiple sessions in one process.
--
-- This is used by `multiSidShell` to implement multiple sessions of
-- `SingleSidIdealFunc` inside.
type MultSidIdealFunc rest sid up sids down m =
  IdealFunc (SidIface (sid:rest) up) (SidIfaceList (sid:rest) sids down) m

-- |An `IdealFunc` that implements a single session. The interface it provides
-- to its caller is maked only with PID values.
--
-- Use this with `multiSidShell` to get a multi-session extension.
type SingleSidIdealFunc up sids down m =
  IdealFunc (Marked Pid up) (ZipMapMarked sids down) m

matchZipMapMarked :: KnownLenD sids
                  -> SameLenD sids down
                  -> InList (ZipMapMarked sids down) p
                  -> ( forall s x y.
                         InList (ZipMapMarked sids down)
                                '((HList SomeOrd '[Pid, s], x), (HList SomeOrd '[Pid, s], y))
                      -> '((HList SomeOrd '[Pid, s], x), (HList SomeOrd '[Pid, s], y)) :~: p
                      -> a
                     )
                  -> a
matchZipMapMarked len lenPrf = \case
  Here -> case (len, lenPrf) of
    (KnownLenS _, SameLenCons _) -> \cont -> cont Here Refl
  There i -> case (len, lenPrf) of
    (KnownLenS j, SameLenCons k) -> \cont -> matchZipMapMarked j k i $ cont . There

matchSidIfaceList :: forall rest sids down p a.
                     KnownLenD sids
                  -> SameLenD sids down
                  -> InList (SidIfaceList rest sids down) p
                  -> ( forall s x y.
                         InList (SidIfaceList rest sids down)
                               '((HList SomeOrd (Pid:s:rest), x), (HList SomeOrd (Pid:s:rest), y))
                      -> '((HList SomeOrd (Pid:s:rest), x), (HList SomeOrd (Pid:s:rest), y)) :~: p
                      -> a
                     )
                  -> a
matchSidIfaceList len lenPrf = \case
  Here -> case (len, lenPrf) of
    (KnownLenS _, SameLenCons _) -> \cont -> cont Here Refl
  There i -> case (len, lenPrf) of
    (KnownLenS j, SameLenCons k) -> \cont -> matchSidIfaceList j k i $ cont . There

multiSidShell :: forall sid x y sids down m rest.
                 Monad m
              => KnownLenD sids
              -> SameLenD sids down
              -> (sid -> SingleSidIdealFunc '(x, y) sids down m)
              -> MultSidIdealFunc rest sid '(x, y) sids down m
multiSidShell len lenPrf impl = helper Map.empty
  where
    helper :: Map.Map (HList SomeOrd (sid:rest)) (SingleSidIdealFunc '(x, y) sids down m)
           -> MultSidIdealFunc rest sid '(x, y) sids down m
    helper m = M.do
      m' <- recvAny >>=: \case
        SomeSndMessage Here contra -> case contra of {}
        SomeSndMessage (There Here) (HCons pid (HCons sid rest), mess) -> M.do
          let (SomeOrd sid') = sid
              (SomeOrd pid') = pid
              k = HCons sid rest
              st = Map.findWithDefault (impl sid') k m
          st' <- ($ SomeSndMessage (There Here) (pid', mess)) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
          (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
          handleResp k resp
          xreturn $ Map.insert k st'' m
        SomeSndMessage (There2 i) mess -> M.do
          matchSidIfaceList @(sid:rest) len lenPrf i $ \_ Refl -> M.do
            let ix = There2 $ sidIfaceListToZipMapMarked @down @sids i len lenPrf
                (HCons pid (HCons s (HCons sid rest)), mess') = mess
                (SomeOrd sid') = sid
                k = HCons sid rest
                st = Map.findWithDefault (impl sid') k m
            st' <- ($ SomeSndMessage ix (HListMatch2 pid s, mess')) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
            (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
            handleResp k resp
            xreturn $ Map.insert k st'' m
      helper m'

    handleResp :: HList SomeOrd (sid:rest)
               -> SomeFstMessage (PingSendChan : Marked Pid '(y, x) : ZipMapMarked sids down)
               -> AsyncT (PingSendChan : SidIface (sid:rest) '(y, x) : SidIfaceList (sid:rest) sids down)
                         m NextSend NextRecv ()
    handleResp k = \case
      SomeFstMessage Here () ->
        send Here ()
      SomeFstMessage (There Here) (respPid, respMess) ->
        send (There Here) (HCons (SomeOrd respPid) k, respMess)
      SomeFstMessage (There2 i) respMess -> matchZipMapMarked len lenPrf i $ \_ Refl ->
        let
          ix = There2 $ zipMapMarkedToSidIfaceList @down @sids i len lenPrf
          (HListMatch2 pid'' s, m') = respMess
        in send ix (HCons pid'' $ HCons s $ k, m')

    zipMapMarkedToSidIfaceList :: forall down' sids' s x' y'.
                                  InList (ZipMapMarked sids' down')
                                        '((HList SomeOrd '[Pid, s], x'), (HList SomeOrd '[Pid, s], y'))
                               -> KnownLenD sids'
                               -> SameLenD sids' down'
                               -> InList (SidIfaceList (sid:rest) sids' down')
                                        '((HList SomeOrd (Pid:s:sid:rest), x'), (HList SomeOrd (Pid:s:sid:rest), y'))
    zipMapMarkedToSidIfaceList = \case
      Here -> \case
        KnownLenS _ -> \case
          SameLenCons _ -> Here
      There i -> \case
        KnownLenS j -> \case
          SameLenCons k -> There $ zipMapMarkedToSidIfaceList i j k

    sidIfaceListToZipMapMarked :: forall down' sids' s x' y'.
                                  InList (SidIfaceList (sid:rest) sids' down')
                                        '((HList SomeOrd (Pid:s:sid:rest), x'), (HList SomeOrd (Pid:s:sid:rest), y'))
                               -> KnownLenD sids'
                               -> SameLenD sids' down'
                               -> InList (ZipMapMarked sids' down')
                                        '((HList SomeOrd '[Pid, s], x'), (HList SomeOrd '[Pid, s], y'))
    sidIfaceListToZipMapMarked = \case
      Here -> \case
        KnownLenS _ -> \case
          SameLenCons _ -> Here
      There i -> \case
        KnownLenS j -> \case
          SameLenCons k -> There $ sidIfaceListToZipMapMarked i j k
