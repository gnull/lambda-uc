{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module LUCk.UC.Core where

-- import qualified Control.XMonad.Do as M
-- import Control.XMonad
-- import Control.Arrow
-- import Control.XMonad.Trans

import LUCk.Syntax
import LUCk.Types

type OnlySendPort a = a :> Void
type OnlyRecvPort a = Void :> a
type PingSendPort = OnlySendPort ()
type PingRecvPort = OnlyRecvPort ()

type Marked :: Type -> Port -> Port
type family Marked u c where
  Marked u p = (u, PortTxType p) :> (u, PortRxType p)

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
type Proto up down = AsyncT (PingSendPort : PortDual up : down) NextRecv NextRecv Void

-- |A `Proto` where @up@ and @down@ interfaces are appropriately marked
-- with ESID and PID values to handle multiple sessions in one process.
--
-- This is used by `multiSidIdealShell` to implement multiple sessions of
-- `SingleSidIdeal` inside.
type MultSidIdeal rest sid up sids down =
  Proto (PidSidIface (sid:rest) up) (PidSidIfaceList (sid:rest) sids down)

-- |A `Proto` that implements a single session. The interface it provides
-- to its caller is maked only with PID values.
--
-- Use this with `multiSidIdealShell` to get a multi-session extension.
type SingleSidIdeal up sids down =
  Proto (Marked Pid up) (ZipMapPidMarked sids down)

-- |A `Proto` that implements a single process in a real (multi-session) protocol.
type MultSidReal rest sid up sids down =
  Proto (SidIface (sid:rest) up) (SidIfaceList (sid:rest) sids down)

-- |A `Proto` that implements a single process in a real (single-session) protocol.
type SingleSidReal up sids down =
  Proto up (ZipMarked sids down)

matchZipMapPidMarked :: KnownLenD sids
                  -> SameLenD sids down
                  -> InList (ZipMapPidMarked sids down) p
                  -> ( forall s x y.
                         PortInList (HList SomeOrd '[Pid, s], x) (HList SomeOrd '[Pid, s], y)
                                    (ZipMapPidMarked sids down)
                      -> (HList SomeOrd '[Pid, s], x) :> (HList SomeOrd '[Pid, s], y) :~: p
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
                   -> (SomeOrd s, x) :> (SomeOrd s, y) :~: p
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
                      -> (HList SomeOrd (Pid:s:rest), x) :> (HList SomeOrd (Pid:s:rest), y) :~: p
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
                      -> (HList SomeOrd (s:rest), x) :> (HList SomeOrd (s:rest), y) :~: p
                      -> a
                     )
                  -> a
matchSidIfaceList len lenPrf = \case
  Here -> case (len, lenPrf) of
    (KnownLenS _, SameLenCons _) -> \cont -> cont Here Refl
  There i -> case (len, lenPrf) of
    (KnownLenS j, SameLenCons k) -> \cont -> matchSidIfaceList j k i $ cont . There
