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

type Pid = String

type family Concat2 l r p where
  -- Concat2 '[] '[] p = p
  Concat2 l r (HListPair lx rx :> HListPair ly ry)
    =    HListPair (Concat l lx) (Concat r rx)
      :> HListPair (Concat l ly) (Concat r ry)

type family MapConcat2 l r ports where
  -- MapConcat2 '[] '[] ports = ports
  MapConcat2 _ _ '[] = '[]
  MapConcat2 l r (p : ports)
    = Concat2 l r p : MapConcat2 l r ports

knownHPPortsAppendPid :: KnownHPPortsD down
                      -> KnownHPPortsD (MapConcat2 '[] '[Pid] down)
knownHPPortsAppendPid KnownHPPortsZ = KnownHPPortsZ
knownHPPortsAppendPid (KnownHPPortsS i) = KnownHPPortsS $ knownHPPortsAppendPid i

mapConcatCompL :: forall l r ports.
                  KnownHPPortsD ports
               -> MapConcat2 l '[] (MapConcat2 '[] r ports) :~: MapConcat2 l r ports
mapConcatCompL = \case
  KnownHPPortsZ -> Refl
  KnownHPPortsS i -> case mapConcatCompL @l @r i of
    Refl -> Refl

mapConcatId :: KnownHPPortsD ports
            -> MapConcat2 '[] '[] ports :~: ports
mapConcatId KnownHPPortsZ = Refl
mapConcatId (KnownHPPortsS i) = case mapConcatId i of
  Refl -> Refl

-- |An interactive algorithm with that we use for defining ideal
-- functionalities and protocols.
--
-- Has the following interfaces.
--
-- - @up@ interface to its callers,
-- - @down@ interfaces to its subroutines,
-- - a single `PingSendPort` interface to yield control to the environment.
type Proto l r up down =
  AsyncT (MapConcat2 l r ((PortDual up) : down))
         NextRecv NextRecv Void

-- |A `Proto` where @up@ and @down@ interfaces are appropriately marked
-- with ESID and PID values to handle multiple sessions in one process.
--
-- This is used by `multiSidIdealShell` to implement multiple sessions of
-- `SingleSidIdeal` inside.
type MultSidIdeal rest sid up down = Proto (sid:rest) '[Pid] up down

-- |A `Proto` that implements a single process in a real (multi-session) protocol.
type MultSidReal rest sid up down =
  HListPair '[] '[Pid] -> Proto (sid:rest) '[] up down

-- |A `Proto` that implements a single session. The interface it provides
-- to its caller is maked only with PID values.
--
-- Use this with `multiSidIdealShell` to get a multi-session extension.
type SingleSidIdeal sid up down =
  HListPair '[sid] '[] -> Proto '[] '[Pid] up down

-- |A `Proto` that implements a single process in a real (single-session) protocol.
type SingleSidReal sid up down =
  HListPair '[sid] '[Pid] -> Proto '[] '[] up down
