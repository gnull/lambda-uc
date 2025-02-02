{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module LUCk.UC.Core where

-- import qualified Control.XMonad.Do as M
-- import Control.XMonad
-- import Control.Arrow
-- import Control.XMonad.Trans

import LUCk.Syntax
import LUCk.Syntax.Async.Eval
import LUCk.Types

type HListPort x y = HListPair '[] '[x] :> HListPair '[] '[y]

type OnlySendPort a = HListPort a Void
type OnlyRecvPort a = HListPort Void a
type PingSendPort = OnlySendPort ()
type PingRecvPort = OnlyRecvPort ()

type Pid = String

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

type NoInitExec ports
  = ExecBuilder ExecIndexInit (ExecIndexSome ports InitAbsent) ()

type NoInitProc ports
  = AsyncT ports NextRecv NextRecv Void

-- |An interactive algorithm with that we use for defining ideal
-- functionalities and protocols.
--
-- Has the following interfaces.
--
-- - @up@ interface to its callers,
-- - @down@ interfaces to its subroutines,
-- - a single `PingSendPort` interface to yield control to the environment.
type UcExec l r adv up down =
  NoInitExec (UcProcessPorts l r adv up down)

type UcProc l r adv up down =
  NoInitProc (UcProcessPorts l r adv up down)

type UcProcessPorts l r adv up down =
  ( Concat2 l r PingSendPort
               : PortDual adv
               : MapConcat2 l r (PortDual up : down)
               )

-- |A `UcExec` where @up@ and @down@ interfaces are appropriately marked
-- with ESID and PID values to handle multiple sessions in one process.
--
-- This is used by `multiSidIdealShell` to implement multiple sessions of
-- `SingleSidIdeal` inside.
type MultSidIdeal rest sid adv up down = UcExec (sid:rest) '[Pid] (Concat2 (sid:rest) '[] adv) up down

-- |A `UcExec` that implements a single process in a real (multi-session) protocol.
type MultSidReal rest sid adv up down =
  HListPair '[] '[Pid] -> UcExec (sid:rest) '[] (Concat2 (sid:rest) '[] adv) up down

-- |A `UcExec` that implements a single session. The interface it provides
-- to its caller is maked only with PID values.
--
-- Use this with `multiSidIdealShell` to get a multi-session extension.
type SingleSidIdeal sid adv up down =
  HListPair '[sid] '[] -> UcExec '[] '[Pid] (Concat2 '[] '[] adv) up down

-- |A `UcExec` that implements a single process in a real (single-session) protocol.
type SingleSidReal sid adv up down =
  HListPair '[sid] '[Pid] -> UcExec '[] '[] (Concat2 '[] '[] adv) up down
