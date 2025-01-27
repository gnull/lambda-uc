module LUCk.UC.Flatten where

import Data.Functor.Identity
import Data.Kind
import Control.Monad qualified as Monad

import Data.HList
import LUCk.Syntax
import LUCk.Syntax.Async
import LUCk.Syntax.Async.Eval

import LUCk.UC.Core

data PidMess a = PidMess Pid a
data SidMess s a = SidMess s a
newtype Sid s = Sid s
data SidPid s = SidPid s Pid

type family Flattened (s :: Type) where
  Flattened (HListPair '[sid] '[]) = Sid sid
  Flattened (HListPair '[sid] '[Pid]) = SidPid sid
  Flattened (HListPair '[] '[m]) = m
  Flattened (HListPair '[] '[Pid, m]) = PidMess m

type family MapFlattenedPorts (l :: [Port]) where
  MapFlattenedPorts '[] = '[]
  MapFlattenedPorts (x :> y : ts) = Flattened x :> Flattened y
                                  : MapFlattenedPorts ts

data FlattenableD s where
  FlattenableSid :: FlattenableD (HListPair '[sid] '[])
  FlattenableSidPid :: FlattenableD (HListPair '[sid] '[Pid])
  FlattenableMess :: FlattenableD (HListPair '[] '[m])
  FlattenablePidMess :: FlattenableD (HListPair '[] '[Pid, m])

class Flattenable s where
  getFlattenableD :: FlattenableD s
instance Flattenable (HListPair '[sid] '[]) where
  getFlattenableD = FlattenableSid
instance Flattenable (HListPair '[sid] '[Pid]) where
  getFlattenableD = FlattenableSidPid
instance Flattenable (HListPair '[] '[m]) where
  getFlattenableD = FlattenableMess
instance Flattenable (HListPair '[] '[Pid, m]) where
  getFlattenableD = FlattenablePidMess

flatten :: forall s. Flattenable s => s -> Flattened s
flatten = case getFlattenableD @s of
  FlattenableSid ->
    \(HListMatch1 (Identity sid), HNil) -> Sid sid
  FlattenableSidPid ->
    \(HListMatch1 (Identity sid), HListMatch1 (Identity pid)) -> SidPid sid pid
  FlattenableMess -> \(HNil, HListMatch1 (Identity m)) -> m
  FlattenablePidMess -> \(HNil, HListMatch2 (Identity pid) (Identity m)) -> PidMess pid m

unflatten :: forall s. Flattenable s => Flattened s -> s
unflatten = case getFlattenableD @s of
  FlattenableSid ->
    \(Sid sid) -> (HListMatch1 (Identity sid), HNil)
  FlattenableSidPid ->
    \(SidPid sid pid) -> (HListMatch1 (Identity sid), HListMatch1 (Identity pid))
  FlattenableMess ->
    \(m) -> (HNil, HListMatch1 (Identity m))
  FlattenablePidMess ->
    \(PidMess pid m) -> (HNil, HListMatch2 (Identity pid) (Identity m))

type family FlattenedUcProcess t where
  FlattenedUcProcess (a -> NoInitExec ports) =
    Flattened a -> NoInitExec (MapFlattenedPorts ports)

type SingleSidIdeal' sid adv up down = FlattenedUcProcess (SingleSidIdeal sid adv up down)
