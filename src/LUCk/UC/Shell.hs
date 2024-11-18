module LUCk.UC.Shell where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Data.Functor.Identity

import Control.Arrow (second)

-- import Control.XMonad.Trans

import LUCk.Syntax
import LUCk.Types

import qualified Data.HList as HList

import LUCk.UC.Core

import qualified Data.Map.Strict as Map

type family MapConcat l r ports where
  MapConcat _ _ '[] = '[]
  MapConcat l r (HListPair lx rx :> HListPair ly ry : ports)
    =    HListPair (Concat l lx) (Concat r rx)
      :> HListPair (Concat l ly) (Concat r ry)
      : MapConcat l r ports

data ConstrAllD (c :: Type -> Constraint) (l :: [Type]) where
  ConstrAllNil :: ConstrAllD c '[]
  ConstrAllCons :: c t
                => ConstrAllD c l
                -> ConstrAllD c (t:l)

class ConstrAll c l where
  getConstrAllD :: ConstrAllD c l

instance ConstrAll c '[] where
  getConstrAllD = ConstrAllNil

instance (c t, ConstrAll c l) => ConstrAll c (t:l) where
  getConstrAllD = ConstrAllCons getConstrAllD

data HListShow l where
  HListShow :: ConstrAllD Ord l
            -> HList Identity l
            -> HListShow l

instance Eq (HListShow l) where
  x == y = compare x y == EQ

instance Ord (HListShow l) where
  compare (HListShow xPrf xs) (HListShow yPrf ys) = case (xs, xPrf, ys, yPrf) of
    (HNil, _, HNil, _) -> EQ
    (HCons x xs', ConstrAllCons xPrf', HCons y ys', ConstrAllCons yPrf') ->
         x `compare` y
      <> HListShow xPrf' xs' `compare` HListShow yPrf' ys'

spawnOnDemand :: forall l r ports.
                 ConstrAllD Ord l
              -> ConstrAllD Ord r
              -> KnownHPPortsD Identity ports
              -> KnownLenD l
              -> KnownLenD r
              -> ((HListPair l r) -> AsyncT ports NextRecv NextRecv Void)
              -> AsyncT (MapConcat l r ports) NextRecv NextRecv Void
spawnOnDemand lOrdPrf rOrdPrf n lLen rLen impl = helper Map.empty
  where
    helper :: Map.Map (HListShow l, HListShow r) (AsyncT ports NextRecv NextRecv Void)
           -> AsyncT (MapConcat l r ports) NextRecv NextRecv Void
    helper states = M.do
      (l, m) <- unwrapMess n lLen rLen <$> recvAny
      let k = let
            (x, y) = l
            in (HListShow lOrdPrf x, HListShow rOrdPrf y)
      let st = Map.findWithDefault (impl l) k states
      st' <- ($ m) . mayOnlyRecvVoidPrf <$> xlift (runTillRecv st)
      (resp, st'') <- mayOnlySendVoidPrf <$> xlift (runTillSend st')
      sendMess $ wrapMess n l resp
      helper $ Map.insert k st'' states

    wrapMess :: forall ports'. KnownHPPortsD Identity ports'
             -> (HListPair l r)
             -> SomeTxMess ports'
             -> SomeTxMess (MapConcat l r ports')
    wrapMess len l (SomeTxMess i m) = inListMatch len i $ \Refl ->
      SomeTxMess (wrapInList len i) (l +++ m)

    inListMatch :: KnownHPPortsD Identity ports'
                -> InList ports' p
                -> (forall lx rx ly ry.
                     (HListPair lx rx :> HListPair ly ry :~: p ) -> a)
                -> a
    inListMatch KnownHPPortsZ contra _ = case contra of {}
    inListMatch (KnownHPPortsS n') i cont = case i of
      Here -> cont Refl
      There i' -> inListMatch n' i' $ cont

    wrapInList :: forall ports' lx rx ly ry.
                  KnownHPPortsD Identity ports'
               -> InList ports' ((HList Identity lx, HList Identity rx) :> (HList Identity ly, HList Identity ry))
               -> InList (MapConcat l r ports')
                         (HListPair (Concat l lx) (Concat r rx)
                           :> HListPair (Concat l ly) (Concat r ry))
    wrapInList KnownHPPortsZ = \case {}
    wrapInList (KnownHPPortsS n') = \case
      Here -> Here
      (There i') -> There $ wrapInList n' i'

    unwrapMess :: forall ports'.
                  KnownHPPortsD Identity ports'
               -> KnownLenD l
               -> KnownLenD r
               -> SomeRxMess (MapConcat l r ports')
               -> ((HListPair l r), SomeRxMess ports')
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
