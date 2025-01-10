{-# LANGUAGE AllowAmbiguousTypes #-}

module LUCk.UC.Shell where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Data.Functor.Identity

import Control.Arrow (first, second, (***))

-- import Control.XMonad.Trans

import LUCk.Syntax
import LUCk.Types
import LUCk.Syntax.Async.Eval

import qualified Data.HList as HList

import LUCk.UC.Core

import qualified Data.Map.Strict as Map

idealToMultSid :: forall sid rest down x y.
                  ConstrAllD Ord (sid:rest)
               -> KnownHPPortsD down
               -> SingleSidIdeal sid (HListPort x y) (HListPort x y) down
               -> MultSidIdeal rest sid (HListPort x y) (HListPort x y) down
idealToMultSid restLen downLen f = case mapConcatCompL @(sid:rest) @'[Pid] downLen of
    Refl -> spawnOnDemand' restLen
                          ConstrAllNil
                          (KnownHPPortsS $ KnownHPPortsS $ KnownHPPortsS $ knownHPPortsAppendPid downLen)
                          (knownLenfromConstrAllD restLen)
                          getKnownLenPrf
                          $ \(l, r) -> f (hlistTakeHead l, r)

-- protoToFunc :: forall sid x y down.
--                KnownHPPortsD down
--             -> SingleSidReal sid (HListPort x y) (HListPort x y) down
--             -> SingleSidIdeal sid (HListPort x y) (HListPort x y) down
-- protoToFunc downLen f (sid, HNil) = case mapConcatId downLen of
--     Refl -> spawnOnDemand getConstrAllD
--                           getConstrAllD
--                           (KnownHPPortsS $ KnownHPPortsS $ KnownHPPortsS downLen)
--                           getKnownLenPrf
--                           getKnownLenPrf
--                           wrapper
--   where
--     wrapper :: HListPair '[] '[Pid] -> UcProcess '[] '[] (HListPort x y) (HListPort x y) down
--     wrapper (HNil, pid) = f (sid, pid)

realToMultSid :: forall sid rest down x y.
                 ConstrAllD Ord (sid:rest)
              -> KnownHPPortsD down
              -> SingleSidReal sid (HListPort x y) (HListPort x y) down
              -> MultSidReal rest sid (HListPort x y) (HListPort x y) down
realToMultSid restLen downLen f (HNil, pid) = case mapConcatId downLen of
    Refl -> spawnOnDemand' restLen
                          getConstrAllD
                          (KnownHPPortsS $ KnownHPPortsS $ KnownHPPortsS downLen)
                          (knownLenfromConstrAllD restLen)
                          getKnownLenPrf
                          wrapper
  where
    wrapper :: HListPair (sid:rest) '[] -> UcProcess '[] '[] (HListPort x y) (HListPort x y) down
    wrapper (HCons sid _, HNil) = f (HCons sid HNil, pid)
