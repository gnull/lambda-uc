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
import LUCk.UC.Flatten

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
    wrapper :: HListPair (sid:rest) '[] -> UcExec '[] '[] (HListPort x y) (HListPort x y) down
    wrapper (HCons sid _, HNil) = f (HCons sid HNil, pid)

newtype ActiveCorrReq state up down = ActiveCorrReq (state -> AsyncExT
     '[]
     ((() ':> Void)
        : ([Char] ':> ActiveCorrReq state up down)
        : MapFlattenedPorts
            (Concat2 '[] '[] (PortDual up) : MapConcat2 '[] '[] down))
     'NextSend
     'NextRecv
     Void)
type ActiveCorrResp = String

newtype ActiveCorrWithErasures sid state up down = ActiveCorrWithErasures
  { runActiveCorrWithErasures :: SidPid sid
                              -> state
                              -> SomeRxMess (NoAdvPorts up down)
                              -> PrAlgo (state, SomeTxMess (NoAdvPorts up down))
  }

activeCorruption :: forall up down state sid.
                    state
                 -> ActiveCorrWithErasures sid state up down
                 -> SingleSidReal' sid (HListPort (ActiveCorrReq state up down) ActiveCorrResp) up down
activeCorruption st f = SingleSidReal' $ \sidpid -> M.do
      recvAny >>=: \case
        SomeRxMess Here contra -> case contra of {}
        SomeRxMess (There Here) (ActiveCorrReq alg) -> alg st
        SomeRxMess (There2 i) m -> M.do
          (st', r) <- xlift (runActiveCorrWithErasures f sidpid st $ SomeRxMess (There i) m)
          sendMess $ case r of
            SomeTxMess Here r' -> SomeTxMess Here r'
            SomeTxMess (There i') r' -> SomeTxMess (There2 i') r'
          runSingleSigReal' (activeCorruption @up @down st' f) sidpid
