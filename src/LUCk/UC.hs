module LUCk.UC
  ( EnvProcess(..)
  , SubRespTree(..)
  , subRespEval
  )
 where

import Control.XMonad
import qualified Control.XMonad.Do as M

import Data.Functor

import LUCk.Syntax
import LUCk.Types

import LUCk.Syntax.Async
import LUCk.Syntax.Async.Eval
import LUCk.Syntax.Async.Eval.Internal

import LUCk.UC.Core
import LUCk.UC.Shell

type EnvProcess down res =
  ExecBuilder ExecIndexInit (ExecIndexSome '[PingRecvPort, down] (InitPresent res)) ()

-- |A tree of subroutine-respecting protocols.
--
-- A `SubRespTree m up` is either an ideal functionality or a protocol where
-- the required subroutine interfaces were filled with actual implementations
-- (and, therefore, are not required and not exposed by a type parameter
-- anymore).
data SubRespTree (up :: Port) where
  MkSubRespTree :: ExecBuilder ExecIndexInit (ExecIndexSome (PingSendPort : PortDual (x :> y) : down) InitAbsent) ()
                -> HList SubRespTree down
                -> SubRespTree (x :> y)

mergeSendPorts :: forall l p s p' s' a st.
                  ListSplitD l p ( OnlySendPort a : s)
               -> ListSplitD s p' ( OnlySendPort a : s')
               -> ExecBuilder (ExecIndexSome l st) (ExecIndexSome (OnlySendPort a : Concat p (Concat p' s')) st) ()
mergeSendPorts i i' = case (listSplitConcat i, listSplitConcat i') of
    (Refl, Refl) -> M.do
      SomeInitStatusIndexRetD retPrf <- execInvariantM
      compPrf <- absentInitStatusComp
      forkRight' compPrf getKnownLenPrf $ process sendMerger
      link Split2 i
      link Split1 (listSplitAdd (listSplitPopSuffix i) i')
      -- We've done everything, now just prove this to the compiler
      case (concatAssocPrf @p @p' @s' (listSplitPopSuffix i), retPrf) of
        (Refl, InitStatusIndexRetAbsent) -> xreturn ()
        (Refl, InitStatusIndexRetPresent) -> xreturn ()
  where
    sendMerger :: AsyncT '[ OnlySendPort a, OnlyRecvPort a, OnlyRecvPort a] NextRecv NextRecv Void
    sendMerger = M.do
      x <- recvAny <&> \case
        SomeRxMess Here contra -> case contra of {}
        SomeRxMess (There Here) x -> x
        SomeRxMess (There2 Here) x -> x
        SomeRxMess (There3 contra) _ -> case contra of {}
      send Here x
      sendMerger

    absentInitStatusComp :: ExecBuilder (ExecIndexSome l' st') (ExecIndexSome l' st') (InitStatusCompD InitAbsent st')
    absentInitStatusComp = execInvariantM <&> \case
      SomeInitStatusIndexRetD InitStatusIndexRetAbsent -> InitStatusNone
      SomeInitStatusIndexRetD InitStatusIndexRetPresent -> InitStatusSnd

-- |Run environment with a given protocol (no adversary yet).
subRespEval :: SubRespTree iface
            -- ^The called protocol with its subroutines composed-in
            -> ExecBuilder ExecIndexInit
                  (ExecIndexSome '[PingSendPort, PortDual iface] InitAbsent) ()
subRespEval (MkSubRespTree p c) = M.do
    p
    forEliminateHlist c $ \_ z -> M.do
      forkRight $ subRespEval z
      case z of
        MkSubRespTree _ _ -> M.do
          link Split1 Split2
          mergeSendPorts Split0 Split0
  where
    forEliminateHlist
      :: HList SubRespTree down
      -> ( forall p z s.
             ListSplitD down p (z:s)
          -> SubRespTree z
          -> ExecBuilder (ExecIndexSome (ping:w:z:s) InitAbsent)
                         (ExecIndexSome (ping:w:s) InitAbsent) ()
         )
      -> ExecBuilder (ExecIndexSome (ping:w:down) InitAbsent)
                     (ExecIndexSome '[ping, w] InitAbsent) ()
    forEliminateHlist HNil _ = xreturn ()
    forEliminateHlist (HCons z zs) f = M.do
      f SplitHere z
      forEliminateHlist zs $ f . SplitThere

ucExec :: EnvProcess up a
       -> SubRespTree up
       -> ExecBuilder ExecIndexInit (ExecIndexSome '[] (InitPresent a)) ()
ucExec e p@(MkSubRespTree _ _) = M.do
  subRespEval p
  forkRight $ e
  link Split0 Split1
  link Split0 Split0
