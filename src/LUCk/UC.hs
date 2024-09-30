module LUCk.UC
  ( ProtoNode
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

type OnlySendChan a = '(a, Void)
type OnlyRecvChan a = '(Void, a)
type PingSendChan = OnlySendChan ()
type PingRecvChan = OnlyRecvChan ()

-- |A protocol without it subroutine implementations built-in.
--
-- - `m` is the monad for local computations,
-- - `up` is the interface we expose to environment (or another protocol that
--   call us as a subroutine),
-- - `down` is the list of interfaces of subroutines we call on,
-- - `bef` is the WT state we start from.
--
-- This type definition ensures that we never terminate, we must continuously
-- be ready to receive messages and respond to them somehow.
data ProtoNode up down m where
  MkIdealNode :: AsyncT (PingSendChan : '(x, y) : down) m NextRecv NextRecv Void
              -> ProtoNode '(y, x) down m

data EnvProcess down m a where
  MkEnvProcess :: AsyncT '[PingRecvChan, down] m NextSend NextSend a
               -> EnvProcess down m a

data KnownPairD p where
  KnownPairD :: KnownPairD '(x, y)

-- |A tree of subroutine-respecting protocols.
--
-- A `SubRespTree m up` is simply @ProtoNode up down m@ where the
-- required subroutine interfaces were filled with actual implementations (and,
-- therefore, are not required and not exposed by a type parameter anymore).
data SubRespTree (m :: Type -> Type) (up :: (Type, Type)) where
  MkSubRespTree :: ProtoNode '(x, y) down m
                -> KnownPairD '(x, y)
                -> HList (SubRespTree m) down
                -> SubRespTree m '(x, y)

mergeSendPorts :: forall l p s p' s' a m i res.
                  ListSplitD l p ( OnlySendChan a : s)
               -> ListSplitD s p' ( OnlySendChan a : s')
               -> ExecBuilder m (ExecIndexSome l i res) (ExecIndexSome (OnlySendChan a : Concat p (Concat p' s')) i res) ()
mergeSendPorts i i' = case (listSplitConcat i, listSplitConcat i') of
    (Refl, Refl) -> execInvariantM >>=: \case
        (iPrf, retPrf) -> M.do
          forkRight' (getForkIndexRecv iPrf) getKnownLenPrf $ process sendMerger
          connect Split2 i
          connect Split1 (listSplitAdd (listSplitPopSuffix i) i')
          -- We've done everything, now just prove this to the compiler
          case (concatAssocPrf @p @p' @s' (listSplitPopSuffix i), iPrf, retPrf) of
            (Refl, _, MayOnlyReturnType) -> xreturn ()
            (Refl, SNextRecv, MayOnlyReturnVoid) -> xreturn ()
            (Refl, SNextSend, MayOnlyReturnVoid) -> xreturn ()
  where
    sendMerger :: AsyncT '[ OnlySendChan a, OnlyRecvChan a, OnlyRecvChan a] m NextRecv NextRecv Void
    sendMerger = M.do
      x <- recvAny <&> \case
        SomeSndMessage Here contra -> case contra of {}
        SomeSndMessage (There Here) x -> x
        SomeSndMessage (There2 Here) x -> x
        SomeSndMessage (There3 contra) _ -> case contra of {}
      send Here x
      sendMerger

-- |Run environment with a given protocol (no adversary yet).
subRespEval :: SubRespTree m iface
            -- ^The called protocol with its subroutines composed-in
            -> ExecBuilder m ExecIndexInit (ExecIndexSome '[PingSendChan, ChanSwap iface] NextRecv Void) ()
subRespEval (MkSubRespTree (MkIdealNode p) _ c) = M.do
    process p
    forEliminateHlist c $ \_ z -> M.do
      forkRight $ subRespEval z
      case z of
        MkSubRespTree _ KnownPairD _ -> M.do
          connect Split1 Split2
          mergeSendPorts Split0 Split0
  where
    forEliminateHlist :: HList (SubRespTree m) down
                      -> ( forall p z s.
                             ListSplitD down p (z:s)
                          -> SubRespTree m z
                          -> ExecBuilder m (ExecIndexSome (ping:w:z:s) NextRecv Void)
                                           (ExecIndexSome (ping:w:s) NextRecv Void) ()
                         )
                      -> ExecBuilder m (ExecIndexSome (ping:w:down) NextRecv Void)
                                       (ExecIndexSome '[ping, w] NextRecv Void) ()
    forEliminateHlist HNil _ = xreturn ()
    forEliminateHlist (HCons z zs) f = M.do
      f SplitHere z
      forEliminateHlist zs $ f . SplitThere
