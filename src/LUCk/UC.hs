module LUCk.UC
  ( ProtoNode
  , EnvNode
  , SubRespTree(..)
  , subRespEval
  )
 where

-- import Control.XMonad
-- import qualified Control.XMonad.Do as M

import LUCk.Syntax
import LUCk.Types

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
type ProtoNode m up down bef = AsyncT m ( '(Snd up, Fst up) : down) bef NextRecv Void

-- |An enviroment algorithm. The `down` is the interface of the functionality
-- environment is allowed to call.
type EnvNode m down a = AsyncT m '[down] NextSend NextSend a

-- |A tree of subroutine-respecting protocols.
--
-- A `SubRespTree m up` is simply `ProtoNode m up down False` where the
-- required subroutine interfaces were filled with actual implementations (and,
-- therefore, are not required and not exposed by a type parameter anymore).
data SubRespTree (m :: Type -> Type) (up :: (Type, Type)) where
  SubRespTreeNode :: ProtoNode m up down NextRecv
                  -> HList (SubRespTree m) down
                  -> SubRespTree m up

-- |Run environment with a given protocol (no adversary yet).
subRespEval :: forall m (iface :: (Type, Type)) a. Monad m
            => EnvNode m iface a
            -- ^Environment
            -> SubRespTree m iface
            -- ^The called protocol with its subroutines composed-in
            -> m a
subRespEval = \e (SubRespTreeNode p ch) -> runTillSend e >>= \case
    SrHalt x -> pure x
    SrSend (SomeFstMessage (There contra) _) _ -> case contra of {}
    SrSend (SomeFstMessage Here m) cont -> do
      p' <- ($ SomeSndMessage Here m) <$> mayOnlyRecvVoidPrf <$> runTillRecv p
      (t, resp) <- subroutineCall @iface p' ch
      e' <- ($ SomeSndMessage Here resp) <$> mayOnlyRecvWTPrf <$> runTillRecv cont
      subRespEval e' t
  where
    subroutineCall :: forall up down.
                   ProtoNode m up down NextSend
                   -> HList (SubRespTree m) down
                   -> m (SubRespTree m up, Snd up)
    subroutineCall p s = do
      (mayOnlySendWTPrf <$> runTillSend p) >>= \case
        (SomeFstMessage Here m', cont') ->
          pure (SubRespTreeNode cont' s, m')
        (SomeFstMessage (There i) m', cont') -> do
          (s', m'') <- forIth i s $ \(SubRespTreeNode ch chchs) -> do
            cont <- ($ SomeSndMessage Here m') <$> mayOnlyRecvVoidPrf <$> runTillRecv ch
            subroutineCall cont chchs
          cont'' <- ($ SomeSndMessage (There i) m'') <$> mayOnlyRecvVoidPrf <$> runTillRecv cont'
          subroutineCall cont'' s'
