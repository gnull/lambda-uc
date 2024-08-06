{-# LANGUAGE ScopedTypeVariables #-}

module UCHS.Monad.InterT.Eval where

import Control.XMonad
import qualified Control.XMonad.Do as M

import UCHS.Monad
import UCHS.Types

type Append :: forall a. [a] -> [a] -> [a]
type family Append l l' where
  Append '[] ys = ys
  Append (x : xs) ys = (x : (Append xs ys))

type Concat :: forall a. [[a]] -> [a]
type family Concat l where
  Concat '[] = '[]
  -- Concat (x : xs) = Append x (Concat xs)

type ProtoNode m up down bef = InterT ('InterPars m '[] ( '(Snd up, Fst up) : down) '[]) bef False Void
type EnvNode m down a = InterT ('InterPars m '[] '[down] '[]) True True a

-- |A tree of subroutine-respecting protocols
data SubRespTree (m :: Type -> Type) (up :: (Type, Type)) where
  SubRespTreeNode :: ProtoNode m up down False
                  -> HList (SubRespTree m) down
                  -> SubRespTree m up

-- |Church encoding of `SubRespTree`
subRespTreeChurch :: SubRespTree m up
                  -> ( forall down. ProtoNode m up down False
                       -> HList (SubRespTree m) down -> a
                     )
                  -> a
subRespTreeChurch (SubRespTreeNode p s) cont = cont p s

-- |Run environment with a given protocol (no adversary yet).
subRespEval :: forall m (iface :: (Type, Type)) a. Monad m
            => EnvNode m iface a
            -- ^Environment
            -> SubRespTree m iface
            -- ^The called protocol with its subroutines composed-in
            -> m a
subRespEval = \e (SubRespTreeNode p ch) -> runTillSend e >>= \case
    SrCall contra _ _ -> case contra of {}
    SrHalt x -> pure x
    SrSend (SomeFstMessage (There contra) _) _ -> case contra of {}
    SrSend (SomeFstMessage Here m) cont -> do
      p' <- mayOnlyRecvVoidPrf <$> runTillRecv (SomeSndMessage Here m) p
      (t, resp) <- subroutineCall @iface p' ch
      e' <- mayOnlyRecvWTPrf <$> runTillRecv (SomeSndMessage Here resp) cont
      subRespEval e' t
  where
    subroutineCall :: forall up down.
                   ProtoNode m up down True
                   -> HList (SubRespTree m) down
                   -> m (SubRespTree m up, Snd up)
    subroutineCall p s = do
      (mayOnlySendWTPrf <$> runTillSend p) >>= \case
        (SomeFstMessage Here m', cont') ->
          pure (SubRespTreeNode cont' s, m')
        (SomeFstMessage (There i) m', cont') -> do
          (s', m'') <- forIth i s $ \(SubRespTreeNode ch chchs) -> do
            cont <- mayOnlyRecvVoidPrf <$> runTillRecv (SomeSndMessage Here m') ch
            subroutineCall cont chchs
          cont'' <- mayOnlyRecvVoidPrf <$> runTillRecv (SomeSndMessage (There i) m'') cont'
          subroutineCall cont'' s'

-- |Proof: A program with sync channels and return type `Void` may not
-- terminate; if it starts from `False` state, it will inevitably request an rx
-- message.
mayOnlyRecvVoidPrf :: RecvRes m ach '[] False Void
       -> InterT ('InterPars m '[] ach '[]) True False Void
mayOnlyRecvVoidPrf = \case
  RrCall contra _ _ -> case contra of {}
  RrHalt contra -> case contra of {}
  RrRecv x -> x

-- |Proof: a program with no sync channels that must terminate in `True` state
-- but starts in `False` state will inevitably request an rx message.
mayOnlyRecvWTPrf :: RecvRes m ach '[] True a
                 -> InterT ('InterPars m '[] ach '[]) True True a
mayOnlyRecvWTPrf = \case
  RrCall contra _ _ -> case contra of {}
  RrRecv x -> x

-- |Proof: a program with no sync channels that must terminate in `False` state
-- that starts from `True` state will inevitable produce a tx message.
mayOnlySendWTPrf :: SendRes m ach '[] False a
       -> (SomeFstMessage ach, InterT ('InterPars m '[] ach '[]) False False a)
mayOnlySendWTPrf = \case
  SrCall contra _ _ -> case contra of {}
  SrSend x cont -> (x, cont)
