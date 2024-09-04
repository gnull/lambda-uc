module UCHS.Protocols.P2 where

import Data.Tuple (swap)
import Data.Type.Equality ((:~:)(Refl))

import Control.Monad
import Control.Arrow (first, second, (***))
import Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Control.Monad.Trans.Class as Trans

import Control.XMonad

import Data.HList
import UCHS.Types
import UCHS.Monad

type Party m iface f t a = InterT ('InterPars m '[] '[iface] '[]) f t a

-- |A transcript of 2-party protocol.
--
-- Implemented as a heterogenous list where two types alternate. Indices
-- specify: the type of head, the type of element after the head (if any) and
-- the type of the last element.
data Transcript (h :: Type) (snd :: Type) (end :: Type) where
  AltHOne :: f -> Transcript f snd f
  AltHCons :: h -> Transcript snd h end -> Transcript h snd end

-- |Two party (2PC) protocol with Semi-honest adversary.
--
-- We return the actual outputs of Alice and Bob and the transcript of their
-- interaction if they halt simultaneously, as exptected. If one of them
-- terminates with the other keeping running, we crash with `mzero`.
--
-- Alice (the first argument) always sends the first message. Protocols where
-- parties do not send anything and just terminate are not allowed.
runP2 :: forall (t :: Bool) m x y a b. (Monad m)
      => SBool t
      -- ^Choice of who must send the last message.
      -> Party m '(x, y) (On NextSend) (IfThenElse t (On NextSend) Off) a
      -- ^Alice
      -> Party m '(y, x) (On NextRecv) (IfThenElse t Off (On NextSend)) b
      -- ^Bob
      -> MaybeT m ((a, b), Transcript x y (IfThenElse t y x))
runP2 t a b = do
      Trans.lift (runTillSend a) >>= \case
        SrCall contra _ _ -> case contra of {}
        SrHalt _ -> case t of
          STrue -> mzero -- runtime fail if no messages were sent
        SrSend (SomeFstMessage (There contra) _) _ -> case contra of {}
        SrSend (SomeFstMessage Here m) contA ->
          Trans.lift (runTillRecv (SomeSndMessage Here m) b) >>= \case
            RrCall contra _ _ -> case contra of {}
            RrHalt _ -> mzero
            RrRecv contB -> case t of
              STrue -> (swap *** AltHCons m) <$> runP2 SFalse contB contA
              SFalse -> (swap *** AltHCons m) <$> runP2 STrue contB contA
        SrSendFinal (SomeFstMessage (There contra) _) _ -> case contra of {}
        SrSendFinal (SomeFstMessage Here m) contA -> do
          resA <- Trans.lift $ runTillHaltAsync contA
          Trans.lift (runTillRecv (SomeSndMessage Here m) b) >>= \case
            RrCall contra _ _ -> case contra of {}
            RrHalt _ -> case t of {}
            RrRecv contB -> Trans.lift (runTillSend contB) >>= \case
              SrCall contra _ _ -> case contra of {}
              SrHalt resB -> case t of
                SFalse -> pure ((resA, resB), AltHOne m)
              SrSend (SomeFstMessage (There contra) _) _ -> case contra of {}
              SrSend (SomeFstMessage Here _) _ -> mzero
              SrSendFinal (SomeFstMessage (There contra) _) _ -> case contra of {}
              SrSendFinal (SomeFstMessage Here _) _ -> mzero
