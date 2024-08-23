module UCHS.Protocols.P2 where

import Data.Tuple (swap)
import Data.Type.Equality ((:~:)(Refl))

import Control.Monad
import Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Control.Monad.Trans.Class as Trans

import Control.XMonad

import Data.HList
import UCHS.Types
import UCHS.Monad

type Party m iface f t a = InterT ('InterPars m '[] '[iface] '[]) f t a

-- |Two party (2PC) protocol with Semi-honest adversary.
--
-- We return the actual outputs of Alice and Bob if they halt simultaneously,
-- as exptected. If one of them terminates with the other keeping running, we
-- crash with `mzero`.
--
-- TODO: add support for extracting the transcript.
runP2 :: forall m x y f t a b. (Monad m, KnownBool f, KnownBool t)
      => Party m '(x, y) f t a
      -- ^Alice
      -> Party m '(y, x) (BoolNeg f) (BoolNeg t) b
      -- ^Bob
      -> MaybeT m (a, b)
runP2 = case getSBool @f of
    STrue -> helper
    SFalse -> case getSBool @t of
      STrue -> \a b -> swap <$> helper b a
      SFalse -> \a b -> swap <$> helper b a
  where
    helper :: forall x' y' t' a' b'. KnownBool t'
           => Party m '(x', y') True t' a'
           -> Party m '(y', x') False (BoolNeg t') b'
           -> MaybeT m (a', b')
    helper a b = do
      Trans.lift (runTillSend a) >>= \case
        SrCall contra _ _ -> case contra of {}
        SrHalt ar -> Trans.lift (runTillHalt b) >>= \case
          Nothing -> mzero
          Just br -> pure (ar, br)
        SrSend (SomeFstMessage Here m) contA ->
          Trans.lift (runTillRecv (SomeSndMessage Here m) b) >>= \case
            RrRecv contB -> case getSBool @t' of
              STrue -> swap <$> helper contB contA
              SFalse -> swap <$> helper contB contA
            RrCall contra _ _ -> case contra of {}
            RrHalt rb -> Trans.lift (runTillHalt contA) >>= \case
              Nothing -> mzero
              Just ra -> pure (ra, rb)
        SrSend (SomeFstMessage (There contra) _) _ -> case contra of {}
