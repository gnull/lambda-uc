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

-- |A heterogenous list where two types alternate.
data Transcript (h :: Type) (snd :: Type) (end :: Type) where
  AltHNil :: h -> Transcript h snd h
  AltHCons :: h -> Transcript snd h end -> Transcript h snd end

-- |Two party (2PC) protocol with Semi-honest adversary.
--
-- We return the actual outputs of Alice and Bob and the transcript of their
-- interaction if they halt simultaneously, as exptected. If one of them
-- terminates with the other keeping running, we crash with `mzero`.
runP2 :: forall m x y f t a b. (Monad m, KnownBool f, KnownBool t)
      => Party m '(x, y) f t a
      -- ^Alice
      -> Party m '(y, x) (BoolNeg f) (BoolNeg t) b
      -- ^Bob
      -> MaybeT m ((a, b), Maybe (IfThenElse f (Transcript x y) (Transcript y x) (IfThenElse t y x)))
runP2 = case getSBool @f of
    STrue -> helper
    SFalse -> case getSBool @t of
      STrue -> \a b -> first swap <$> helper b a
      SFalse -> \a b -> first swap <$> helper b a
  where
    helper :: forall x' y' t' a' b'. KnownBool t'
           => Party m '(x', y') True t' a'
           -> Party m '(y', x') False (BoolNeg t') b'
           -> MaybeT m ((a', b'), Maybe (Transcript x' y' (IfThenElse t' y' x')))
    helper a b = do
      Trans.lift (runTillSend a) >>= \case
        SrCall contra _ _ -> case contra of {}
        SrHalt ar -> Trans.lift (runTillHalt b) >>= \case
          Nothing -> mzero
          Just br -> pure ((ar, br), Nothing)
        SrSend (SomeFstMessage Here m) contA ->
          Trans.lift (runTillRecv (SomeSndMessage Here m) b) >>= \case
            RrRecv contB -> case getSBool @t' of
              STrue -> (swap *** fmap (AltHCons m)) <$> helper contB contA
              SFalse -> (swap *** consWithMaybe m) <$> helper contB contA
            RrCall contra _ _ -> case contra of {}
            RrHalt rb -> Trans.lift (runTillHalt contA) >>= \case
              Nothing -> mzero
              Just ra -> case getSBool @t' of
                -- SFalse -> pure ((ra, rb), Just $ AltHNil m)
                STrue -> pure ((ra, rb), Just $ _)
        SrSend (SomeFstMessage (There contra) _) _ -> case contra of {}

    consWithMaybe :: h -> Maybe (Transcript snd h h) -> Maybe (Transcript h snd h)
    consWithMaybe h Nothing = Just $ AltHNil h
    consWithMaybe h (Just l) = Just $ AltHCons h l
