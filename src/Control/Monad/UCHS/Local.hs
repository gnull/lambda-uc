{-# LANGUAGE DerivingVia #-}
-- {-# LANGUAGE ScopedTypeVariables #-}

module Control.Monad.UCHS.Local where

import Data.Kind (Type)
import Data.Void

import Data.HList

import Control.XFreer
import Control.XApplicative
import Control.XMonad

import Control.Monad.UCHS.Sync

-- type ZipConst :: forall f s. [f] -> s -> [(f, s)]
-- type family ZipConst fs s where
--   ZipConst '[] _ = '[]
--   ZipConst (h:rest) s = ('(h, s) : ZipConst rest s)

newtype Algo (pr :: Bool) (ra :: Bool) (ex :: Type) (a :: Type) =
  Algo { runAlgo :: SyncAlgo ('SyncPars pr ra '[ '(ex, True)] '(Void, Void) '[]) True True a }

  deriving (Functor) via
    (SyncAlgo ('SyncPars pr ra '[ '(ex, True)] '(Void, Void) '[]) True True)
  deriving (Applicative, Monad) via
    (SyncAlgo ('SyncPars pr ra '[ '(ex, True)] '(Void, Void) '[]) True True)

liftToSync :: InList '(ex, b) exs
           -> Algo pr ra ex a
           -> SyncAlgo ('SyncPars pr ra exs p l) b b a
liftToSync _ (Algo (SyncAlgo (Pure v))) = pure v
liftToSync i (Algo (SyncAlgo (Bind v f))) =
  case v of
    YieldAction contra -> case contra of {}
    CallAction contra _ -> case contra of {}
    PrintAction s -> liftToSync i . Algo . SyncAlgo . f =<<:
      debugPrint s
    RandAction -> liftToSync i . Algo . SyncAlgo . f =<<:
      rand
    -- TODO: get rid of the undefined here
    ThrowAction Here e -> liftToSync i . Algo . SyncAlgo . undefined =<<:
      throw i e
    ThrowAction (There contra) _ -> case contra of {}
