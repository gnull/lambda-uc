module UCHS.Types
  ( module Data.HList
  , module Data.Void
  , module Data.Kind
  , module Data.Type.Equality
  , Not
  , SBool(..)
  , SMaybeBool(..)
  , Or
  , BoolNeg
  , Empty
  , IfThenElse
  , KnownBool(..)
  , lemmaBoolNegInv
  , KnownMaybeBool(..)
  , SameLen(..)
  , SameLength(..)
  , Index
  , IndexReachableT(..)
  , IndexReachable(..)
  )
where

import Data.Void (Void)

import Data.Kind (Type, Constraint)
import Data.HList

import Data.Type.Equality ((:~:)(Refl))

type Not (a :: Type) = a -> Void

data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SMaybeBool (a :: Maybe Bool) where
  SJustTrue :: SMaybeBool (Just True)
  SJustFalse :: SMaybeBool (Just False)
  SNothing :: SMaybeBool Nothing

type Or :: Bool -> Bool -> Bool
type family Or x y where
  Or True _ = True
  Or _ True = True
  Or _ _ = False

type BoolNeg :: Bool -> Bool
type family BoolNeg x where
  BoolNeg True = False
  BoolNeg False = True

-- |Type-level if-then-else, we use it to choose constraints conditionally
type IfThenElse :: forall a. Bool -> a -> a -> a
type family IfThenElse c t f where
  IfThenElse True t _ = t
  IfThenElse False _ f = f

-- |Empty constraint
class Empty x
instance Empty x

-- | ¬¬x = x
lemmaBoolNegInv :: forall b. KnownBool b => BoolNeg (BoolNeg b) :~: b
lemmaBoolNegInv = case getSBool @b of
  STrue -> Refl
  SFalse -> Refl

-- |Known boolean value. Implemented by constants, but not by `forall (b ::
-- Bool). b`. Adding this to the context of a function polymorphic over `b` is
-- the same as adding an explicit parameter `SBool b` to it. I.e. `SBool b ->`
-- is the same as `KnownBool b =>`.
class KnownBool (b :: Bool) where
  getSBool :: SBool b
instance KnownBool False where
  getSBool = SFalse
instance KnownBool True where
  getSBool = STrue

class KnownMaybeBool (b :: Maybe Bool) where
  getSMaybeBool :: SMaybeBool b
instance KnownMaybeBool Nothing where
  getSMaybeBool = SNothing
instance KnownMaybeBool (Just False) where
  getSMaybeBool = SJustFalse
instance KnownMaybeBool (Just True) where
  getSMaybeBool = SJustTrue

-- -- |Signleton type to express the list structure (length) but not the contents.
-- data SListLen :: forall a. [a] -> Type where
--   SListLenZ :: SListLen '[]
--   SListLenS :: forall a (x :: a) (l :: [a]). SListLen l -> SListLen (x : l)

-- -- |Class of list values for which their length is known at compile time.
-- type KnownLength :: forall a. [a] -> Constraint
-- class KnownLength l where
--   getSListLen :: SListLen l

-- instance KnownLength '[] where
--   getSListLen = SListLenZ

-- instance KnownLength xs => KnownLength (x:xs) where
--   getSListLen = SListLenS $ getSListLen @_ @xs

data SameLen :: forall a b. [a] -> [b] -> Type where
  SameLenNil :: SameLen '[] '[]
  SameLenCons :: SameLen l l' -> SameLen (x:l) (x':l')

type SameLength :: forall a b. [a] -> [b] -> Constraint
class SameLength l l' where
  proveSameLength :: SameLen l l'

instance SameLength '[] '[] where
  proveSameLength = SameLenNil

instance SameLength l l' => SameLength (x:l) (x':l') where
  proveSameLength = SameLenCons proveSameLength

type Index = Maybe Bool

-- |Models the reachability relation defined as:
--
-- 1. `Just a` can reach any state.
-- 2. `Nothing` can reach `Nothing`.
data IndexReachableT (bef :: Index) (aft :: Index) where
  IndexReachableJust :: IndexReachableT (Just a) b
  IndexReachableNothing :: IndexReachableT Nothing Nothing

-- |Typeclass for automatically deriving `IndexReachableT`.
class IndexReachable bef aft where
  getIndexReachablePrf :: IndexReachableT bef aft

instance IndexReachable (Just a) b where
  getIndexReachablePrf = IndexReachableJust

instance IndexReachable Nothing Nothing where
  getIndexReachablePrf = IndexReachableNothing
