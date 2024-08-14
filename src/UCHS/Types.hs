module UCHS.Types
  ( module Data.HList
  , module Data.Void
  , module Data.Kind
  , SBool(..)
  , Or
  , Fst
  , MapFst
  , Snd
  , Empty
  , IfThenElse
  , KnownBool(..)
  , SameLen(..)
  , SameLength(..)
  )
where

import Data.Void (Void)

import Data.Kind (Type, Constraint)
import Data.HList

import Data.Type.Equality ((:~:)(Refl))

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

type Or :: Bool -> Bool -> Bool
type family Or x y where
  Or True _ = True
  Or _ True = True
  Or _ _ = False

-- |Type-level if-then-else, we use it to choose constraints conditionally
type IfThenElse :: forall a. Bool -> a -> a -> a
type family IfThenElse c t f where
  IfThenElse True t _ = t
  IfThenElse False _ f = f

-- |Empty constraint
class Empty x
instance Empty x

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
