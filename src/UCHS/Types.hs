module UCHS.Types
  ( module Data.HList
  , module Data.Void
  , module Data.Kind
  , SBool(..)
  , Or
  , Fst
  , Snd
  , Empty
  , IfThenElse
  , KnownBool(..)
  )
where

import Data.Void (Void)

import Data.Kind (Type)
import Data.HList

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

type Or :: Bool -> Bool -> Bool
type family Or x y where
  Or True _ = True
  Or _ True = True
  Or _ _ = False

type Fst :: (Type, Type) -> Type
type family Fst p where
  Fst '(x, _) = x

type Snd :: (Type, Type) -> Type
type family Snd p where
  Snd '(_, y) = y

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
