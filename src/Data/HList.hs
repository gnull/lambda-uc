module Data.HList where

import Prelude hiding ((!!))

import Data.Kind (Type)
import Data.Type.Equality ((:~:)(Refl))

-- * Dependent pointer into a list

-- |Dependent index of an element of type @(x, y)@ in list @xs@
--
-- We use lists of pairs to encode the channels an algorithm has access to,
-- as well heterogenous lists @HList@ that occur during interpretation of our
-- algorithms. And this type serves as a pointer into one of such channels in
-- the list.
type InList :: forall a. a -> [a] -> Type
data InList x xs where
    Here :: InList x (x : xs)
    There :: InList x xs -> InList x (y : xs)

data SomeIndex xs where
    SomeIndex :: InList x xs -> SomeIndex xs

data SomeValue xs where
  SomeValue :: InList x xs -> x -> SomeValue xs

-- |Compare two indices for equality
testEquality :: InList x xs -> InList y xs -> Maybe (x :~: y)
testEquality Here Here = Just Refl
testEquality (There a) (There b) = testEquality a b
testEquality _ _ = Nothing

-- |Pad the index to make it valid after applying @(::)@ to the list.
padMessageIndex :: SomeValue ts -> SomeValue (t : ts)
padMessageIndex (SomeValue i' x') = SomeValue (There i') x'

-- * Channel Lists

-- |A pointer into the list of channels @xs@.
--
-- The @Chan x y xs@ is a bi-directional channel where you can send values of
-- type $x$ and receive type $y$.
type Chan :: forall a b. a -> b -> [(a, b)] -> Type
type Chan x y xs = InList '(x, y) xs

data SomeSndMessage xs where
  SomeSndMessage :: Chan x y xs -> y -> SomeSndMessage xs

data SomeFstMessage xs where
  SomeFstMessage :: Chan x y xs -> x -> SomeFstMessage xs

-- * Heterogenous Lists
--
-- This defines a list where values may have different types,
-- as prescribed by the list type's index.

-- |Heterogenous List
type HList :: forall a. (a -> Type) -> [a] -> Type
data HList f (types :: [a]) where
    HNil :: HList f '[]
    HCons :: f t -> HList f ts -> HList f (t : ts)

-- |Fetch the value under given index. Statically checked version of @Prelude.(!!)@.
(!!) :: HList f types -> InList x types -> f x
(!!) (HCons x _) Here = x
(!!) (HCons _ xs) (There t) = xs !! t
(!!) HNil contra = case contra of

-- |Convert @HList@ to a regular list.
homogenize
  :: (forall x. InList x types -> f x -> a)
  -> HList f types
  -> [a]
homogenize _ HNil = []
homogenize g (HCons x xs) = g Here x : homogenize (g . There) xs
