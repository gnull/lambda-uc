module Data.HList where

import Prelude hiding ((!!))

import Data.Kind (Type)
import Data.Type.Equality ((:~:)(Refl))

import Data.Functor.Identity

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

-- Mixing this with `Fst` and `Snd` is hard at this point, since haskell fails
-- to automatically derive `(Snd up, Fst up) ~ ChanSwap up`.
type ChanSwap :: (Type, Type) -> (Type, Type)
type family ChanSwap p where
  ChanSwap '(x, y) = '(y, x)

type Fst :: forall a b. (a, b) -> a
type family Fst p where
  Fst '(x, _) = x

type MapFst :: forall a b. [(a, b)] -> [a]
type family MapFst l where
  MapFst '[] = '[]
  MapFst ( '(x, y) : l) = x : MapFst l

type Snd :: forall a b. (a, b) -> b
type family Snd p where
  Snd '(_, y) = y

type Zip :: forall a b. [a] -> [b] -> [(a, b)]
type family Zip l l' where
  Zip '[] '[] = '[]
  Zip (x:xs) (y:ys) = '(x, y) : Zip xs ys

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

pattern HListMatch0 :: HList f '[]
pattern HListMatch0 = HNil
{-# COMPLETE HListMatch0 #-}

pattern HListMatch1 :: f a -> HList f '[a]
pattern HListMatch1 a = HCons a HNil
{-# COMPLETE HListMatch1 #-}

pattern HListMatch2 :: f a -> f a' -> HList f '[a, a']
pattern HListMatch2 a a' = HCons a (HListMatch1 a')
{-# COMPLETE HListMatch2 #-}

pattern HListMatch3 :: f a -> f a' -> f a'' -> HList f '[a, a', a'']
pattern HListMatch3 a a' a'' = HCons a (HListMatch2 a' a'')
{-# COMPLETE HListMatch3 #-}

-- |Heterigenous zip of two lists
type HList2 :: forall a b. (a -> b -> Type) -> [a] -> [b] -> Type
data HList2 f (x :: [a]) (y :: [b]) where
    HNil2 :: HList2 f '[] '[]
    HCons2 :: f x y -> HList2 f xs ys -> HList2 f (x:xs) (y:ys)


pattern HList2Match0 :: HList2 f '[] '[]
pattern HList2Match0 = HNil2
{-# COMPLETE HList2Match0 #-}

pattern HList2Match1 :: f a b -> HList2 f '[a] '[b]
pattern HList2Match1 a = HCons2 a HNil2
{-# COMPLETE HList2Match1 #-}

pattern HList2Match2 :: f a b -> f a' b' -> HList2 f '[a, a'] '[b, b']
pattern HList2Match2 a a' = HCons2 a (HList2Match1 a')
{-# COMPLETE HList2Match2 #-}

pattern HList2Match3 :: f a b -> f a' b' -> f a'' b'' -> HList2 f '[a, a', a''] '[b, b', b'']
pattern HList2Match3 a a' a'' = HCons2 a (HList2Match2 a' a'')
{-# COMPLETE HList2Match3 #-}

-- |Fetch the value under given index. Statically checked version of @Prelude.(!!)@.
(!!) :: HList f types -> InList x types -> f x
(!!) (HCons x _) Here = x
(!!) (HCons _ xs) (There t) = xs !! t
(!!) HNil contra = case contra of

-- |Applies given mutating action to one of the elements in the list
forIthFst :: Monad m
       => InList x xs
       -- ^Element index
       -> HList2 f xs ys
       -- ^List
       -> (forall y. f x y -> m (f x y, z))
       -- ^Action
       -> m (HList2 f xs ys, z)
forIthFst Here (HCons2 x xs) f = do
  (x', z) <- f x
  pure (HCons2 x' xs, z)
forIthFst (There i) (HCons2 x xs) f = do
  (xs', z) <- forIthFst i xs f
  pure (HCons2 x xs', z)

-- |Applies given mutating action to one of the elements in the list
forIth :: Monad m
            => InList x types
            -- ^Action
            -> HList f types
            -- ^Element index
            -> (f x -> m (f x, z))
            -- ^List
            -> m (HList f types, z)
forIth Here (HCons x xs) f = do
  (x', z) <- f x
  pure (HCons x' xs, z)
forIth (There i) (HCons x xs) f = do
  (xs', z) <- forIth i xs f
  pure (HCons x xs', z)

-- |Like `map`, but for `HList`.
hMap :: (forall a. InList a types -> f a -> g a) -> HList f types -> HList g types
hMap f = \case
  HNil -> HNil
  HCons x xs -> HCons (f Here x) $ hMap (\i-> f $ There i) xs

-- |Convert @HList@ to a regular list.
homogenize
  :: forall t (types :: [t]) (f :: t -> Type) a.
     (forall x. InList x types -> f x -> a)
  -> HList f types
  -> [a]
homogenize _ HNil = []
homogenize g (HCons x xs) = g Here x : homogenize (g . There) xs
