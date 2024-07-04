module HeterogenousList where

import Data.Kind (Type)
import Data.Type.Equality ((:~:)(Refl))

-- heterogenous lists

data HeteroList f (types :: [Type]) where
    HNil :: HeteroList f '[]
    HCons :: f t -> HeteroList f ts -> HeteroList f (t : ts)

data InList x xs where
    Here :: InList x (x : xs)
    There :: InList x xs -> InList x (y : xs)

areInListEqual :: InList x xs -> InList y xs -> Maybe (x :~: y)
areInListEqual Here Here = Just Refl
areInListEqual (There a) (There b) = areInListEqual a b
areInListEqual _ _ = Nothing

heteroListGet :: HeteroList f types -> InList x types -> f x
heteroListGet (HCons x _) Here = x
heteroListGet (HCons _ xs) (There t) = heteroListGet xs t
heteroListGet HNil contra = case contra of

homogenize
  :: (forall x. InList x types -> f x -> a)
  -> HeteroList f types
  -> [a]
homogenize _ HNil = []
homogenize g (HCons x xs) = g Here x : homogenize (g . There) xs

data SomeIndex xs where
    SomeIndex :: InList x xs -> SomeIndex xs

data SomeMessage xs where
  SomeMessage :: InList x xs -> x -> SomeMessage xs

data SomeSndMessage xs where
  SomeSndMessage :: InList (x, y) xs -> y -> SomeSndMessage xs

data SomeFstMessage xs where
  SomeFstMessage :: InList (x, y) xs -> x -> SomeFstMessage xs

padMessageIndex :: SomeMessage ts -> SomeMessage (t : ts)
padMessageIndex (SomeMessage i' x') = SomeMessage (There i') x'
