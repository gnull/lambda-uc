{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.HList where

import Prelude hiding ((!!))

import Data.Kind (Type, Constraint)
import Data.Type.Equality ((:~:)(Refl), TestEquality(..))

import Control.Arrow (first, second)

-- * Dependent pointer into a list

-- |Dependent index of an element of type @(x, y)@ in list @xs@
--
-- We use lists of pairs to encode the ports an algorithm has access to,
-- as well heterogenous lists @HList@ that occur during interpretation of our
-- algorithms. And this type serves as a pointer into one of such ports in
-- the list.
type InList :: forall a. [a] -> a -> Type
data InList xs x where
    Here :: InList (x : xs) x
    There :: InList xs x -> InList (y : xs) x

pattern There2 :: InList xs x -> InList (y0 : y1 : xs) x
pattern There2 i = There (There i)
{-# COMPLETE There2 #-}

pattern There3 :: InList xs x -> InList (y0 : y1 : y2 : xs) x
pattern There3 i = There (There2 i)
{-# COMPLETE There3 #-}

data SomeIndex xs where
    SomeIndex :: InList xs x -> SomeIndex xs

data SomeValue xs where
  SomeValue :: InList xs x -> x -> SomeValue xs

-- |Compare two indices for equality
instance TestEquality (InList xs) where
  -- testEquality :: InList x xs -> InList y xs -> Maybe (x :~: y)
  testEquality Here Here = Just Refl
  testEquality (There a) (There b) = testEquality a b
  testEquality _ _ = Nothing

-- |Pad the index to make it valid after applying @(::)@ to the list.
padMessageIndex :: SomeValue ts -> SomeValue (t : ts)
padMessageIndex (SomeValue i' x') = SomeValue (There i') x'

-- * Port Lists

-- |A port is defined by a pair of types.
--
-- @`P` A B@ allows sending values of type @A@ and receiving @B@.
data Port = P Type Type

type PortTxType :: Port -> Type
type family PortTxType p where
  PortTxType (P x _) = x

type PortRxType :: Port -> Type
type family PortRxType p where
  PortRxType (P _ x) = x

type PortSwap :: Port -> Port
type family PortSwap p where
  PortSwap (P x y) = P y x

-- |A pointer into the list of ports @xs@.
--
-- The @`PortInList` x y xs@ is a proof of @`P` x y@ being in @xs@.
type PortInList :: Type -> Type -> [Port] -> Type
type PortInList x y xs = InList xs (P x y)

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

data SomeRxMess xs where
  SomeRxMess :: PortInList x y xs -> y -> SomeRxMess xs

data SomeTxMess xs where
  SomeTxMess :: PortInList x y xs -> x -> SomeTxMess xs

-- * Heterogenous Lists
--
-- This defines a list where values may have different types,
-- as prescribed by the list type's index.

-- |Heterogenous List
type HList :: forall a. (a -> Type) -> [a] -> Type
data HList f (types :: [a]) where
    HNil :: HList f '[]
    HCons :: f t -> HList f ts -> HList f (t : ts)

-- |Signleton type to express the list structure (length) but not the contents.
data KnownLenD :: forall a. [a] -> Type where
  KnownLenZ :: KnownLenD '[]
  KnownLenS :: forall a (x :: a) (l :: [a]). KnownLenD l -> KnownLenD (x : l)

-- |Class of list values for which their length is known at compile time.
type KnownLen :: forall a. [a] -> Constraint
class KnownLen l where
  getKnownLenPrf :: KnownLenD l

instance KnownLen '[] where
  getKnownLenPrf = KnownLenZ

instance KnownLen xs => KnownLen (x:xs) where
  getKnownLenPrf = KnownLenS $ getKnownLenPrf @_ @xs

data PortsLenD (ports :: [Port]) where
  PortsLenZ :: PortsLenD '[]
  PortsLenS :: PortsLenD l -> PortsLenD (P x y : l)

data SameLenD :: forall a b. [a] -> [b] -> Type where
  SameLenNil :: SameLenD '[] '[]
  SameLenCons :: SameLenD l l' -> SameLenD (x:l) (x':l')

type SameLen :: forall a b. [a] -> [b] -> Constraint
class SameLen l l' where
  proveSameLength :: SameLenD l l'

instance SameLen '[] '[] where
  proveSameLength = SameLenNil

instance SameLen l l' => SameLen (x:l) (x':l') where
  proveSameLength = SameLenCons proveSameLength

type Concat :: forall a. [a] -> [a] -> [a]
type family Concat xs ys where
  Concat '[] ys = ys
  Concat (x:xs) ys = x:Concat xs ys

-- |Proof of `p ++ (p' ++ s') == (p ++ p') ++ s'`.
concatAssocPrf :: forall p p' s' l s.
                  ListSplitD l p s
               -> (Concat p (Concat p' s')) :~: (Concat (Concat p p') s')
concatAssocPrf = \case
  SplitHere -> Refl
  SplitThere i -> case concatAssocPrf @_ @p' @s' i of
    Refl -> Refl

concatInjPrf :: forall xs ys ys'.
             Concat xs ys :~: Concat xs ys'
             -> KnownLenD xs
             -> ys :~: ys'
concatInjPrf Refl = \case
  KnownLenZ -> Refl
  KnownLenS rest -> concatInjPrf Refl rest

-- |Statement @`ListSplitD` l p s@ says that @l = p ++ s@, i.e. that @l@ can be
-- cut into prefix @p@ and suffix @s@.
--
-- Structure-wise, this is just a pointer, like `InList`, but it carries
-- different information on type-level.
data ListSplitD :: forall a. [a] -> [a] -> [a] -> Type where
  SplitHere :: ListSplitD l '[] l
  SplitThere :: ListSplitD l p s -> ListSplitD (x:l) (x:p) s

type ListSplitConcat p s = ListSplitD (Concat p s) p s

class ListSplit l p s where
  getListSplit :: ListSplitD l p s

instance (KnownLen p, l ~ Concat p s) => ListSplit l p s where
  getListSplit = getListSplit' getKnownLenPrf

getListSplit' :: KnownLenD p
              -> ListSplitD (Concat p s) p s
getListSplit' = \case
    KnownLenZ -> SplitHere
    KnownLenS i -> SplitThere $ getListSplit' i

listSplitConcat :: ListSplitD l p s
                -> Concat p s :~: l
listSplitConcat = \case
  SplitHere -> Refl
  SplitThere i -> case listSplitConcat i of
    Refl -> Refl

listSplitAdd :: ListSplitD l p s
             -> ListSplitD s p' s'
             -> ListSplitD l (Concat p p') s'
listSplitAdd = \case
  SplitHere -> id
  SplitThere i -> \j -> SplitThere $ listSplitAdd i j

listConcatSplit :: ListSplitD l p s
                -> ListSplitD (Concat p s') p s'
listConcatSplit SplitHere = SplitHere
listConcatSplit (SplitThere i) = SplitThere $ listConcatSplit i

listSplitPopSuffix :: ListSplitD (Concat p (x:s)) p (x:s)
                   -> ListSplitD (Concat p s) p s
listSplitPopSuffix = \case
  SplitHere -> SplitHere
  SplitThere i -> SplitThere $ listSplitPopSuffix i

listSplitSubst :: ListSplitD l' p' (s:rest)
               -> ListSplitConcat p' (f:rest)
listSplitSubst = \case
  SplitHere -> SplitHere
  SplitThere i -> SplitThere $ listSplitSubst i

listSplitSwap :: ListSplitD l p (f:l')
              -> ListSplitD l' p' (s:rest)
              -> ( ListSplitConcat p (s:(Concat p' (f:rest)))
                 , ListSplitConcat p' (f:rest)
                 )
listSplitSwap = \case
  SplitHere -> \p -> (SplitHere, listSplitSubst p)
  SplitThere i -> \p -> first SplitThere $ listSplitSwap i p

listSplitSuff2 :: ListSplitD l p (f:l')
               -> ListSplitD l' p' (s:rest)
               -> ( ListSplitConcat p (Concat p' rest)
                  , ListSplitConcat p' rest
                  )
listSplitSuff2 = \case
  SplitHere -> \p -> case listSplitConcat p of
    Refl -> (SplitHere, listSplitPopSuffix p)
  SplitThere i -> \p -> first SplitThere $ listSplitSuff2 i p


-- instance ListSplit l '[] l where
--   getListSplit = SplitHere
-- instance ListSplit l p s => ListSplit (x:l) (x:p) s where
--   getListSplit = SplitThere getListSplit

pattern Split0 :: ListSplitD l '[] l
pattern Split0 = SplitHere
{-# COMPLETE Split0 #-}

pattern Split1 :: ListSplitD (x0 : l) '[x0] l
pattern Split1 = SplitThere Split0
{-# COMPLETE Split1 #-}

pattern Split2 :: ListSplitD (x0 : x1 : l)
                            (x0 : '[x1]) l
pattern Split2 = SplitThere Split1
{-# COMPLETE Split2 #-}

pattern Split3 :: ListSplitD (x0 : x1 : x2 : l)
                            (x0 : x1 : '[x2]) l
pattern Split3 = SplitThere Split2
{-# COMPLETE Split3 #-}

pattern Split4 :: ListSplitD (x0 : x1 : x2 : x3 : l)
                            (x0 : x1 : x2 : '[x3]) l
pattern Split4 = SplitThere Split3
{-# COMPLETE Split4 #-}

pattern Split5 :: ListSplitD (x0 : x1 : x2 : x3 : x4 : l)
                            (x0 : x1 : x2 : x3 : '[x4]) l
pattern Split5 = SplitThere Split4
{-# COMPLETE Split5 #-}

hlistDrop :: ListSplitD l p s
          -> HList f l
          -> HList f s
hlistDrop SplitHere xs = xs
hlistDrop (SplitThere i) (HCons _ xs) = hlistDrop i xs

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
(!!) :: HList f types -> InList types x -> f x
(!!) (HCons x _) Here = x
(!!) (HCons _ xs) (There t) = xs !! t
(!!) HNil contra = case contra of

-- |Applies given mutating action to one of the elements in the list
forIthFst :: Monad m
       => InList xs x
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
            => InList types x
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
hMap :: (forall a. InList types a -> f a -> g a) -> HList f types -> HList g types
hMap f = \case
  HNil -> HNil
  HCons x xs -> HCons (f Here x) $ hMap (\i-> f $ There i) xs

-- |Convert @HList@ to a regular list.
homogenize
  :: forall t (types :: [t]) (f :: t -> Type) a.
     (forall x. InList types x -> f x -> a)
  -> HList f types
  -> [a]
homogenize _ HNil = []
homogenize g (HCons x xs) = g Here x : homogenize (g . There) xs
