{-# LANGUAGE AllowAmbiguousTypes #-}

module LUCk.Types
  ( module Data.HList
  , module Data.Void
  , module Data.Kind
  , module Data.Type.Equality
  , Not
  , SBool(..)
  , SIndex(..)
  , Or
  , BoolNeg
  , Empty
  , IfThenElse
  , KnownBool(..)
  , lemmaBoolNegInv
  , Concat
  , concatAssocPrf
  , concatInjPrf
  , ListSplitD(..)
  , ListSplitConcat
  , ListSplit(..)
  , pattern Split0
  , pattern Split1
  , pattern Split2
  , pattern Split3
  , pattern Split4
  , pattern Split5
  , getListSplit'
  , listConcatSplit
  , listSplitConcat
  , listSplitAdd
  , listSplitPopSuffix
  , listSplitSwap
  , listSplitSuff2
  , KnownIndex(..)
  , KnownLenD(..)
  , KnownLen(..)
  , KnownPortD(..)
  , SameLenD(..)
  , SameLen(..)
  , Index(..)
  )
where

import Data.Void (Void)
import Control.Arrow

import Data.Kind (Type, Constraint)
import Data.HList

import Data.Type.Equality ((:~:)(Refl))

type Not (a :: Type) = a -> Void

data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SIndex (a :: Index) where
  SNextSend :: SIndex NextSend
  SNextRecv :: SIndex NextRecv

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

class KnownIndex (b :: Index) where
  getSIndex :: SIndex b
instance KnownIndex NextRecv where
  getSIndex = SNextRecv
instance KnownIndex NextSend where
  getSIndex = SNextSend

-- |Signleton type to express the list structure (length) but not the contents.
data KnownLenD :: forall a. [a] -> Type where
  KnownLenZ :: KnownLenD '[]
  KnownLenS :: forall a (x :: a) (l :: [a]). KnownLenD l -> KnownLenD (x : l)

data KnownPortD p where
  KnownPortD :: KnownPortD (P x y)

-- |Class of list values for which their length is known at compile time.
type KnownLen :: forall a. [a] -> Constraint
class KnownLen l where
  getKnownLenPrf :: KnownLenD l

instance KnownLen '[] where
  getKnownLenPrf = KnownLenZ

instance KnownLen xs => KnownLen (x:xs) where
  getKnownLenPrf = KnownLenS $ getKnownLenPrf @_ @xs

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

-- |Next operation of the asyncronous algorithm
data Index
  = NextSend
  -- ^Our turn to `LUCk.Monad.Class.Async.send`
  | NextRecv
  -- ^Our turn to `LUCk.Monad.Class.Async.recvAny`

-- -- |The index of our monad for asynchronous algorithms
-- data ExtendedIndex
--   = On Index
--   -- ^Asynchronous interaction is on, next operation is given by the `NextOp`
--   | Off
--   -- ^Asynchronous interaction is off, we're not allowed to call
--   -- `LUCk.Monad.Class.Async.send` or `LUCk.Monad.Class.Async.recvAny`
