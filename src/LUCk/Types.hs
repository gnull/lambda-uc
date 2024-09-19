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
  , concatInjPrf
  , KnownIndex(..)
  , KnownLenD(..)
  , KnownLen(..)
  , SameLen(..)
  , SameLength(..)
  , Index(..)
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

concatInjPrf :: forall xs ys ys'.
             Concat xs ys :~: Concat xs ys'
             -> KnownLenD xs
             -> ys :~: ys'
concatInjPrf Refl = \case
  KnownLenZ -> Refl
  KnownLenS rest -> concatInjPrf Refl rest

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

-- |Class of list values for which their length is known at compile time.
type KnownLen :: forall a. [a] -> Constraint
class KnownLen l where
  getKnownLenPrf :: KnownLenD l

instance KnownLen '[] where
  getKnownLenPrf = KnownLenZ

instance KnownLen xs => KnownLen (x:xs) where
  getKnownLenPrf = KnownLenS $ getKnownLenPrf @_ @xs

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
