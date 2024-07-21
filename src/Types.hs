module Types
  ( module Data.HList
  , SBool(..)
  )
where

import Data.HList

-- |Singleton @Bool@ used to store the dependent value of Write Token
data SBool (a :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False
