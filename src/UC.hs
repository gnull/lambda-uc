{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}

module UC where

import Data.Kind (Type)

data InList (party :: a) (parties :: [a]) where
  Here :: InList x (x : xs)
  There :: InList x xs -> InList x (y : xs)

class AllowParties m (parties :: [Int]) | m -> parties where
  send :: InList party parties -> v -> m ()
  recv :: InList party patries -> m v

-- class Conn party m v where
--   send :: AllowParties m parties => InList party parties -> v -> m ()
--   recv :: AllowParties m parties => InList party patries -> m v

pattern Alice = 0
pattern Bob = 1
pattern Charlie = 2

aliceCon :: [Int]
aliceCon = [1]

aliceAlgo
  :: (Monad m, AllowParties m aliceCon)
  => m String
aliceAlgo = recv bob
  where
    bob = Here

bobCon :: [Int]
bobCon = [0, 2]

bobAlgo
  :: (Monad m, AllowParties m bobCon)
  => m ()
bobAlgo = undefined
  where
    alice = Here
    charlie = There $ Here
