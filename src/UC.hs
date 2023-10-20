LAN

module UC where

class AllowsParties m (parties :: [Int]) | m -> parties

instance AllowParties (ConnectionMonad parties) parties

data InList (party :: a) (parties :: [a]) where
  Here :: InList x (x : xs)
  There :: InList x xs -> InList x (y : xs)

class Conn party m v where
  send :: AllowsParties m parties => InList party parties -> v -> m ()
  recv :: AllowsParties m parties => InList party patries -> m v
