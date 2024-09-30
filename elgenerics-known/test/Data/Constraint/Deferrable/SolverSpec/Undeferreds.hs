{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Data.Constraint.Deferrable.SolverSpec.Undeferreds where

import Control.Monad (join)
import Data.Constraint.Deferrable (Deferrable (..), deferEither_, (:~:) (Refl))
import Data.Proxy (Proxy)
import Data.Type.Equality (TestEquality (testEquality))
import Data.TypeLevel.Known (sKnownVal')
import GHC.TypeNats (KnownNat, Nat, natVal)
import Numeric.Natural (Natural)

class Foo env (n :: Nat) where
  knn :: Proxy env -> Proxy n -> Natural

data Dummy

instance Foo Dummy 1 where
  knn = const natVal

instance (Deferrable (KnownNat n)) => Deferrable (Foo Dummy n) where
  deferEither _ r =
    join $
      deferEither_ @(KnownNat n) $
        case testEquality (sKnownVal' @n) (sKnownVal' @1) of
          Just Refl -> Right r
          Nothing -> Left "No dictionary"
