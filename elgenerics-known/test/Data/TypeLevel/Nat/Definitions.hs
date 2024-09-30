{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -O #-}

module Data.TypeLevel.Nat.Definitions where

import Data.Proxy (Proxy)
import Data.TypeLevel.Known
import Data.TypeLevel.Nat (tnat)
import GHC.TypeLits (KnownNat, type (<=))
import Numeric.Natural (Natural)

branchTNat :: (KnownNat n, n <= 3) => Proxy n -> Natural
{-# INLINE branchTNat #-}
branchTNat (_ :: Proxy n) = case sKnownVal' @n of
  [tnat|0|] -> 0
  [tnat|1|] -> 1
  [tnat|2|] -> 2
  [tnat|3|] -> 3
  _ -> error "Could not happen!"
