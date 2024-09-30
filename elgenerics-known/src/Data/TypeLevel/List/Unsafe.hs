{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}

module Data.TypeLevel.List.Unsafe (
  unsafeWithKnownTyListBy,
  unsafeWithKnownMember,
) where

import Data.TypeLevel.List.Core
import GHC.TypeLits
import Unsafe.Coerce

newtype WrapLen as r
  = WrapLen ((KnownNat (Length as)) => r)

unsafeWithKnownTyListBy ::
  forall as bs r.
  (KnownNat (Length bs)) =>
  ((KnownNat (Length as)) => r) ->
  r
{-# INLINE unsafeWithKnownTyListBy #-}
unsafeWithKnownTyListBy f =
  let len = tyListLength @bs
   in unsafeCoerce
        (WrapLen @as f)
        (fromIntegral len :: Natural)

newtype WrapMem x as r
  = WrapMem ((Member x as) => r)

unsafeWithKnownMember ::
  forall x as r.
  Natural ->
  ((Member x as) => r) ->
  r
{-# INLINE unsafeWithKnownMember #-}
unsafeWithKnownMember n f =
  unsafeCoerce
    (WrapMem @x @as f)
    n
