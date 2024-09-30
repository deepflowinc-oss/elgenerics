{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans -dcore-lint #-}
{-# OPTIONS_GHC -fobject-code #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Data.Union.HigherKinded (
  Union,
  KnownTyList,
  inject,
  project,
  projectEither,
  Inhabited (..),
  decompose,
  fromSingleton,
  absurd,
  weaken,
  elimAll,
) where

import Control.DeepSeq
import Data.Constraint.Operators
import Data.HList.HigherKinded
import Data.Inhabited
import Data.Membership
import Data.Proxy
import Data.Sum.Class qualified as Sum
import Data.TypeLevel.List
import Data.Union.Internal
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Deriving
import Unsafe.Coerce

instance
  (All Show (Map h as), KnownTyList as) =>
  Show (Union h as)
  where
  showsPrec d = elimAll @_ @Show (showsPrec d)

instance (All NFData (Map h as), KnownTyList as) => NFData (Union h as) where
  rnf = elimAll @_ @NFData rnf

decompose :: Union h (a ': as) -> Either (Union h as) (h a)
{-# INLINE decompose #-}
decompose (Summand i v) =
  if i == 0
    then Right $ unsafeCoerce v
    else Left $ Summand (i - 1) v

inject :: forall h a as. (Member a as) => h a -> Union h as
{-# INLINE [1] inject #-}
inject a = Summand (idx @a @as) a

idx :: forall a as. (Member a as) => Word
idx = fromIntegral $ natVal $ Proxy @(Index a as)

absurd :: Union h '[] -> a
{-# INLINE absurd #-}
absurd = undefined

project :: forall h a as. (Member a as) => Union h as -> Maybe (h a)
{-# INLINE project #-}
project (Summand i v) =
  if i == idx @a @as
    then Just $ unsafeCoerce v
    else Nothing

projectEither ::
  forall h a as.
  (Member a as) =>
  Union h as ->
  Either (Union h (DeleteOne a as)) a
{-# INLINE projectEither #-}
projectEither (Summand i v) =
  let n = idx @a @as
   in if i == n
        then Right $ unsafeCoerce v
        else Left $ Summand (if i < n then i else i + 1) v

fromSingleton :: Union h '[a] -> h a
fromSingleton (Summand _ v) = unsafeCoerce v

weaken :: Union h as -> Union h (a ': as)
{-# INLINE weaken #-}
weaken (Summand i v) = Summand (i + 1) v

instance (Member a as) => Sum.HasSummand (h a) (Union h as) where
  inject' = inject
  project' = project

fromHList :: (Word, HList h as) -> Union h as
{-# INLINE fromHList #-}
fromHList (n, hl) =
  withKnownNat n $ \k ->
    Summand n $ hindex k hl

toHList ::
  forall h as.
  (KnownTyList as, All Inhabited (Map h as)) =>
  Union h as ->
  (Word, HList h as)
toHList (Summand i v) =
  (,) i $
    generate @h @as $ \pk@(Proxy :: Proxy k) ->
      let k = natVal pk
       in withMembership (elemAtMembership @k @(Map h as)) $
            if k == fromIntegral i
              then unsafeCoerce v
              else inhabitant

elimAll ::
  forall h c r as.
  (All c (Map h as), KnownTyList as) =>
  (forall x. (Member x as, c (h x)) => h x -> r) ->
  Union h as ->
  r
elimAll f (Summand k v) =
  withKnownNat k $ \(Proxy :: Proxy k) ->
    withMembershipC @c (elemAtMembership @k @(Map h as)) $
      withMembership (elemAtMembership @k @as) $
        f @(ElemAt k as) (unsafeCoerce v)

derivingUnbox
  "Union"
  [t|
    forall h as.
    ( KnownTyList as
    , All U.Unbox (Map h as)
    , All Inhabited (Map h as)
    ) =>
    Union h as ->
    (Word, HList h as)
    |]
  [|toHList|]
  [|fromHList|]
