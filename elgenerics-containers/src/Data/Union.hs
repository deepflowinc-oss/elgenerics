{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -funbox-strict-fields -Wno-orphans #-}

module Data.Union (
  Union,
  KnownTyList,
  inject,
  project,
  projectEither,
  Inhabited (..),
  IsSum (..),
  decompose,
  fromSingleton,
  absurd,
  weaken,
  elimAll,
) where

import Data.Coerce
import Data.Constraint.Operators
import Data.Functor.Identity
import Data.Inhabited
import Data.Kind (Type)
import Data.Membership
import Data.Proxy
import Data.TypeLevel.List
import Data.Union.HigherKinded qualified as HK
import Data.Union.Internal qualified as HK
import GHC.Generics
import Unsafe.Coerce

type Union = HK.Union Identity

decompose :: forall a as. Union (a ': as) -> Either (Union as) a
{-# INLINE decompose #-}
decompose = coerce $ HK.decompose @Identity @a @as

inject :: forall a as. (Member a as) => a -> Union as
{-# INLINE [1] inject #-}
inject = HK.inject . Identity

absurd :: Union '[] -> a
{-# INLINE absurd #-}
absurd = HK.absurd

project :: forall a as. (Member a as) => Union as -> Maybe a
{-# INLINE project #-}
project = coerce @(Maybe (Identity a)) . HK.project

projectEither ::
  forall a as.
  (Member a as) =>
  Union as ->
  Either (Union (DeleteOne a as)) a
{-# INLINE projectEither #-}
projectEither = coerce $ HK.projectEither @Identity @a @as

fromSingleton :: forall a. Union '[a] -> a
{-# INLINE fromSingleton #-}
fromSingleton = coerce $ HK.fromSingleton @Identity @a

weaken :: Union as -> Union (a ': as)
{-# INLINE weaken #-}
weaken = HK.weaken

class IsSum c where
  type Summands c :: [Type]
  type Summands c = GSums (Rep c)
  toOpenUnion :: c -> Union (Summands c)
  default toOpenUnion ::
    (Generic c, GIsSum (Rep c), GSums (Rep c) ~ Summands c) =>
    c ->
    Union (Summands c)
  toOpenUnion = gToUnion . from
  fromOpenUnion :: Union (Summands c) -> c
  default fromOpenUnion ::
    (Generic c, GIsSum (Rep c), GSums (Rep c) ~ Summands c) =>
    Union (Summands c) ->
    c
  fromOpenUnion = to . gFromUnion

instance IsSum (Either a b)

class GIsSum f where
  type GSums f :: [Type]
  gToUnion :: f () -> Union (GSums f)
  gFromUnion :: Union (GSums f) -> f ()

instance GIsSum (K1 i c) where
  type GSums (K1 i c) = '[c]
  gToUnion = HK.Summand 0
  {-# INLINE gToUnion #-}
  gFromUnion (HK.Summand _ v) = K1 $ unsafeCoerce v
  {-# INLINE gFromUnion #-}

shiftIdx :: Word -> Union as -> Union bs
{-# INLINE shiftIdx #-}
shiftIdx i (HK.Summand j v) = HK.Summand (i + j) v

instance (KnownNat (Length (GSums f)), GIsSum f, GIsSum g) => GIsSum (f :+: g) where
  type GSums (f :+: g) = GSums f ++ GSums g
  gToUnion (L1 f) = shiftIdx 0 $ gToUnion f
  gToUnion (R1 g) =
    shiftIdx (fromIntegral $ natVal $ Proxy @(Length (GSums f))) $
      gToUnion g
  gFromUnion (HK.Summand i v) =
    let offset = fromIntegral (natVal $ Proxy @(Length (GSums f)))
     in if i < offset
          then L1 $ gFromUnion (HK.Summand i v)
          else R1 $ gFromUnion (HK.Summand (i - offset) v)

instance (GIsSum f) => GIsSum (M1 i c f) where
  type GSums (M1 i c f) = GSums f
  gToUnion = gToUnion . unM1
  gFromUnion = M1 . gFromUnion

elimAll ::
  forall c r as.
  (All c as) =>
  (forall x. (Member x as, c x) => x -> r) ->
  Union as ->
  r
elimAll f (HK.Summand k v) =
  withKnownNat k $ \(Proxy :: Proxy k) ->
    withMembershipC @c (elemAtMembership @k @as) $
      f @(ElemAt k as) (unsafeCoerce v)

instance
  {-# OVERLAPPING #-}
  (All Show as) =>
  Show (Union as)
  where
  showsPrec d = elimAll @Show (showsPrec d)
