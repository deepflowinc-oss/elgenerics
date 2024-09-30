{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Data.Membership (
  Membership,
  elemAtMembership,
  membership,
  withMembership,
  withMembershipC,
  mapMembership,
  consMembership,
  SortByWithIndex,
  Subset,
  HasElem,
  position,
  subDict,
  sortSubset,
  unsortSubset,
  Sortable,
  type (∈),
  type (⊆),
  permutation,
  permutationWith,
  fromKnownTyListC,
  fromKnownTyList,
  foldMapTyListC,
  foldMapTyList,
  foldrMTyListC,
  foldrMTyList,
  foldrTyListC,
  foldrTyList,
  foldlMTyListC',
  foldlMTyList',
  module Data.TypeLevel.Nat,
  module Data.TypeLevel.Tuple,
) where

import Control.Category.Monoid
import Data.Coerce
import Data.Constraint
import Data.Constraint.Operators
import Data.Foldable (fold)
import Data.List (elemIndex)
import Data.Maybe
import Data.Monoid (Endo (..))
import Data.Proxy
import Data.TypeLevel.List.Core
import Data.TypeLevel.List.Unsafe
import Data.TypeLevel.Nat
import Data.TypeLevel.Ord
import Data.TypeLevel.Tuple
import GHC.Exts
import Unsafe.Coerce

newtype Membership (a :: k) (as :: [k]) = Membership Word

instance Show (Membership a as) where
  showsPrec _ (Membership i) = showChar '@' . shows i

membership :: forall a as. (Member a as) => Membership a as
membership = Membership $ fromIntegral $ natVal $ Proxy @(Index a as)

mapMembership :: forall h a as. Membership a as -> Membership (h a) (Map h as)
mapMembership = coerce

type a ∈ as = Member a as

type as ⊆ bs = Subset as bs

type Subset as bs = All (HasElem bs) as

newtype WrapM a as r = WrapM ((Member a as) => r)

withMembership ::
  forall a as r.
  Membership a as ->
  ((Member a as) => r) ->
  r
withMembership (Membership a) f =
  unsafeCoerce (WrapM @a @as @r f) (fromIntegral a :: Natural)

withMembershipC ::
  forall c a as r.
  (All c as) =>
  Membership a as ->
  ((c a, Member a as) => r) ->
  r
withMembershipC mem f = withMembership mem $ f \\ subDict @c @a @as

position :: forall a as. (Member a as) => Word
position = fromIntegral $ natVal (Proxy @(Index a as))

subDict ::
  forall c a as.
  (All c as, Member a as)
    :- c a
subDict = Sub $ elimByAll @c @a @as Dict

elemAtMembership :: forall n as. (KnownNat n) => Membership (ElemAt n as) as
elemAtMembership = Membership $ fromIntegral $ natVal $ Proxy @n

fromKnownTyListC ::
  forall c as r proxy.
  (All c as) =>
  (forall x. (Member x as, c x) => Proxy x -> r) ->
  proxy as ->
  [r]
fromKnownTyListC f _ =
  map
    ( \(ElemDict (_ :: Proxy# x) w (Dict :: Dict (c x))) ->
        unsafeWithKnownMember @x @as w $
          f (Proxy @x)
    )
    $ genDicts @c @as

fromKnownTyList ::
  forall as r proxy.
  (KnownTyList as) =>
  (forall x. (Member x as) => Proxy x -> r) ->
  proxy as ->
  [r]
fromKnownTyList f _ =
  [ withKnownNat (fromIntegral n) $ \(Proxy :: Proxy n) ->
    withMembership (elemAtMembership @n @as) $
      f (Proxy @(ElemAt n as))
  | n <- [0 .. fromIntegral (natVal @(Length as) Proxy) - 1 :: Int]
  ]

foldMapTyList ::
  forall as w proxy.
  (KnownTyList as, Monoid w) =>
  (forall x. (Member x as) => Proxy x -> w) ->
  proxy as ->
  w
foldMapTyList f = fold . fromKnownTyList @as f

foldMapTyListC ::
  forall c as w proxy.
  (KnownTyList as, All c as, Monoid w) =>
  (forall x. (Member x as, c x) => Proxy x -> w) ->
  proxy as ->
  w
foldMapTyListC f = fold . fromKnownTyListC @c @as f

foldrMTyListC ::
  forall c as m b proxy.
  (KnownTyList as, All c as, Monad m) =>
  (forall x. (Member x as, c x) => Proxy x -> b -> m b) ->
  b ->
  proxy as ->
  m b
foldrMTyListC f =
  flip $
    appEndoM . foldMapTyListC @c (\p -> EndoM $ f p)

foldrMTyList ::
  forall as m b proxy.
  (KnownTyList as, Monad m) =>
  (forall x. (Member x as) => Proxy x -> b -> m b) ->
  b ->
  proxy as ->
  m b
foldrMTyList f =
  flip $
    appEndoM . foldMapTyList (\p -> EndoM $ f p)

foldrTyList ::
  forall as b proxy.
  (KnownTyList as) =>
  (forall x. (Member x as) => Proxy x -> b -> b) ->
  b ->
  proxy as ->
  b
foldrTyList f =
  flip $
    appEndo . foldMapTyList (\p -> Endo $ f p)

foldrTyListC ::
  forall c as b proxy.
  (KnownTyList as, All c as) =>
  (forall x. (Member x as, c x) => Proxy x -> b -> b) ->
  b ->
  proxy as ->
  b
foldrTyListC f =
  flip $
    appEndo . foldMapTyListC @c (\p -> Endo $ f p)

foldlMTyListC' ::
  forall c as m b proxy.
  (KnownTyList as, All c as, Monad m) =>
  (forall x. (Member x as, c x) => Proxy x -> b -> m b) ->
  b ->
  proxy as ->
  m b
foldlMTyListC' f = \z0 ps ->
  foldrTyListC @c (\p k z -> (k $!) =<< f p z) return ps z0

foldlMTyList' ::
  forall as m b proxy.
  (KnownTyList as, Monad m) =>
  (forall x. (Member x as) => Proxy x -> b -> m b) ->
  b ->
  proxy as ->
  m b
foldlMTyList' f = \z0 ps ->
  foldrTyList (\p k z -> (k $!) =<< f p z) return ps z0

class (Member a xs) => HasElem xs a

instance (Member a xs) => HasElem xs a

permutation ::
  forall xs ys.
  (Subset xs ys) =>
  [Word]
permutation =
  fromKnownTyListC @(HasElem ys) @xs
    (\(Proxy :: (HasElem ys x) => Proxy x) -> position @x @ys)
    Proxy

permutationWith ::
  forall xs ys.
  (KnownTyList xs) =>
  (forall x. (Member x xs) => Proxy x -> Membership x ys) ->
  [Word]
{-# INLINE permutationWith #-}
permutationWith pos =
  fromKnownTyList @xs
    (\(Proxy :: Proxy x) -> coerce $ pos $ Proxy @x)
    Proxy

type SortByWithIndex cmp xs =
  SortBy (Comparing2 cmp Snd1) (Indexed xs)

type Sortable cmp xs =
  (All KnownNat (MapApply Fst1 (SortByWithIndex cmp xs)))

natListVal :: (All KnownNat xs) => Proxy xs -> [Natural]
natListVal = fromKnownTyListC @KnownNat natVal

sortSubset ::
  forall cmp x xs.
  (Member x xs, Sortable cmp xs) =>
  Membership x (SortBy cmp xs)
sortSubset =
  let is = natListVal @(MapApply Fst1 (SortByWithIndex cmp xs)) Proxy
      Membership i = membership @x @xs
   in Membership (fromIntegral $ fromJust $ elemIndex (fromIntegral i) is)

unsortSubset ::
  forall cmp x xs.
  (Member x (SortBy cmp xs), Sortable cmp xs) =>
  Membership x xs
unsortSubset =
  let is = natListVal @(MapApply Fst1 (SortByWithIndex cmp xs)) Proxy
      Membership i = membership @x @(SortBy cmp xs)
   in Membership $ fromIntegral (is !! fromIntegral i)

consMembership :: forall z ys w. (Member z ys) => Membership z (w ': ys)
consMembership = withTailMember @z @ys @w membership
