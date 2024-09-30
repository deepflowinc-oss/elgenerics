{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Data.TypeLevel.List.Core where

import Data.TypeLevel.Function
import Data.TypeLevel.Ord.Internal
import GHC.Exts
import GHC.TypeLits
import Unsafe.Coerce (unsafeCoerce)

type family Length (as :: [k]) where
  Length '[] = 0
  Length (_ ': as) = 1 + Length as

data Length1 :: [k] ~> Nat

type instance Apply Length1 ks = Length ks

type SortBy cmp ks = SortByAux cmp (Length ks) ks

type family SortByAux cmp n ks where
  SortByAux _ _ '[] = '[]
  SortByAux _ _ '[x] = '[x]
  SortByAux cmp n xs =
    MergeBy
      cmp
      (SortByAux cmp (n `Div` 2) (Take (n `Div` 2) xs))
      (SortByAux cmp (n - (n `Div` 2)) (Drop (n `Div` 2) xs))

type family Take (n :: Nat) (as :: [k]) :: [k] where
  Take 0 _ = '[]
  Take n (x ': xs) = x ': Take (n - 1) xs
  Take _ _ = '[]

type family Drop (n :: Nat) (as :: [k]) :: [k] where
  Drop 0 xs = xs
  Drop n (x ': xs) = Drop (n - 1) xs
  Drop _ '[] = '[]

type family
  MergeBy
    (cmp :: k ~> k ~> Ordering)
    (ls :: [k])
    (rs :: [k]) ::
    [k]
  where
  MergeBy _ '[] rs = rs
  MergeBy _ ls '[] = ls
  MergeBy cmp (x ': xs) (y ': ys) =
    CaseOrdering
      (Apply (Apply cmp x) y)
      (x ': MergeBy cmp xs (y ': ys))
      (x ': y ': MergeBy cmp xs ys)
      (y ': MergeBy cmp (x ': xs) ys)

type family ElemAt (n :: Nat) ts where
  ElemAt 0 (t ': ts) = t
  ElemAt n (_ ': ts) = ElemAt (n - 1) ts
  ElemAt _ _ = TypeError ('Text "Index out of bounds")

type Index (a :: k) (ts :: [k]) = Index' a ts '[]

type family Index' (a :: k) (ts :: [k]) (rs :: [k]) where
  Index' a (a ': _) _ = 0
  Index' a (b ': as) rs = 1 + Index' a as (Snoc rs b)
  Index' a '[] rs =
    TypeError
      ( 'Text "A type `"
          ':<>: 'ShowType a
          ':<>: 'Text "' is not an element of "
          ':<>: 'ShowType rs
      )

type family Snoc (rs :: [k]) (a :: k) where
  Snoc '[] a = '[a]
  Snoc (b ': bs) a = b ': Snoc bs a

type Member a as = (KnownNat (Index a as))

type family MapApply (n :: k ~> k') (as :: [k]) :: [k'] where
  MapApply _ '[] = '[]
  MapApply n (a ': as) = Apply n a ': MapApply n as

data MapApply1 (f :: k ~> k') :: [k] ~> [k']

type instance Apply (MapApply1 f) xs = MapApply f xs

type family Map f as where
  Map _ '[] = '[]
  Map f (a ': as) = f a ': Map f as

type family (++) as bs where
  (a ': as) ++ bs = a ': (as ++ bs)
  '[] ++ bs = bs

type Indexed (as :: [a]) = IndexedAux 0 as

type family IndexedAux n xs where
  IndexedAux _ '[] = '[]
  IndexedAux n (x ': xs) = '(n, x) ': IndexedAux (n + 1) xs

type KnownTyList xs = KnownNat (Length xs)

data PList (xs :: [k]) where
  PNil :: PList '[]
  PCons :: Proxy# x -> PList xs -> PList (x ': xs)

tyListSkeleton ::
  forall xs.
  (KnownTyList xs) =>
  PList xs
tyListSkeleton = go (tyListLength @xs)
  where
    go :: forall ys. Word -> PList ys
    {-# INLINE go #-}
    go !0 = unsafeCoerce $ PNil
    go n = unsafeCoerce $ PCons (proxy# :: Proxy# Any) $ go (n - 1)

tyListLength :: forall xs. (KnownTyList xs) => Word
tyListLength = fromIntegral $ natVal' @(Length xs) proxy#

type family Matches x xs where
  Matches x (x ': xs) = x ': Matches x xs
  Matches x (_ ': xs) = Matches x xs
  Matches _ '[] = '[]

data Matches1 (x :: k) :: [k] ~> [k]

type instance Apply (Matches1 x) xs = Matches x xs
