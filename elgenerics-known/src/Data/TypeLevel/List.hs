{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Data.TypeLevel.List (
  Index,
  Snoc,
  DeleteOne,
  Length,
  Length1,
  Map,
  Zip,
  Sum,
  Take,
  Drop,
  Sliced,
  NotElem,
  Replicate,
  mapApplyAppend,
  KnownTyList,
  All,
  SplitAt,
  MergeBy,
  InsertBy,
  CmpSymbol2,
  CmpSymbol1,
  SortBy,
  Indexed,
  sIndexed,
  Member,
  Matches,
  Matches1,
  CatMaybes,
  CatMaybes1,
  Applies,
  Applies2,
  Applies1,
  AppliesCon,
  AppliesCon2,
  AppliesCon1,
  mapKnownTyList,
  mapApplyKnownTyList,
  tyListLength,
  tyListSkeleton,
  takeMapApply,
  sortKnownTyList,
  indexKnownTyList,
  dropMapApply,
  sortIdemp,
  ElemAt,
  Apply,
  MapApply,
  MapApply1,
  type (++),
  (%++),
  Concat,
  ConcatMapApply,
  elemAtReplicate,
  appendEmptyL,
  elemAtZip,
  elemAtMap,
  elemAtMapApply,
  withTailMember,
  elemAtIndex,
  allAppendDict,
  withAllAppend,
  ZipWithSame,
  ZipSame,
  ZipWith,
  KnownNatList,
  natListVal,
  KnownSymbolList,
  KnownTypeableList,
  sLength,
  module Data.TypeLevel.List.Properties,
  module Data.Membership,
) where

import Data.Constraint
import Data.Constraint.Operators
import Data.Membership
import Data.Type.Equality
import Data.TypeLevel.Function
import Data.TypeLevel.Known
import Data.TypeLevel.List.Core
import Data.TypeLevel.List.Overloaded ()
import Data.TypeLevel.List.Properties
import Data.TypeLevel.List.Unsafe
import Data.TypeLevel.Ord.Internal
import GHC.TypeLits hiding (natVal)
import Type.Reflection
import Unsafe.Coerce

type family DeleteOne (a :: k) (as :: [k]) where
  DeleteOne a (a ': as) = as
  DeleteOne a (b ': as) = b ': DeleteOne a as
  DeleteOne _ '[] = '[]

indexKnownTyList ::
  forall as r.
  (KnownTyList as) =>
  ((KnownTyList (Indexed as)) => r) ->
  r
{-# INLINE indexKnownTyList #-}
indexKnownTyList =
  unsafeWithKnownTyListBy @(Indexed as) @as

mapKnownTyList ::
  forall h as r.
  (KnownTyList as) =>
  ((KnownTyList (Map h as)) => r) ->
  r
mapKnownTyList =
  unsafeWithKnownTyListBy @(Map h as) @as

sortKnownTyList ::
  forall cmp as r.
  (KnownTyList as) =>
  ((KnownTyList (SortBy cmp as)) => r) ->
  r
sortKnownTyList =
  unsafeWithKnownTyListBy @(SortBy cmp as) @as

mapApplyKnownTyList ::
  forall h as r.
  (KnownTyList as) =>
  ((KnownTyList (MapApply h as)) => r) ->
  r
mapApplyKnownTyList =
  unsafeWithKnownTyListBy @(MapApply h as) @as

type family Zip as bs where
  Zip as '[] = '[]
  Zip '[] bs = '[]
  Zip (a ': as) (b ': bs) = (a, b) ': Zip as bs

elemAtZip :: forall k as bs. ElemAt k (Zip as bs) :~: (ElemAt k as, ElemAt k bs)
elemAtZip = unsafeCoerce $ Refl @()

elemAtMap :: forall k f as. ElemAt k (Map f as) :~: f (ElemAt k as)
elemAtMap = unsafeCoerce $ Refl @()

elemAtMapApply :: forall k f as. ElemAt k (MapApply f as) :~: Apply f (ElemAt k as)
elemAtMapApply = unsafeCoerce $ Refl @()

elemAtIndex :: forall x xs. ElemAt (Index x xs) xs :~: x
elemAtIndex = unsafeCoerce $ Refl @()

type family Concat (as :: [[k]]) :: [k] where
  Concat '[] = '[]
  Concat (as ': ass) = as ++ Concat ass

appendEmptyL ::
  forall xs. '[] ++ xs :~: xs
appendEmptyL = unsafeCoerce $ Refl @()

type ConcatMapApply (f :: k ~> [k1]) (as :: [k]) = Concat (MapApply f as)

type family CatMaybes (ms :: [Maybe k]) :: [k] where
  CatMaybes '[] = '[]
  CatMaybes ('Just x ': xs) = x ': CatMaybes xs
  CatMaybes (_ ': xs) = CatMaybes xs

data CatMaybes1 :: [Maybe k] ~> [k]

type instance Apply CatMaybes1 a = CatMaybes a

type family Sum (ns :: [Nat]) :: Nat where
  Sum '[] = 0
  Sum (n ': ns) = n + Sum ns

type SplitAt n xs = '(Take n xs, Drop n xs)

type family Sliced (ls :: [Nat]) (as :: [k]) :: [[k]] where
  Sliced '[] _ = '[]
  Sliced (n ': ns) xs = Take n xs ': Sliced ns (Drop n xs)

type KnownNatList ns = (All KnownNat ns)

natListVal :: forall ns proxy. (KnownNatList ns) => proxy ns -> [Word]
natListVal = fromKnownTyListC @KnownNat (fromIntegral . natVal)

type KnownSymbolList ns = (All KnownSymbol ns)

type KnownTypeableList ns = (All Typeable ns)

type family ZipWithSame (f :: a -> b -> c) (as :: [a]) (bs :: [b]) :: [c] where
  ZipWithSame _ '[] '[] = '[]
  ZipWithSame f (a ': as) (b ': bs) = f a b ': ZipWithSame f as bs
  ZipWithSame _ as bs =
    TypeError
      ( 'Text "Zipping lists of different length: "
          ':<>: 'ShowType as
          ':<>: 'Text " with "
          ':<>: 'ShowType bs
      )

type ZipSame as bs = ZipWithSame (,) as bs

data CmpSymbol2 :: Symbol ~> Symbol ~> Ordering

data CmpSymbol1 (s :: Symbol) :: Symbol ~> Ordering

type instance Apply CmpSymbol2 s = CmpSymbol1 s

type instance Apply (CmpSymbol1 s) t = CmpSymbol s t

type family NotElem a as :: Constraint where
  NotElem a (a ': as) =
    TypeError
      ('Text "A type " ':<>: 'ShowType a ':<>: 'Text " already in entry")
  NotElem a (_ ': as) = NotElem a as
  NotElem _ '[] = ()

type family InsertBy cmp x xs where
  InsertBy _ x '[] = '[x]
  InsertBy cmp x (y ': ys) =
    CaseOrdering
      (Apply (Apply cmp x) y)
      (x ': y ': ys)
      (y ': ys)
      (y ': InsertBy cmp x ys)

type family Replicate (n :: Nat) (x :: k) :: [k] where
  Replicate 0 _ = '[]
  Replicate n x = x ': Replicate (n - 1) x

elemAtReplicate ::
  forall n k t. ElemAt k (Replicate n t) :~: t
elemAtReplicate = unsafeCoerce (Refl @())

mapApplyAppend ::
  MapApply f (xs ++ ys) :~: (MapApply f xs ++ MapApply f ys)
mapApplyAppend = unsafeCoerce $ Refl @()

takeMapApply ::
  forall f n xs. MapApply f (Take n xs) :~: Take n (MapApply f xs)
takeMapApply = unsafeCoerce $ Refl @()

dropMapApply ::
  forall f n xs. MapApply f (Drop n xs) :~: Drop n (MapApply f xs)
dropMapApply = unsafeCoerce $ Refl @()

type family ZipWith (f :: a ~> b ~> c) (as :: [a]) (bs :: [b]) :: [c] where
  ZipWith _ '[] _ = '[]
  ZipWith _ _ '[] = '[]
  ZipWith f (a ': as) (b ': bs) = Apply (Apply f a) b ': ZipWith f as bs

sortIdemp ::
  forall cmp xs.
  SortBy cmp (SortBy cmp xs)
    :~: SortBy cmp xs
sortIdemp = unsafeCoerce $ Refl @()

type family Applies (fs :: [k -> k]) (k0 :: k) :: k where
  Applies '[] k0 = k0
  Applies (f ': fs) k0 = f (Applies fs k0)

data Applies2 :: [k -> k] ~> k ~> k

data Applies1 (fs :: [k -> k]) :: k ~> k

type instance Apply Applies2 fs = Applies1 fs

type instance Apply (Applies1 fs) a = Applies fs a

type family AppliesCon (fs :: [k ~> k]) (z :: k) :: k where
  AppliesCon '[] x = x
  AppliesCon (f ': fs) x = Apply f (AppliesCon fs x)

data AppliesCon2 :: [k ~> k] ~> k ~> k

data AppliesCon1 (fs :: [k ~> k]) :: k ~> k

type instance Apply AppliesCon2 fs = AppliesCon1 fs

type instance Apply (AppliesCon1 fs) x = AppliesCon fs x

sLength :: SList xs -> SNat (Length xs)
sLength SNil = sKnownVal'
sLength (_ :% rest) = sKnownVal' @1 %+ sLength rest

sIndexed :: SList xs -> SList (Indexed xs)
sIndexed = sIndexedAux $ sKnownVal' @0

sIndexedAux :: SNat n -> SList xs -> SList (IndexedAux n xs)
sIndexedAux _ SNil = SNil
sIndexedAux n (x :% xs) =
  SPair n x :% sIndexedAux (n %+ sKnownVal' @1) xs

infixr 5 %++

(%++) :: SList xs -> SList ys -> SList (xs ++ ys)
SNil %++ ys = ys
(x :% xs) %++ ys = x :% (xs %++ ys)

allAppendDict ::
  forall c xs ys.
  (KnownTyList xs, KnownTyList ys, All c xs, All c ys) =>
  Dict (All c (xs ++ ys))
allAppendDict = go (tyListSkeleton @xs) (tyListSkeleton @ys)
  where
    go ::
      (All c as, All c bs) =>
      PList as ->
      PList bs ->
      Dict (All c (as ++ bs))
    go PNil _ = Dict
    go (PCons _ xs) ys = withDict (go xs ys) Dict

withAllAppend ::
  forall c xs ys r.
  (KnownTyList xs, KnownTyList ys, All c xs, All c ys) =>
  ((All c (xs ++ ys)) => r) ->
  r
withAllAppend = withDict (allAppendDict @c @xs @ys)
