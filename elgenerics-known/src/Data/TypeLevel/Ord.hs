{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.TypeLevel.Ord (
  Ordering (..),
  type LT,
  type EQ,
  type GT,
  Compare2,
  Compare1,
  Max,
  Min,
  Comparing,
  Comparing1,
  Comparing2,
  Comparing3,
  Comparing4,
  POrd (..),
  SOrd (..),
  sCaseOrdering,
  SortedBy,
  Sorted,
  Merge,
  sLex,
  Lex,
  Lex2,
  Lex1,
  CaseOrdering,
) where

import Data.Kind
import Data.TypeLevel.Bool
import Data.TypeLevel.Function
import Data.TypeLevel.Known
import Data.TypeLevel.Monoid
import Data.TypeLevel.Nat
import Data.TypeLevel.Ord.Internal
import Data.TypeLevel.Typeable
import Data.Void (Void)
import GHC.TypeLits as TL
import Unsafe.Coerce (unsafeCoerce)

type family Lex (l :: Ordering) (r :: Ordering) :: Ordering where
  Lex LT _ = LT
  Lex EQ r = r
  Lex GT _ = GT

data Lex2 :: Ordering ~> Ordering ~> Ordering

data Lex1 (l :: Ordering) :: Ordering ~> Ordering

type instance Apply Lex2 l = Lex1 l

type instance Apply (Lex1 l) r = Lex l r

type Max n m = CaseOrdering (Compare n m) m m n

type Min n m = CaseOrdering (Compare n m) n n m

instance PSemigroup Ordering where
  type Mappend l r = Lex l r

instance PMonoid Ordering where
  type Mempty = EQ

class POrd a where
  type Compare (l :: a) (r :: a) :: Ordering

data Compare2 :: k ~> k ~> Ordering

data Compare1 (a :: k) :: k ~> Ordering

type instance Apply Compare2 a = Compare1 a

type instance Apply (Compare1 a) b = Compare a b

type family CmpList l r where
  CmpList '[] '[] = EQ
  CmpList '[] (_ ': _) = LT
  CmpList (_ ': _) '[] = GT
  CmpList (a ': as) (b ': bs) = Compare a b <> CmpList as bs

instance (POrd a) => POrd [a] where
  type Compare l r = CmpList l r

instance POrd Nat where
  type Compare a b = CmpNat a b

instance POrd Symbol where
  type Compare a b = CmpSymbol a b

type family CmpMaybe l r where
  CmpMaybe 'Nothing 'Nothing = EQ
  CmpMaybe 'Nothing ('Just _) = LT
  CmpMaybe ('Just _) 'Nothing = GT
  CmpMaybe ('Just l) ('Just r) = Compare l r

instance (POrd a) => POrd (Maybe a) where
  type Compare l r = CmpMaybe l r

instance POrd PTypeRep where
  type Compare l r = CmpTypeRep l r

instance POrd Type where
  type Compare l r = Compare (TypeRepOf l) (TypeRepOf r)

class (SortedByAux cmp as) => SortedBy cmp as

instance (SortedByAux cmp as) => SortedBy cmp as

type family
  SortedByAux
    (cmp :: k ~> k ~> Ordering)
    (ks :: [k]) ::
    Constraint
  where
  SortedByAux _ '[] = ()
  SortedByAux _ '[x] = ()
  SortedByAux cmp (a ': b ': as) =
    CaseOrdering
      (Apply (Apply cmp a) b)
      (SortedByAux cmp (b ': as))
      (SortedByAux cmp (b ': as))
      (Throw ('Text "List not sorted: " ':<>: 'ShowType (a ': b ': as)))

type Sorted xs = SortedBy Compare2 xs

type family Throw m where
  Throw m = TypeError m

instance (POrd a, POrd b) => POrd (a, b) where
  type Compare l r = CmpTuple l r

type family CmpTuple (l :: (a, b)) (r :: (a, b)) :: Ordering where
  CmpTuple '(a, b) '(c, d) = Compare a c `Lex` Compare b d

type Comparing cmp f x y = (Apply (Apply cmp (Apply f x)) (Apply f y) :: Ordering)

data Comparing4 :: (k' ~> k' ~> Ordering) ~> (k ~> k') ~> (k ~> k ~> Ordering)

data Comparing3 (cmp :: k' ~> k' ~> Ordering) :: (k ~> k') ~> (k ~> k ~> Ordering)

data Comparing2 (cmp :: k' ~> k' ~> Ordering) (map :: (k ~> k')) :: (k ~> k ~> Ordering)

data Comparing1 (cmp :: k' ~> k' ~> Ordering) (map :: (k ~> k')) (x :: k) :: (k ~> Ordering)

type instance Apply Comparing4 cmp = Comparing3 cmp

type instance Apply (Comparing3 cmp) f = Comparing2 cmp f

type instance Apply (Comparing2 cmp f) x = Comparing1 cmp f x

type instance Apply (Comparing1 cmp f x) y = Comparing cmp f x y

type family Merge xs ys where
  Merge '[] ys = ys
  Merge xs '[] = xs
  Merge (x ': xs) (y ': ys) =
    MergeAux (Compare x y) x y xs ys

type family MergeAux cmp x y xs ys where
  MergeAux 'LT x y xs ys = x ': Merge xs (y ': ys)
  MergeAux 'EQ x y xs ys = x ': Merge xs ys
  MergeAux 'GT x y xs ys = y ': Merge (x ': xs) ys

class SOrd k where
  sCompare :: Sing (l :: k) -> Sing (r :: k) -> Sing (Compare l r)

instance SOrd Nat where
  {-# INLINE sCompare #-}
  sCompare (n :: SNat n) (m :: SNat m) =
    case compare (knownNatVal n) (knownNatVal m) of
      LT -> unsafeCoerce SLT
      EQ -> unsafeCoerce SEQ
      GT -> unsafeCoerce SGT

instance SOrd Symbol where
  {-# INLINE sCompare #-}
  sCompare (n :: SSymbol n) (m :: SSymbol m) =
    case compare (knownSymbolVal n) (knownSymbolVal m) of
      LT -> unsafeCoerce SLT
      EQ -> unsafeCoerce SEQ
      GT -> unsafeCoerce SGT

instance (SOrd k) => SOrd [k] where
  {-# INLINE sCompare #-}
  sCompare SNil SNil = SEQ
  sCompare SNil (:%) {} = SLT
  sCompare (:%) {} SNil = SGT
  sCompare (x :% xs) (y :% ys) =
    sCompare x y `sLex` sCompare xs ys

instance (SOrd k, SOrd k') => SOrd (k, k') where
  sCompare (SPair a b) (SPair a' b') =
    sCompare a a' `sLex` sCompare b b'
  {-# INLINE sCompare #-}

instance SOrd PTypeRep where
  sCompare l r =
    case sTestEquality l r of
      Equal -> SEQ
      NonEqual -> case (l, r) of
        (STySym s, STySym t) -> sCompare s t
        (STySym _, STyNat {}) -> SLT
        (STySym _, SCon {}) -> SLT
        (STySym _, STyApp {}) -> SLT
        (STySym _, STyFun {}) -> SLT
        (STyNat n, STyNat m) -> sCompare n m
        (STyNat {}, STySym {}) -> SGT
        (STyNat {}, SCon {}) -> SLT
        (STyNat {}, STyApp {}) -> SLT
        (STyNat {}, STyFun {}) -> SLT
        (SCon a b c, SCon x y z) ->
          sCompare a x
            `sLex` sCompare b y
            `sLex` sCompare c z
        (SCon {}, STySym {}) -> SGT
        (SCon {}, STyNat {}) -> SGT
        (SCon {}, STyApp {}) -> SLT
        (SCon {}, STyFun {}) -> SLT
        (STyApp f x, STyApp g y) ->
          sCompare f g `sLex` sCompare x y
        (STyApp {}, STyFun {}) -> SLT
        (STyApp {}, STySym {}) -> SGT
        (STyApp {}, STyNat {}) -> SGT
        (STyApp {}, SCon {}) -> SGT
        (STyFun a b, STyFun a' b') ->
          sCompare a a' `sLex` sCompare b b'
        (STyFun {}, STySym {}) -> SGT
        (STyFun {}, STyNat {}) -> SGT
        (STyFun {}, SCon {}) -> SGT
        (STyFun {}, STyApp {}) -> SGT

instance SOrd Type where
  sCompare l r =
    sTypeRepOf l `sCompare` sTypeRepOf r

infixr 9 `sLex`

sLex :: Sing l -> Sing (q :: Ordering) -> Sing (l `Lex` q)
sLex SLT _ = SLT
sLex SEQ r = r
sLex SGT _ = SGT

sCaseOrdering ::
  SOrdering ord ->
  Sing lt ->
  Sing eq ->
  Sing gt ->
  Sing (CaseOrdering ord lt eq gt)
{-# INLINE sCaseOrdering #-}
sCaseOrdering SLT lt _ _ = lt
sCaseOrdering SEQ _ eq _ = eq
sCaseOrdering SGT _ _ gt = gt

instance POrd Void where
  type Compare b b' = CmpVoid b b'

type family CmpVoid (bo :: Void) (bot' :: Void) :: Ordering where

instance SOrd Void where
  sCompare = \case {}

instance POrd Bool where
  type Compare a b = CmpBool a b

instance SOrd Bool where
  sCompare = sCmpBool
