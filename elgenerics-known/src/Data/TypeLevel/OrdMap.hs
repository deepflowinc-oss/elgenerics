{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall -Wno-orphans -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fprint-explicit-kinds -fprint-explicit-foralls #-}

module Data.TypeLevel.OrdMap (
  OrdMap,
  type Branch,
  type Leaf,
  ToList,
  FromList,
  FromAscList,
  UnsafeFromAscList,
  sFromList,
  sToList,
  UnsafeFromAscListOfSize,
  Member,
  NotMember,
  Singleton,
  sSingleton,
  Empty,
  sEmpty,
  type Null,
  sNull,
  Insert,
  sInsert,
  Index,
  IndexM,
  Equivalent,
  Equivalent',
  sEquivalent,
  Equivalence (..),
  SEquivalence (..),
  AlignOM,
  sAlignOM,
  Split,
  sSplit,
  Join,
  sJoin,
  ThenEqv,
  sThenEqv,
  Disjoint,
  sDisjoint,
  Disjointness (..),
  SDisjointness (..),
  MergePerm,
  sMergePerm,
  Size,
  sSize,
  FieldAt,
  FieldAtM,
  SField (..),
  BothC,
  FieldC,
  Color,
  SColor (..),
  B,
  R,
  RankT,
  SRankT (..),
  EntryAtM,
  EntryAt,
  Delete,
  Intersect,
  Merge,
  sMerge,
  LabelAtM,
  LabelAt,
  sFMapOM,
  MapApplyWithKey,
  MapWithKey,
  MapKeysMonotonic,
  MapApplyKeysMonotonic,
  LookupWithIndex,
  Lookup,
  Lookup',
  Field (..),
  type (:::),
  ConstField,
  ConstField1,
  ConstFields,
  ConstFields1,
  Label,
  Entry,
  sLabel,
  sEntry,
  Labels,
  Entries,
  Label',
  Entry',
  sLabels,
  sEntries,
  ConstMap,
  sConstMap,
  ConstList,
  sConstList,
  toConstListMembership,
  fromConstListMembership,
  withAllConstMap,
  sortAllDict,
  SortableList,
  SortableLabels,
  SortPermutation,
  sortPermutation,
  sSortPermutation,
  Sortedness (..),
  LabelSorted,
  memberToList,
  fieldAtToList,
  withToListMember,
  elimMemberToList,
  allOMIntro,
  allOMDictIntro,
  deferAllOMWith,
  sortAllFieldC,
  unsortMembership,
  withOrdMapMember,
  indexFieldAt,
  elemAtFieldDistrib,
  elimConstField,
  withLabelsMember,
  withUnsortedMember,
  withUnsortedMember',
  withLabelIndex,

  -- * Debug Type operators
  BlackCountInvariant,
  RedRedInvariant,
  ValidRBTree,
  Paths,
  BlackCounts,
  SOrdMap (),
  sLookupWithIndex,
  sLookupWithIndex',
  OMMembership (),
  AllOM (..),
  omMembership,
  SomeOMMember (..),
  DeferrableFor2,
  omMembership',
  allOMDict',
  CustomDict (..),
  LabelC,
  EntryC,
  foldMapOrdMap,
  foldMapOrdMapC,
  foldMapOrdMap',
  foldMapOrdMapC',
  foldrMOrdMap,
  foldrMOrdMapC,
  foldrOrdMap,
  foldrOrdMapC,
  foldlMOrdMap',
  foldlMOrdMapC',
  foldlOrdMap',
  foldlOrdMapC',
  fromLabelListMember,
  allOMToListAll,
  elimAllOM,
  allOMToAllFieldCDict,
  elimFieldCons,
  toSomeColor,
  colorVal,
  sColorVal,
  elimMaybeCLookup',

  -- * Unsafe operations
  unsafeWithOrdMapMember,
) where

import Control.Category.Monoid
import Data.Constraint
import Data.Constraint.Deferrable
import Data.Constraint.Operators
import Data.Functor ((<&>))
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Monoid (Endo (..))
import Data.Proxy
import Data.These
import Data.Type.Equality
import Data.TypeLevel.Applicative as App hiding (Empty)
import Data.TypeLevel.Function
import Data.TypeLevel.Known
import Data.TypeLevel.List hiding (Index, Member, natVal)
import Data.TypeLevel.List qualified as List
import Data.TypeLevel.List.Overloaded qualified as List
import Data.TypeLevel.List.Unsafe (unsafeWithKnownMember)
import Data.TypeLevel.Maybe hiding (type (<$>), type (<|>))
import Data.TypeLevel.Ord hiding (Merge)
import Data.TypeLevel.OrdMap.Internal
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as U
import GHC.Generics hiding (R)
import GHC.TypeLits hiding (natVal)
import GHC.TypeNats (natVal)
import Type.Reflection
import Unsafe.Coerce

data Equivalence k v
  = IsEquivalent
  | SizeMismatch Nat Nat
  | MustBeEmpty (OrdMap k v)
  | KeyNotFound k v (OrdMap k v)
  | ValueMismatch k v v (OrdMap k v, v, OrdMap k v)

defineSingletons ''Equivalence
deriveShowSing ''Equivalence
deriveKnown ''Equivalence
deriveSTestEquality ''Equivalence

infix 9 :::, :%::

data Field l k = l ::: k
  deriving (Read, Show, Eq, Ord, Typeable, Generic)

data SField (f :: Field l k) where
  (:%::) :: Sing l -> Sing k -> SField (l '::: k)

deriving instance
  (ShowSing l, ShowSing k) =>
  Show (SField (fld :: Field l k))

type instance Sing = SField

instance (Known l, Known k) => Known (l ::: k) where
  sKnownVal' = sKnownVal' @l :%:: sKnownVal' @k

instance (HasSing l, HasSing k) => HasSing (Field l k) where
  type Demote (Field l k) = Field (Demote l) (Demote k)
  promote (l ::: k) =
    case (promote l, promote k) of
      (MkSomeSing sl, MkSomeSing sk) -> MkSomeSing $ sl :%:: sk
  demote (sl :%:: sk) = demote sl ::: demote sk

instance (SingTypeable l, SingTypeable r) => SingTypeable (Field l r) where
  singTypeRep (l :%:: r) =
    withSingTypeable l $ withSingTypeable r typeRep

instance
  (STestEquality l, STestEquality k) =>
  STestEquality (Field l k)
  where
  sTestEquality = \(l :%:: k) (l' :%:: k') ->
    case (sTestEquality l l', sTestEquality k k') of
      (Equal, Equal) -> Equal
      (NonEqual, _) -> unsafeCoerce $ NonEqual @0 @1
      (_, NonEqual) -> unsafeCoerce $ NonEqual @0 @1

type (:::) = '(:::)

type Entries xs = MapApply Entry' (ToList xs)

type Labels xs = MapApply Label' (ToList xs)

type family Entry (a :: Field l k) :: k where
  Entry (_ ::: x) = x

data Entry' :: Field l k ~> k

type instance Apply Entry' a = Entry a

type family FMapApply f a where
  FMapApply f 'Leaf = 'Leaf
  FMapApply f ('Branch c n rk l k v r) =
    'Branch c n rk (FMapApply f l) k (Apply f v) (FMapApply f r)

instance PFunctor (OrdMap k) where
  type (<$>) f dic = FMapApply f dic

type family Label (a :: Field l k) :: l where
  Label (label ::: _) = label

data Label' :: Field l k ~> l

type instance Apply Label' a = Label a

type family Rank (dic :: OrdMap k v) :: RankT where
  Rank Leaf = MkRankT 1
  Rank (Branch _ _ rk _ _ _ _) = rk

type family Size (dic :: OrdMap k v) :: SizeT where
  Size 'Leaf = 0
  Size ('Branch _ n _ _ _ _ _) = n

type Leaf = 'Leaf

type Branch = 'Branch

type Empty = 'Leaf

sEmpty :: SOrdMap Empty
sEmpty = SLeaf

type family Null (dic :: OrdMap k v) where
  Null 'Leaf = 'True
  Null _ = 'False

sNull :: SOrdMap dic -> SBool (Null dic)
sNull SLeaf = STrue
sNull SBranch {} = SFalse

type Singleton k v = 'Branch 'B 1 (MkRankT 2) Leaf k v Leaf

type NotMember x xs =
  FromNothing
    ( 'Text "Key "
        ':<>: 'ShowType x
        ':<>: 'Text " must not be present in "
        ':<>: 'ShowType (ToList xs)
    )
    (() :: Constraint)
    (LookupWithIndex x xs)

type Lookup' ::
  forall k v.
  k ->
  OrdMap k v ->
  v
type Lookup' k dic =
  FromJust
    ( 'Text "Key `"
        ':<>: 'ShowType k
        ':<>: 'Text " doesn't exist in "
        ':<>: 'ShowType (ToList dic)
    )
    (Lookup k dic)

type Equivalent l r = (FromEquivalence (Equivalent' l r) :: Constraint)

type family FromEquivalence (eqv :: Equivalence k v) :: Constraint where
  FromEquivalence 'IsEquivalent = ()
  FromEquivalence ('MustBeEmpty tr) =
    TypeError ('Text "OrdMap should be empty, but got: " ':$$: 'ShowType tr)
  FromEquivalence ('SizeMismatch n m) =
    TypeError
      ( 'Text "Given OrdMaps must have the same size, but got: "
          ':<>: 'ShowType '(n, m)
      )
  FromEquivalence ('KeyNotFound k v tr') =
    TypeError
      ( 'Text "A tree must have a key-value pair"
          ':<>: 'ShowType '(k, v)
          ':$$: 'Text ", but given: "
            ':<>: 'ShowType tr'
      )
  FromEquivalence ('ValueMismatch k v v' tr') =
    TypeError
      ( 'Text "A key `"
          ':<>: 'ShowType k
          ':<>: 'Text "' has different associated value:"
          ':$$: 'Text "\texpected: "
            ':<>: 'ShowType v
          ':$$: 'Text "\t but got: "
            ':<>: 'ShowType v'
          ':$$: 'Text "\tin sub(tree): "
            ':<>: 'ShowType tr'
      )

type family
  Equivalent'_ (p :: Bool) (l :: OrdMap k v) (r :: OrdMap k v) ::
    Equivalence k v
  where
  Equivalent'_ 'True _ _ = 'IsEquivalent
  Equivalent'_ 'False 'Leaf tr = 'MustBeEmpty tr
  Equivalent'_ 'False tr 'Leaf = 'MustBeEmpty tr
  Equivalent'_ 'False (Branch _ n _ l k v r) r' =
    EquivAux (n === Size r') n (Size r') r' (Split k r') l k v r

type Equivalent' l r = Equivalent'_ (l === r) l r

-- Equivalent' l' (Branch _ n _ l k v r) =
--   EquivAux (n == Size l') n (Size l') l' (Split k l') l k v r

(%==) :: (STestEquality k) => Sing (a :: k) -> Sing b -> SBool (a == b)
l %== b = case sTestEquality l b of
  Equal -> STrue
  NonEqual -> SFalse

sEquivalent ::
  (SOrd key, STestEquality key, STestEquality val) =>
  SOrdMap (l :: OrdMap key val) ->
  SOrdMap r ->
  SEquivalence (Equivalent' l r)
sEquivalent l0 r0 =
  case sTestEquality l0 r0 of
    Equal -> SIsEquivalent
    NonEqual ->
      case (l0, r0) of
        (SLeaf, r@SBranch {}) -> SMustBeEmpty r
        (r@SBranch {}, SLeaf) -> SMustBeEmpty r
        (SBranch _ n _ l k v r, r'@SBranch {}) ->
          let nr' = sSize r'
           in sEquivAux (n %=== nr') n nr' r' (sSplit k r') l k v r

type family ThenEqv eqv eqv' where
  ThenEqv 'IsEquivalent eqv' = eqv'
  ThenEqv err _ = err

infixr 1 `ThenEqv`, `sThenEqv`

sThenEqv :: SEquivalence eq -> SEquivalence eq' -> Sing (eq `ThenEqv` eq')
sThenEqv SIsEquivalent s = s
sThenEqv emp@SMustBeEmpty {} _ = emp
sThenEqv emp@SSizeMismatch {} _ = emp
sThenEqv emp@SValueMismatch {} _ = emp
sThenEqv emp@SKeyNotFound {} _ = emp

type family EquivAux p n m tr' trpl l k v r where
  EquivAux 'True _ _ tr' '(_, 'Nothing, _) _ k v _ =
    'KeyNotFound k v tr'
  EquivAux 'True _ _ tr '(l', 'Just '(_, v'), r') l k v r =
    ChkEqual (v == v') l' r' k v v'
      `ThenEqv` Equivalent' l' l
      `ThenEqv` Equivalent' r' r
  EquivAux 'False n m _ _ _ _ _ _ = 'SizeMismatch n m

sEquivAux ::
  (SOrd key, STestEquality key, STestEquality val) =>
  SBool p ->
  SNat n ->
  SNat m ->
  SOrdMap tr' ->
  STriple trpl ->
  SOrdMap l ->
  Sing (k :: key) ->
  Sing (v :: val) ->
  SOrdMap r ->
  Sing (EquivAux p n m tr' trpl l k v r)
sEquivAux STrue _ _ tr' (SMkTriple l' sroot r') l k v r =
  case sroot of
    SNothing -> SKeyNotFound k v tr'
    (SJust (SPair _ v')) ->
      sChkEqual (v %== v') l' r' k v v'
        `sThenEqv` sEquivalent l' l
        `sThenEqv` sEquivalent r' r
sEquivAux SFalse n m _ _ _ _ _ _ =
  SSizeMismatch n m

sChkEqual ::
  SBool b ->
  SOrdMap l ->
  SOrdMap r ->
  Sing k ->
  Sing v ->
  Sing v' ->
  SEquivalence (ChkEqual b l r k v v')
sChkEqual STrue _ _ _ _ _ = SIsEquivalent
sChkEqual SFalse l r k v v' = SValueMismatch k v v' (SMkTriple l v' r)

type family ChkEqual p l r k v v' where
  ChkEqual 'True _ _ _ _ _ = 'IsEquivalent
  ChkEqual 'False l r k v v' = 'ValueMismatch k v v' '(l, v', r)

type LookupWithIndex' k dic =
  FromJust
    ( 'Text "Key `"
        ':<>: 'ShowType k
        ':<>: 'Text " doesn't exist in "
        ':<>: 'ShowType (ToList dic)
    )
    (LookupWithIndex k dic)

type Lookup :: forall k v. k -> OrdMap k v -> Maybe v
type Lookup (k :: key) (dic :: OrdMap key val) =
  Fst1 <$> LookupWithIndex k dic

type IndexM (k :: key) (dic :: OrdMap key val) =
  Snd1 <$> LookupWithIndex k dic

type Index k dic = Snd (LookupWithIndex' k dic)

type LookupWithIndex :: forall k v. k -> OrdMap k v -> Maybe (v, Nat)
type family LookupWithIndex (k :: key) (dic :: OrdMap key val) where
  LookupWithIndex k Leaf = 'Nothing
  -- GHC の型レベル言語は正格なので、CaseOrdering を用いると、
  -- 不要な節まで計算され効率が落ちる可能性がある。
  -- そのため LookupCase を定義し、展開が行われないようにしている
  LookupWithIndex k (Branch _ _ _ l k' v r) =
    LookupCase
      0
      k
      (Compare k k')
      l
      v
      r

class (KnownNat (Index k dic)) => Member (k :: key) (dic :: OrdMap key val)

instance (KnownNat (Index k dic)) => Member k dic

instance
  (ShowSing k, ShowSing v) =>
  Show (SOrdMap (dic :: OrdMap k v))
  where
  showsPrec d smap =
    showParen (d > 10) $
      showString "FromAscList " . shows (sToList smap)

instance
  ( SOrd key
  , Known (k :: key)
  , Known (dic :: OrdMap key val)
  , ShowSing key
  , ShowSing val
  ) =>
  Deferrable (Member k dic)
  where
  deferEither _ f =
    case sLookupWithIndex (sKnownVal' @k) (sKnownVal' @dic) of
      SNothing ->
        Left $
          "Type-level OrdMap"
            ++ show (sKnownVal' @dic)
            ++ "doesn't have a field "
            ++ show (sKnownVal' @k)
      SJust (SPair _ (snat :: SNat n)) ->
        withKnown' snat $ toKnownNat @n $ Right f

-- GHC の型レベル言語は正格なので、CaseOrdering を用いると、
-- 不要な節まで計算され効率が落ちる可能性がある。
-- そのため LookupCase を定義し、展開が行われないようにしている
type family LookupCase offset key ord dic val dic' where
  LookupCase n _ 'EQ l val _ = 'Just '(val, n + Size l)
  LookupCase _ k 'LT 'Leaf _ _ = 'Nothing
  LookupCase n k 'LT ('Branch _ _ _ l k' v' r) _ _ =
    LookupCase n k (Compare k k') l v' r
  LookupCase n k 'GT _ _ 'Leaf = 'Nothing
  LookupCase n k 'GT l _ ('Branch _ _ _ l' k' v' r') =
    LookupCase (n + Size l + 1) k (Compare k k') l' v' r'

-- | @'FieldAt' i@ returns the @i@-th minimum number, or result in type error.
type FieldAt i dic =
  FromJust
    ( 'Text "Index out of bounds: (#"
        ':<>: 'ShowType i
        ':<>: 'Text ", "
        ':<>: 'ShowType (Size dic)
        ':<>: 'Text ") "
        ':<>: 'ShowType (ToList dic)
        ':<>: 'Text "."
    )
    (FieldAtM i dic)

type EntryAt k dic = Entry (FieldAt k dic)

type EntryAtM k dic = Entry' <$> FieldAtM k dic

type LabelAt k dic = Label (FieldAt k dic)

type LabelAtM k dic = Label' <$> FieldAtM k dic

type family FieldAtM (i :: Nat) (dic :: OrdMap k v) :: Maybe (Field k v) where
  FieldAtM i 'Leaf = 'Nothing
  FieldAtM i ('Branch _ n _ l k v r) =
    FieldAtAux i (Compare i n) (Compare i (Size l)) l k v r

type family FieldAtAux i iCmpN iCmpL l k v r where
  FieldAtAux i 'LT 'EQ _ k v _ = 'Just (k ::: v)
  FieldAtAux i 'LT 'LT ('Branch _ n' _ l' k' v' r') _ _ _ =
    FieldAtAux i (Compare i n') (Compare i (Size l')) l' k' v' r'
  FieldAtAux i 'LT 'GT l _ _ r =
    FieldAtM (i - Size l - 1) r
  FieldAtAux _ _ _ _ _ _ _ = 'Nothing

type ToList dic = ToListAux '[] dic

sToList :: SOrdMap dic -> SList (ToList dic)
sToList = sToListAux SNil

sToListAux :: SList acc -> SOrdMap dic -> SList (ToListAux acc dic)
sToListAux acc SLeaf = acc
sToListAux acc (SBranch _ _ _ l k v r) =
  sToListAux ((k :%:: v) :% sToListAux acc r) l

type family ToListAux acc (dic :: OrdMap key val) where
  ToListAux acc 'Leaf = acc
  ToListAux acc ('Branch _ _ _ l k v r) =
    ToListAux ((k ::: v) ': ToListAux acc r) l

type Insert k v dic =
  Merge dic (Singleton k v)

sInsert ::
  (SOrd key) =>
  Sing (k :: key) ->
  Sing v ->
  SOrdMap dic ->
  SOrdMap (Insert k v dic)
sInsert k v dic = sMerge dic (sSingleton k v)

sSingleton :: Sing k -> Sing v -> SOrdMap (Singleton k v)
sSingleton k v =
  SBranch sKnownVal' sKnownVal' sKnownVal' SLeaf k v SLeaf

type family Merge (l :: OrdMap k v) (r :: OrdMap k v) :: OrdMap k v where
  Merge 'Leaf dic = dic
  Merge dic 'Leaf = dic
  Merge ('Branch c n rk l' k' v' r') r =
    MergeAux (Split k' r) l' k' v' r'

sMerge ::
  (SOrd k) =>
  SOrdMap (l :: OrdMap k v) ->
  SOrdMap (r :: OrdMap k v) ->
  SOrdMap (Merge l r)
sMerge SLeaf dic = dic
sMerge dic SLeaf = dic
sMerge (SBranch _ _ _ l' k' v' r') r@SBranch {} =
  sMergeAux (sSplit k' r) l' k' v' r'

sMergeAux ::
  (SOrd key) =>
  STriple tpl ->
  SOrdMap l ->
  Sing (k :: key) ->
  Sing v ->
  SOrdMap r ->
  Sing (MergeAux tpl l k v r)
sMergeAux (SMkTriple lt SNothing gt) l k v r =
  sJoin (sMerge l lt) k v (sMerge r gt)
sMergeAux (SMkTriple lt (SJust (SPair k v)) gt) l _ _ r =
  sJoin (sMerge l lt) k v (sMerge r gt)

type family MergeAux tpl l k v r where
  MergeAux '(lt, 'Nothing, gt) l k v r =
    Join (Merge l lt) k v (Merge r gt)
  MergeAux '(lt, 'Just '(k, v), gt) l _ _ r =
    Join (Merge l lt) k v (Merge r gt)

type family
  Split (k :: key) (dic :: OrdMap key val) ::
    (OrdMap key val, Maybe (key, val), OrdMap key val)
  where
  Split k 'Leaf = '( 'Leaf, 'Nothing, 'Leaf)
  Split k ('Branch c n rk l k' v' r) =
    SplitAux k (Compare k k') c n rk l k' v' r

sSplit ::
  (SOrd key) =>
  Sing (k :: key) ->
  SOrdMap dic ->
  STriple (Split k dic)
sSplit _ SLeaf = SMkTriple SLeaf SNothing SLeaf
sSplit k (SBranch c n rk l k' v' r) =
  sSplitAux k (sCompare k k') c n rk l k' v' r

type family SplitAux k cmp c n rk l k' v' r where
  SplitAux k 'EQ c n rk l k' v' r = '(l, 'Just '(k', v'), r)
  SplitAux k 'LT c n rk l k' v' r =
    SplitAuxLT (Split k l) k' v' r
  SplitAux k 'GT c n rk l k' v' r =
    SplitAuxGT l k' v' (Split k r)

sSplitAux ::
  (SOrd key) =>
  Sing (k :: key) ->
  SOrdering cmp ->
  Sing c ->
  SNat n ->
  SRankT rk ->
  SOrdMap l ->
  Sing k' ->
  Sing v' ->
  SOrdMap r ->
  STriple (SplitAux k cmp c n rk l k' v' r)
sSplitAux _ SEQ _ _ _ l k v r = SMkTriple l (SJust $ SPair k v) r
sSplitAux k SLT _ _ _ l k' v' r = sSplitAuxLT (sSplit k l) k' v' r
sSplitAux k SGT _ _ _ l k' v' r = sSplitAuxGT l k' v' (sSplit k r)

type family SplitAuxLT trpl k v r where
  SplitAuxLT '(l2, mv, r2) k v r = '(l2, mv, Join r2 k v r)

sSplitAuxLT ::
  STriple trpl ->
  Sing k ->
  Sing v ->
  SOrdMap r ->
  STriple (SplitAuxLT trpl k v r)
sSplitAuxLT (SMkTriple l2 mv r2) k v r =
  SMkTriple l2 mv $ sJoin r2 k v r

type family SplitAuxGT l k v trpl where
  SplitAuxGT l k v '(l2, mv, r2) = '(Join l k v l2, mv, r2)

sSplitAuxGT ::
  SOrdMap l ->
  Sing k ->
  Sing v ->
  STriple trpl ->
  STriple (SplitAuxGT l k v trpl)
sSplitAuxGT l k v (SMkTriple l2 mv r2) =
  SMkTriple (sJoin l k v l2) mv r2

sRotateL :: SOrdMap dic -> SOrdMap (RotateL dic)
sRotateL
  ( SBranch
      SB
      h1
      rk1
      a
      k1
      v1
      ( SBranch
          SR
          _
          _
          b
          k2
          v2
          (SBranch SR h3 _ c k3 v3 d)
        )
    ) =
    SBranch
      SR
      h1
      rk1
      ( SBranch
          SB
          (sSize a %+ sSize b %+ sKnownVal')
          rk1
          a
          k1
          v1
          b
      )
      k2
      v2
      ( SBranch
          SB
          h3
          rk1
          c
          k3
          v3
          d
      )
sRotateL i = unsafeCoerce i

type family RotateL dic where
  RotateL
    ( Branch
        'B
        h1
        rk1
        a
        k1
        v1
        ( Branch
            'R
            h2
            rk2
            b
            k2
            v2
            (Branch 'R h3 rk3 c k3 v3 d)
        )
    ) =
    Branch
      'R
      h1
      rk1
      ( Branch
          'B
          (Size a + Size b + 1)
          rk1
          a
          k1
          v1
          b
      )
      k2
      v2
      ( Branch
          'B
          h3
          rk1
          c
          k3
          v3
          d
      )
  RotateL dic = dic

sRotateR :: SOrdMap dic -> SOrdMap (RotateR dic)
sRotateR
  ( SBranch
      SB
      h1
      rk1
      ( SBranch
          SR
          _
          _
          (SBranch SR h3 _ a k1 v1 b)
          k2
          v2
          c
        )
      k3
      v3
      d
    ) =
    SBranch
      SR
      h1
      rk1
      ( SBranch
          SB
          h3
          rk1
          a
          k1
          v1
          b
      )
      k2
      v2
      ( SBranch
          SB
          (sSize c %+ sSize d %+ sKnownVal')
          rk1
          c
          k3
          v3
          d
      )
sRotateR dic = unsafeCoerce dic

type family RotateR dic where
  RotateR
    ( Branch
        'B
        h1
        rk1
        ( Branch
            'R
            h2
            rk2
            (Branch 'R h3 rk3 a k1 v1 b)
            k2
            v2
            c
        )
        k3
        v3
        d
    ) =
    Branch
      'R
      h1
      rk1
      ( Branch
          'B
          h3
          rk1
          a
          k1
          v1
          b
      )
      k2
      v2
      ( Branch
          'B
          (Size c + Size d + 1)
          rk1
          c
          k3
          v3
          d
      )
  RotateR dic = dic

sJoin ::
  SOrdMap l ->
  Sing k ->
  Sing v ->
  SOrdMap r ->
  SOrdMap (Join l k v r)
sJoin l k v r =
  sBlacken $
    sJoinAux
      (sCompare (sRank l) (sRank r))
      l
      k
      v
      r

type family
  Join (l :: OrdMap key val) (k :: key) (v :: val) (r :: OrdMap key val) ::
    OrdMap key val
  where
  Join l k v r =
    Blacken
      ( JoinAux
          (Compare (Rank l) (Rank r))
          l
          k
          v
          r
      )

sJoinAux ::
  SOrdering a ->
  SOrdMap l ->
  Sing k ->
  Sing v ->
  SOrdMap r ->
  SOrdMap (JoinAux a l k v r)
sJoinAux SGT l k v r = sJoinAuxLeft (sRank r) l k v r
sJoinAux SLT l k v r = sJoinAuxRight (sRank l) l k v r
sJoinAux SEQ l k v r =
  SBranch
    SR
    (sSize l %+ sSize r %+ sKnownVal')
    (sRank l)
    l
    k
    v
    r

sRank :: SOrdMap dic -> SRankT (Rank dic)
sRank SLeaf = sKnownVal'
sRank (SBranch _ _ r _ _ _ _) = r

type family JoinAux a l k v r where
  JoinAux 'GT l k v r =
    JoinAuxLeft (Rank r) l k v r
  JoinAux 'LT l k v r =
    JoinAuxRight (Rank l) l k v r
  JoinAux EQ l k v r =
    Branch 'R (Size l + Size r + 1) (Rank l) l k v r

sJoinAuxLeft ::
  SRankT targRk ->
  SOrdMap l ->
  Sing k ->
  Sing v ->
  SOrdMap r ->
  SOrdMap (JoinAuxLeft targRk l k v r)
sJoinAuxLeft
  targRk
  (SBranch SB n rk' l' k' v' r')
  k
  v
  r =
    case sTestEquality targRk rk' of
      Equal ->
        SBranch
          SR
          (sSize r %+ n %+ sKnownVal')
          targRk
          (SBranch SB n targRk l' k' v' r')
          k
          v
          r
      NonEqual ->
        unsafeCoerce $ -- trust me
          sRotateL
            ( SBranch
                SB
                (n %+ sSize r %+ sKnownVal' @1)
                rk'
                l'
                k'
                v'
                (sJoinAuxLeft targRk r' k v r)
            )
sJoinAuxLeft
  targRk
  (SBranch SR n rk' l' k' v' r')
  k
  v
  r =
    SBranch
      SR
      (n %+ sSize r %+ sKnownVal')
      rk'
      l'
      k'
      v'
      (sJoinAuxLeft targRk r' k v r)
sJoinAuxLeft (SMkRankT rk) SLeaf k v r =
  case sTestEquality rk $ sKnownVal' @1 of
    Equal ->
      SBranch
        SR
        (sSize r %+ sKnownVal')
        (SMkRankT sKnownVal')
        SLeaf
        k
        v
        r
    NonEqual -> error "sJoinAuxLeft: Impossible clause!"

type family JoinAuxLeft targRk l k v r where
  JoinAuxLeft
    targRk
    (Branch 'B n targRk l' k' v' r')
    k
    v
    r =
    Branch
      'R
      (Size r + n + 1)
      targRk
      (Branch 'B n targRk l' k' v' r')
      k
      v
      r
  JoinAuxLeft
    targRk
    (Branch 'B n rk' l' k' v' r')
    k
    v
    r =
    RotateL
      ( Branch
          'B
          (n + Size r + 1)
          rk'
          l'
          k'
          v'
          (JoinAuxLeft targRk r' k v r)
      )
  JoinAuxLeft
    targRk
    (Branch 'R n rk' l' k' v' r')
    k
    v
    r =
    ( Branch
        'R
        (n + Size r + 1)
        rk'
        l'
        k'
        v'
        (JoinAuxLeft targRk r' k v r)
    )
  JoinAuxLeft (MkRankT 1) 'Leaf k v r =
    Branch
      'R
      (Size r + 1)
      (MkRankT 1)
      'Leaf
      k
      v
      r

type family JoinAuxRight targRk l k v r where
  JoinAuxRight
    targRk
    l
    k
    v
    (Branch 'B n targRk l' k' v' r') =
    Branch
      'R
      (Size l + n + 1)
      targRk
      l
      k
      v
      (Branch 'B n targRk l' k' v' r')
  JoinAuxRight
    targRk
    l
    k
    v
    (Branch 'B n rk' l' k' v' r') =
    RotateR
      ( Branch
          'B
          (n + Size l + 1)
          rk'
          (JoinAuxRight targRk l k v l')
          k'
          v'
          r'
      )
  JoinAuxRight
    targRk
    l
    k
    v
    (Branch 'R n rk' l' k' v' r') =
    ( Branch
        'R
        (n + Size l + 1)
        rk'
        (JoinAuxRight targRk l k v l')
        k'
        v'
        r'
    )
  JoinAuxRight (MkRankT 1) l k v 'Leaf =
    Branch
      'R
      (Size l + 1)
      (MkRankT 1)
      l
      k
      v
      'Leaf

sJoinAuxRight ::
  SRankT targRk ->
  SOrdMap l ->
  Sing (k :: key) ->
  Sing v ->
  SOrdMap r ->
  SOrdMap (JoinAuxRight targRk l k v r)
sJoinAuxRight targRk l k v (SBranch SB n rk' l' k' v' r') =
  case sTestEquality targRk rk' of
    Equal ->
      SBranch
        SR
        (sSize l %+ n %+ sKnownVal')
        targRk
        l
        k
        v
        (SBranch SB n targRk l' k' v' r')
    NonEqual ->
      unsafeCoerce $
        sRotateR $
          SBranch
            SB
            (n %+ sSize l %+ sKnownVal' @1)
            rk'
            (sJoinAuxRight targRk l k v l')
            k'
            v'
            r'
sJoinAuxRight targRk l k v (SBranch SR n rk' l' k' v' r') =
  SBranch
    SR
    (n %+ sSize l %+ sKnownVal')
    rk'
    (sJoinAuxRight targRk l k v l')
    k'
    v'
    r'
sJoinAuxRight (SMkRankT sn) l k v SLeaf =
  case sTestEquality sn (sKnownVal' @1) of
    Equal ->
      SBranch
        SR
        (sSize l %+ sKnownVal')
        sKnownVal'
        l
        k
        v
        SLeaf
    NonEqual -> error "sJoinAuxRight: IMPOSSIBLE!"

type family Intersect l r where
  Intersect 'Leaf _ = 'Leaf
  Intersect _ 'Leaf = 'Leaf
  Intersect (Branch _ _ _ l k v r) r' =
    IntersectAux (Split k r') l r

type family IntersectAux trpl l r where
  IntersectAux '(lt, 'Just '(k, v), gt) l r =
    Join (Intersect l lt) k v (Intersect r gt)
  IntersectAux '(lt, 'Nothing, gt) l r =
    Merge (Intersect l lt) (Intersect r gt)

type Delete k dic = DeleteAux (Split k dic) dic

type family DeleteAux tpl dic where
  DeleteAux '(_, 'Nothing, _) dic = dic
  DeleteAux '(l, _, r) _ = Merge l r

type family Blacken dic where
  Blacken ('Branch 'R n rk l k v r) = 'Branch 'B n (SuccRank rk) l k v r
  Blacken t = t

sSuccRank :: SRankT r -> SRankT (SuccRank r)
sSuccRank (SMkRankT r) = SMkRankT (r %+ sKnownVal')

sBlacken :: SOrdMap dic -> SOrdMap (Blacken dic)
sBlacken (SBranch SR n rk l k v r) =
  SBranch SB n (sSuccRank rk) l k v r
sBlacken (SBranch SB n rk l k v r) =
  SBranch SB n rk l k v r
sBlacken SLeaf = SLeaf

type family SuccRank rk where
  SuccRank ('MkRankT rk) = MkRankT (rk + 1)

sFromList :: (SOrd key) => SList (dic :: [Field key val]) -> SOrdMap (FromList dic)
sFromList SNil = sEmpty
sFromList ((k :%:: v) :% SNil) = sSingleton k v
sFromList ((k :%:: v) :% kvs@(:%) {}) =
  sInsert k v $ sFromList kvs

type family FromList xs where
  FromList '[] = 'Leaf
  FromList '[k ::: v] = Singleton k v
  FromList ((k ::: v) ': kvs) =
    Insert k v (FromList kvs)

type family MapApplyWithKey (f :: k ~> v ~> v') dic where
  MapApplyWithKey _ Leaf = Leaf
  MapApplyWithKey f (Branch c n rk l k v r) =
    Branch
      c
      n
      rk
      (MapApplyWithKey f l)
      k
      (Apply (Apply f k) v)
      (MapApplyWithKey f r)

type family MapWithKey (f :: k -> v -> v') dic where
  MapWithKey _ Leaf = Leaf
  MapWithKey f (Branch c n rk l k v r) =
    Branch
      c
      n
      rk
      (MapWithKey f l)
      k
      (f k v)
      (MapWithKey f r)

type family MapWithIndex (f :: Nat -> v -> v') dic where
  MapWithIndex _ Leaf = Leaf
  MapWithIndex f (Branch c n rk l k v r) =
    Branch c n rk (MapWithIndex f l) k (f (Size l) v) (MapWithIndex f r)

type family MapApplyWithIndex (f :: Nat ~> v ~> v') dic where
  MapApplyWithIndex _ Leaf = Leaf
  MapApplyWithIndex f (Branch c n rk l k v r) =
    Branch
      c
      n
      rk
      (MapApplyWithIndex f l)
      k
      (Apply (Apply f (Size l)) v)
      (MapApplyWithIndex f r)

type family
  MapKeysMonotonic
    (f :: k -> k')
    (dic :: OrdMap k v) ::
    OrdMap k' v
  where
  MapKeysMonotonic _ Leaf = Leaf
  MapKeysMonotonic f (Branch c n rk l k v r) =
    Branch c n rk (MapKeysMonotonic f l) (f k) v (MapKeysMonotonic f r)

type family
  MapApplyKeysMonotonic
    (f :: k ~> k')
    (dic :: OrdMap k v) ::
    OrdMap k' v
  where
  MapApplyKeysMonotonic _ Leaf = Leaf
  MapApplyKeysMonotonic f (Branch c n rk l k v r) =
    Branch
      c
      n
      rk
      (MapApplyKeysMonotonic f l)
      (Apply f k)
      v
      (MapApplyKeysMonotonic f r)

sSwapField ::
  SList xs -> SList (MapApply (Uncurry (:::) .: Swap1) xs)
sSwapField SNil = SNil
sSwapField (SPair x y :% xs) =
  (y :%:: x) :% sSwapField xs

sSortPermutation ::
  (SOrd key) =>
  SList (dic :: [Field key val]) ->
  SList (SortPermutation dic)
sSortPermutation =
  sEntries . sFromList . sSwapField . sIndexed . sLabels'

type SortPermutation (xs :: [Field k v]) =
  Entries
    ( FromList
        ( MapApply
            (Uncurry (:::) .: Swap1)
            (Indexed (MapApply Label' xs))
        )
    )

type SortableLabels xs =
  Known (SortPermutation xs)

type SortableList xs =
  Known (SortPermutation (ConstFields '() xs))

sortPermutation ::
  forall ps.
  (SortableLabels ps) =>
  U.Vector Int
sortPermutation =
  U.fromList $
    map fromIntegral $
      knownVal' @(SortPermutation ps)

unsortMembership ::
  forall l v ps r.
  ( SortableLabels ps
  , LookupWithIndex l (FromList ps)
      ~ 'Just '(v, Index l (FromList ps))
  , Member l (FromList ps)
  ) =>
  ( (List.Member (l ::: v) ps) =>
    r
  ) ->
  r
unsortMembership f =
  let pos = fromIntegral $ natVal @(Index l (FromList ps)) Proxy
   in unsafeWithKnownMember
        @(l ::: v)
        @ps
        (fromIntegral $ perm U.! pos)
        f
  where
    perm = sortPermutation @ps

withUnsortedMember ::
  forall ps r.
  (SortableLabels ps) =>
  (forall l. (Member l (FromList ps)) => Proxy l -> r) ->
  ( forall fld.
    (List.Member fld ps) =>
    Proxy fld ->
    r
  )
withUnsortedMember f = \(_ :: Proxy l) ->
  let pos = fromIntegral $ position @l @ps
   in unsafeWithOrdMapMember
        @(Label l)
        @(FromList ps)
        (fromIntegral $ fromJust $ U.elemIndex pos perm)
        $ f (Proxy @(Label l))
  where
    perm = sortPermutation @ps

withUnsortedMember' ::
  forall l ps r.
  (SortableLabels ps, List.Member l ps) =>
  ((Member (Label l) (FromList ps)) => r) ->
  r
withUnsortedMember' =
  let pos = fromIntegral $ natVal @(List.Index l ps) Proxy
   in unsafeWithOrdMapMember
        @(Label l)
        @(FromList ps)
        (fromIntegral $ fromJust $ U.elemIndex pos perm)
  where
    perm = sortPermutation @ps

withLabelIndex ::
  forall ps f.
  (forall l. (List.Member l (Labels (FromList ps))) => Proxy l -> f l) ->
  ( forall l.
    (Member l (FromList ps)) =>
    Proxy l ->
    f l
  )
withLabelIndex f = \(_ :: Proxy l) ->
  let pos = fromIntegral $ List.natVal @(Index l (FromList ps)) Proxy
   in unsafeWithKnownMember
        @l
        @(Labels (FromList ps))
        pos
        $ f (Proxy @l)

data ReadTree = Nought | Single | Br ReadTree ReadTree
  deriving (Typeable, Generic)

type family BuildReadTree n :: ReadTree where
  BuildReadTree 0 = 'Nought
  BuildReadTree 1 = 'Single
  BuildReadTree n = BuildReadTreeAux n ((n - 1) `Div` 2)

type family BuildReadTreeAux n q where
  BuildReadTreeAux n q =
    'Br (BuildReadTree (n - 1 - q)) (BuildReadTree q)

type family
  ReadMap d m (tr :: ReadTree) (xs :: [Field k v]) ::
    (OrdMap k v, [Field k v])
  where
  ReadMap _ _ 'Nought xs = '( 'Leaf, xs)
  ReadMap d d 'Single ((k ::: v) ': xs) =
    '( 'Branch 'R 1 (MkRankT 1) 'Leaf k v 'Leaf, xs)
  ReadMap _ _ 'Single ((k ::: v) ': xs) =
    '( 'Branch 'B 1 (MkRankT 2) 'Leaf k v 'Leaf, xs)
  ReadMap d k ('Br l r) xs = BrAuxL d k (ReadMap d (k + 1) l xs) r

type family BrAuxL d k tpl r where
  BrAuxL d m '(l, (k ::: v) ': xs) r =
    BrAuxR d m l k v (ReadMap d (m + 1) r xs)

type family BrAuxR d m l k v tpl where
  BrAuxR d d l k v '(r, xs) =
    '( 'Branch 'R (Size l + Size r + 1) (Rank l) l k v r, xs)
  BrAuxR d m l k v '(r, xs) =
    '( 'Branch 'B (Size l + Size r + 1) (SuccRank (Rank l)) l k v r, xs)

{- | 長さやソート済か検査せずにソート済と仮定して木を作る

  /c.f./ 'FromList', 'UnsafeFromAscList', 'FromAscList'.
-}
type UnsafeFromAscListOfSize n xs =
  Fst (ReadMap (Log2 (n + 1)) 0 (BuildReadTree n) xs)

{- | ソート済でラベルの重複を持たないリストから 'OrdMap' を作る。
   重複を持たないか・ソート済みかは検査しない。
   インタフェースが頻繁に変わりうる場合は 'FromAscList' を使うとよい。

  /c.f./ 'FromList', 'UnsafeFromAscListOFSize', 'FromAscList'.
-}
type UnsafeFromAscList xs = UnsafeFromAscListOfSize (Length xs) xs

{- | ソート済のリストから 'OrdMap' を作る。ソート済でない場合はエラーとする。
   ソート済だと確信が持て、そのラベルの集合の並び順を書き換える頻度が少ないと思われる場合、
   'UnsafeFromAscList' を使うと定数倍コンパイルが速くなる。

  /c.f./ 'FromList', 'UnsafeFromAscList', 'FromAscList'.
-}
type FromAscList xs = FromAscListAux (LabelSorted xs) xs

type family FromAscListAux sorted xs where
  FromAscListAux 'IsSorted xs = UnsafeFromAscList xs
  FromAscListAux ('UnsortedOn orig n l r) _ =
    TypeError
      ( 'Text "Unsorted fields given to FromAscList: the "
          ':<>: 'ShowType n
          ':<>: 'Text "th field: "
          ':$$: 'Text "\t"
            ':<>: 'ShowType l
          ':$$: 'Text "is strictly larger than successing field: "
          ':$$: 'Text "\t"
            ':<>: 'ShowType r
          ':$$: 'Text "in a given list of fields:"
          ':$$: 'Text "\t"
            ':<>: 'ShowType orig
      )
  FromAscListAux ('DuplicatedLabel orig n l v v') _ =
    TypeError
      ( 'Text "A field `"
          ':<>: 'ShowType l
          ':<>: 'Text "' is duplicated in the given list at index "
          ':<>: 'ShowType n
          ':<>: 'Text "."
          ':$$: 'Text "Associated with:"
          ':$$: 'ShowType n
            ':<>: 'Text ":\t"
            ':<>: 'ShowType v
          ':$$: 'ShowType (n + 1)
            ':<>: 'Text ":\t"
            ':<>: 'ShowType v'
          ':$$: 'Text "In the given list of fields:"
          ':$$: 'Text "\t"
            ':<>: 'ShowType orig
      )

type instance List.PElement (OrdMap k v) = Field k v

instance List.PIsList (OrdMap k v) where
  type FromList xs = FromList xs
  type Cons kvs xs = Insert (Label kvs) (Entry kvs) xs
  type Empty = Empty

memberToList ::
  forall fld recs.
  Index (Label fld) recs
    :~: List.Index fld (ToList recs)
memberToList = unsafeCoerce $ Refl @()

indexFieldAt ::
  ((k + 1) <= Size recs) =>
  Index (LabelAt k recs) recs :~: k
indexFieldAt = unsafeCoerce $ Refl @()

withOrdMapMember ::
  forall l recs r.
  (Member l recs) =>
  ((List.Member (l ::: Lookup' l recs) (ToList recs)) => r) ->
  r
withOrdMapMember =
  unsafeWithKnownMember
    @(l ::: Lookup' l recs)
    @(ToList recs)
    (List.natVal $ Proxy @(Index l recs))

elimMemberToList ::
  (List.Member l (ToList recs)) =>
  Lookup' (Label l) recs :~: Entry l
elimMemberToList = unsafeCoerce $ Refl @()

withToListMember ::
  forall l recs p.
  (List.Member l (ToList recs)) =>
  ( ( LookupWithIndex (Label l) recs
        ~ 'Just '(Entry l, List.Index l (ToList recs))
    ) =>
    p
  ) ->
  p
withToListMember act =
  gcastWith
    ( unsafeCoerce $ Refl @() ::
        LookupWithIndex (Label l) recs
          :~: 'Just '(Entry l, List.Index l (ToList recs))
    )
    act

fieldAtToList ::
  forall k recs.
  FieldAt k recs
    :~: List.ElemAt k (ToList recs)
fieldAtToList = unsafeCoerce $ Refl @()

elemAtFieldDistrib ::
  ElemAt k (ToList dic) :~: (LabelAt k dic ::: EntryAt k dic)
elemAtFieldDistrib = unsafeCoerce $ Refl @()

data Succ :: Nat ~> Nat

type instance Apply Succ n = n + 1

type BlackCounts dic =
  MapApply
    (Length1 .: Matches1 B .: MapApply1 Fst1)
    (Paths dic)

type BlackCountInvariant dic = ChkAllEq (BlackCounts dic)

type family RedRedInvariant dic :: Constraint where
  RedRedInvariant 'Leaf = ()
  RedRedInvariant ('Branch 'R _ _ (Branch 'R _ _ _ _ _ _) _ _ _) =
    TypeError ('Text "No Red-Red invariant failed")
  RedRedInvariant ('Branch 'R _ _ _ _ _ (Branch 'R _ _ _ _ _ _)) =
    TypeError ('Text "No Red-Red invariant failed")
  RedRedInvariant ('Branch _ _ _ l _ _ r) =
    (RedRedInvariant l, RedRedInvariant r)

type ValidRBTree dic =
  (RedRedInvariant dic, BlackCountInvariant dic, RootIsBlack dic, LabelSorted (ToList dic) ~ 'IsSorted)

type Paths dic = PathsAux dic

type family PathsAux (dic :: OrdMap k v) :: [[(Color, Maybe (k, v))]] where
  PathsAux 'Leaf = '[ '[ '( 'B, Nothing)]]
  PathsAux ('Branch c _ _ l k v r) =
    MapApply (Cons1 '(c, 'Just '(k, v))) (Paths l ++ Paths r)

data Cons1 (x :: k) :: [k] ~> [k]

type instance Apply (Cons1 x) xs = x ': xs

type family RootIsBlack a :: Constraint where
  RootIsBlack 'Leaf = ()
  RootIsBlack (Branch 'B _ _ _ _ _ _) = ()
  RootIsBlack (Branch 'R _ _ _ _ _ _) =
    TypeError ('Text "Root is not black!")

type family ChkAllEq a :: Constraint where
  ChkAllEq '[] = ()
  ChkAllEq '[x] = ()
  ChkAllEq (x ': x ': xs) = ChkAllEq (x ': xs)
  ChkAllEq (x ': y ': xs) =
    TypeError
      ('Text "Nonequal elements: " ':<>: 'ShowType '(x, y))

type ConstField e l = l ::: e

data ConstField1 (e :: v) :: k ~> Field k v

type instance Apply (ConstField1 v) k = ConstField v k

type ConstFields v fs = MapApply (ConstField1 v) fs

data ConstFields1 (e :: v) :: [k] ~> [Field k v]

type instance Apply (ConstFields1 v) ks = ConstFields v ks

unsafeWithOrdMapMember ::
  forall l xs r.
  Word ->
  ((Member l xs) => r) ->
  r
unsafeWithOrdMapMember pos act =
  let nat = fromIntegral pos :: Natural
   in unsafeCoerce (WithOMMem @l @xs @r act) nat

newtype WithOMMem l xs r
  = WithOMMem ((Member l xs) => r)

elimConstField ::
  forall l a xs.
  (Member l (FromList (ConstFields a xs))) =>
  Lookup' l (FromList (ConstFields a xs)) :~: a
elimConstField = unsafeCoerce $ Refl @()

withLabelsMember ::
  forall l qs r.
  (Member l qs) =>
  ((List.Member l (Labels qs)) => r) ->
  r
withLabelsMember =
  unsafeWithKnownMember
    @l
    @(Labels qs)
    (List.natVal $ Proxy @(Index l qs))

data Sortedness l v
  = IsSorted
  | UnsortedOn [Field l v] Nat (Field l v) (Field l v)
  | DuplicatedLabel [Field l v] Nat l v v

type LabelSorted dic = LabelSorted' 0 dic dic

type family
  LabelSorted'
    n
    (orig :: [Field l v])
    (flds :: [Field l v]) ::
    Sortedness l v
  where
  LabelSorted' _ _ '[] = 'IsSorted
  LabelSorted' _ _ '[x] = 'IsSorted
  LabelSorted' n orig ((a ::: av) ': (b ::: bv) ': as) =
    CaseOrdering
      (Compare a b)
      (LabelSorted' (n + 1) orig ((b ::: bv) ': as))
      ('DuplicatedLabel orig n a av bv)
      ('UnsortedOn orig n (a ::: av) (b ::: bv))

sLookupWithIndex ::
  (SOrd k) => Sing (lab :: k) -> SOrdMap dic -> SMaybe (LookupWithIndex lab dic)
sLookupWithIndex _ SLeaf = SNothing
sLookupWithIndex k (SBranch _ _ _ l k' v r) =
  sLookupCase (sKnownVal' :: SNat 0) k (sCompare k k') l v r

-- | A variant of 'sLookupWithIndex' with all the kinds explicitly qunatified.
sLookupWithIndex' ::
  forall k v (lab :: k) (dic :: OrdMap k v).
  (SOrd k) =>
  Sing (lab :: k) ->
  Sing dic ->
  Sing (LookupWithIndex lab dic)
sLookupWithIndex' = sLookupWithIndex

sSize :: SOrdMap dic -> SNat (Size dic)
sSize SLeaf = sKnownVal' @0
sSize (SBranch _ n _ _ _ _ _) = n

sLookupCase ::
  (SOrd k) =>
  SNat offset ->
  Sing (key :: k) ->
  SOrdering ord ->
  SOrdMap dic ->
  Sing val ->
  SOrdMap dic' ->
  Sing (LookupCase offset key ord dic val dic')
sLookupCase n _ SEQ l val _ =
  SJust $
    val `SPair` (n %+ sSize l)
sLookupCase _ _ SLT SLeaf _ _ = SNothing
sLookupCase n k SLT (SBranch _ _ _ l k' v' r) _ _ =
  sLookupCase n k (sCompare k k') l v' r
sLookupCase _ _ SGT _ _ SLeaf = SNothing
sLookupCase n k SGT l _ (SBranch _ _ _ l' k' v' r') =
  sLookupCase
    (n %+ sSize l %+ sKnownVal' @1)
    k
    (sCompare k k')
    l'
    v'
    r'

sLabel :: SField f -> Sing (Label f)
sLabel (l :%:: _) = l

sEntry :: SField f -> Sing (Entry f)
sEntry (_ :%:: v) = v

sLabels ::
  SOrdMap dic -> SList (Labels dic)
sLabels = sLabels' . sToList

sLabels' :: SList fs -> SList (MapApply Label' fs)
sLabels' = go
  where
    go :: SList (flds :: [Field l k]) -> SList (MapApply Label' flds)
    go SNil = SNil
    go (x :% xs) = sLabel x :% go xs

sEntries ::
  SOrdMap dic -> SList (Entries dic)
sEntries = go . sToList
  where
    go :: SList (flds :: [Field l k]) -> SList (MapApply Entry' flds)
    go SNil = SNil
    go (x :% xs) = sEntry x :% go xs

type ConstList fs = ConstFields '() fs

type ConstMap fs = FromList (ConstList fs)

toConstListMembership ::
  forall l ps.
  (List.Member l ps) =>
  Membership (l ::: '()) (ConstList ps)
toConstListMembership =
  unsafeCoerce $ membership @l @ps

fromConstListMembership ::
  forall l ps.
  (List.Member (l ::: '()) (ConstList ps)) =>
  Membership l ps
fromConstListMembership =
  unsafeCoerce $ membership @(l ::: '()) @(ConstList ps)

sConstList ::
  SList xs -> SList (ConstFields '() xs)
sConstList SNil = SNil
sConstList (x :% xs) = (x :%:: sKnownVal') :% sConstList xs

sConstMap :: (SOrd k) => SList (xs :: [k]) -> SOrdMap (ConstMap xs)
sConstMap = sFromList . sConstList

data Disjointness k = IsDisjoint | OverlappingKey k

deriveAllKnown True ''Disjointness

_ovl :: (KnownDisjointness d) => pxy d -> SDisjointness d
_ovl = sDisjointnessVal

_f :: (HasSing k, Known d) => pxy (d :: Disjointness k) -> Disjointness (Demote k)
_f = disjointnessVal

_fg :: (HasSing k) => Disjointness (Demote k) -> SomeSing (Disjointness k)
_fg = toSomeDisjointness

type family Disjoint' (ls :: OrdMap k v) (rs :: OrdMap k v) :: Disjointness k where
  Disjoint' 'Leaf _ = IsDisjoint
  Disjoint' _ 'Leaf = IsDisjoint
  Disjoint' l' (Branch _ _ _ l k _ r) =
    DisjointAux (Split k l') l k r

type family DisjointAux trpl l k r where
  DisjointAux '(l', 'Nothing, r') l k r =
    Disjoint' l' l `ChoiceDisj` Disjoint' r' r
  DisjointAux '(l', 'Just _, _) _ k _ = OverlappingKey k

type Disjoint ls rs = Disjoint' ls rs ~ IsDisjoint

type family ChoiceDisj f g where
  ChoiceDisj IsDisjoint r = r
  ChoiceDisj (OverlappingKey k) _ = OverlappingKey k

sDisjoint ::
  (SOrd k) =>
  SOrdMap (l :: OrdMap k v) ->
  SOrdMap r ->
  SDisjointness (Disjoint' l r)
sDisjoint SLeaf _ = SIsDisjoint
sDisjoint _ SLeaf = SIsDisjoint
sDisjoint l'@SBranch {} (SBranch _ _ _ l k _ r) =
  case sSplit k l' of
    SMkTriple l'' SNothing r'' ->
      sDisjoint l'' l `sChoiceDisj` sDisjoint r'' r
    SMkTriple _ SJust {} _ ->
      SOverlappingKey k

sChoiceDisj :: SDisjointness s -> SDisjointness r -> SDisjointness (ChoiceDisj s r)
sChoiceDisj SIsDisjoint r = r
sChoiceDisj s@SOverlappingKey {} _ = s

type family EnumFromLess f n m acc where
  EnumFromLess f n n acc = acc
  EnumFromLess f n m acc = f n ': EnumFromLess f (n + 1) m acc

sEnumFromLess ::
  forall lr n m xs.
  (forall a. Sing a -> SEither (lr a)) ->
  SNat n ->
  SNat m ->
  SList xs ->
  SList (EnumFromLess lr n m xs)
sEnumFromLess eithCons n m xs = go n
  where
    go :: SNat k -> SList (EnumFromLess lr k m xs)
    go k =
      case sTestEquality k m of
        Equal -> xs
        NonEqual -> unsafeCoerce $ eithCons k :% go (k %+ sKnownVal' @1)

sMergePerm ::
  (SOrd k) =>
  SOrdMap (l :: OrdMap k v) ->
  SOrdMap (r :: OrdMap k v) ->
  SList (MergePerm l r)
sMergePerm = sMergePerm' (sKnownVal' @0) (sKnownVal' @0) SNil

type MergePerm l r = MergePerm' 0 0 '[] l r

type family
  MergePerm'
    (n :: Nat)
    (m :: Nat)
    (cont :: [Either Nat Nat])
    (l :: OrdMap k v)
    (r :: OrdMap k v) ::
    [Either Nat Nat]
  where
  MergePerm' _ _ acc 'Leaf 'Leaf = acc
  MergePerm' _ m acc 'Leaf r = EnumFromLess Right m (m + Size r) acc
  MergePerm' n _ acc l 'Leaf = EnumFromLess Left n (n + Size l) acc
  MergePerm' n m acc (Branch _ _ _ l k _ r) r' =
    MergePermAux n m acc (Split k r') l k r

sMergePerm' ::
  (SOrd key) =>
  SNat n ->
  SNat m ->
  SList count ->
  SOrdMap (l :: OrdMap key val) ->
  SOrdMap r ->
  SList (MergePerm' n m count l r)
sMergePerm' _ _ acc SLeaf SLeaf = acc
sMergePerm' _ m acc SLeaf r@SBranch {} =
  sEnumFromLess SRight m (m %+ sSize r) acc
sMergePerm' n _ acc l@SBranch {} SLeaf =
  sEnumFromLess SLeft n (n %+ sSize l) acc
sMergePerm' n m acc (SBranch _ _ _ l k _ r) r'@SBranch {} =
  sMergePermAux n m acc (sSplit k r') l k r

sMergePermAux ::
  (SOrd key) =>
  SNat n ->
  SNat m ->
  SList acc ->
  STriple view ->
  SOrdMap (l :: OrdMap key val) ->
  Sing k ->
  SOrdMap (r :: OrdMap key val) ->
  SList (MergePermAux n m acc view l k r)
sMergePermAux n m acc (SMkTriple l' SNothing r') l _ r =
  sMergePerm'
    n
    m
    ( SLeft (n %+ sSize l)
        :% sMergePerm'
          ((n %+ sKnownVal' @1) %+ sSize l)
          (m %+ sSize l')
          acc
          r
          r'
    )
    l
    l'
sMergePermAux n m acc (SMkTriple l' SJust {} r') l _ r =
  sMergePerm'
    n
    m
    ( SRight (m %+ sSize l')
        :% sMergePerm'
          (n %+ sKnownVal' @1 %+ sSize l)
          (m %+ sKnownVal' @1 %+ sSize l')
          acc
          r
          r'
    )
    l
    l'

type family MergePermAux n m acc view l k r where
  MergePermAux n m acc '(l', 'Nothing, r') l k r =
    MergePerm'
      n
      m
      ('Left (n + Size l) ': MergePerm' ((n + 1) + Size l) (m + Size l') acc r r')
      l
      l'
  MergePermAux n m acc '(l', 'Just _, r') l k r =
    MergePerm'
      n
      m
      ('Right (m + Size l') ': MergePerm' (n + 1 + Size l) (m + 1 + Size l') acc r r')
      l
      l'

type family
  AllOM' (c :: k -> v -> Constraint) (dic :: OrdMap k v) ::
    Constraint
  where
  AllOM' c 'Leaf = ()
  AllOM' c ('Branch _ _ _ l k v r) =
    (AllOM c l, c k v, AllOM c r)

data SomeOMMember dic where
  MkSomeOMMember :: OMMembership k dic -> SomeOMMember dic

class
  (KnownNat (Size dic), Known dic, AllOM' c dic) =>
  AllOM c dic
  where
  allOMDict ::
    OMMembership k dic ->
    Dict (c k (Lookup' k dic))

instance AllOM c Leaf where
  allOMDict = error "allOMDict: Membership for empty OrdMap!"

instance
  ( AllOM c l
  , KnownNat (Size l)
  , KnownNat n
  , AllOM c r
  , c k v
  , Known l
  , Known r
  , Known k
  , Known rk
  , Known v
  , Known col
  ) =>
  (AllOM c (Branch col n rk l k v r))
  where
  allOMDict (OMMembership i :: OMMembership k' _) =
    let lSize = natVal @(Size l) Proxy
     in case compare i lSize of
          LT -> unsafeCoerce $ allOMDict @c @l (OMMembership i :: OMMembership k' l)
          EQ -> unsafeCoerce (Dict @(c k v))
          GT ->
            unsafeCoerce $
              allOMDict @c @r
                (OMMembership (i - lSize - 1) :: OMMembership k' r)

class (Deferrable (c x y)) => DeferrableFor2 c x y

instance (Deferrable (c x y)) => DeferrableFor2 c x y

instance
  (Known dic, AllOM (DeferrableFor2 c) dic) =>
  Deferrable (AllOM c dic)
  where
  deferEither _ = \f ->
    go (sKnownVal' @dic)
      <&> \Dict -> f
    where
      go ::
        (AllOM (DeferrableFor2 c) ys) =>
        SOrdMap ys ->
        Either String (Dict (AllOM c ys))
      go SLeaf = Right Dict
      go (SBranch c s rk l (k :: Sing k) (v :: Sing v) r) =
        withKnown' c $
          withKnownNat' s $
            withKnown' rk $
              withKnown' k $
                withKnown' v $
                  do
                    Dict <- deferEither_ @(c k v) @(Dict (c k v)) $ Dict @(c k v)
                    Dict <- go l
                    Dict <- go r
                    pure Dict

foldMapOrdMapC ::
  forall c dic w.
  (Monoid w, AllOM c dic) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    , c k v
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    w
  ) ->
  w
foldMapOrdMapC f = go 0 $ sKnownVal' @dic
  where
    go :: forall xs. (AllOM c xs) => Natural -> SOrdMap xs -> w
    go _ SLeaf = mempty
    go !off (SBranch _ _ _ l (k :: Sing k) (v :: Sing v) r) =
      withKnown' k $
        withKnown' v $
          let lSize = demote (sSize l) + off
           in case promote @Nat lSize of
                MkSomeSing (sn :: SNat n) ->
                  withKnownNat' sn
                    $ gcastWith
                      ( unsafeCoerce (Refl @()) ::
                          LookupWithIndex k dic :~: 'Just '(v, n)
                      )
                    $ go off l
                      <> f (Proxy @k) (Proxy @v) (Proxy @n)
                      <> go (lSize + 1) r

foldMapOrdMap ::
  forall dic w.
  (Monoid w, Known dic) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    w
  ) ->
  w
{-# INLINE foldMapOrdMap #-}
foldMapOrdMap = foldMapOrdMapAux @_ @_ @dic

foldMapOrdMapAux ::
  forall key val (dic :: OrdMap key val) w.
  (Monoid w, Known dic) =>
  ( forall k v n.
    (Known k, Known v, LookupWithIndex k dic ~ 'Just '(v, n), KnownNat n) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    w
  ) ->
  w
foldMapOrdMapAux f = go 0 $ sKnownVal' @dic
  where
    go :: forall (xs :: OrdMap key val). Natural -> SOrdMap xs -> w
    go _ SLeaf = mempty
    go !off (SBranch _ _ _ (l :: SOrdMap l) (k :: Sing k) (v :: Sing v) r) =
      let lSize = demote (sSize l) + off
       in case promote @Nat lSize of
            MkSomeSing (sn :: SNat n) ->
              withKnown' k
                $ withKnown' v
                $ withKnownNat' sn
                $ gcastWith
                  ( unsafeCoerce (Refl @()) ::
                      LookupWithIndex k dic :~: 'Just '(v, n)
                  )
                $ go off l
                  <> f (Proxy @k) (Proxy @v) (Proxy @n)
                  <> go (lSize + 1) r

foldMapOrdMapC' ::
  forall c dic w.
  (Monoid w, AllOM c dic) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    , c k v
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    w
  ) ->
  w
foldMapOrdMapC' f = go 0 $ sKnownVal' @dic
  where
    go :: forall xs. (AllOM c xs) => Natural -> SOrdMap xs -> w
    go _ SLeaf = mempty
    go !off (SBranch _ _ _ l (k :: Sing k) (v :: Sing v) r) =
      withKnown' k $
        withKnown' v $
          let lSize = demote (sSize l) + off
           in case promote @Nat lSize of
                MkSomeSing (sn :: SNat n) ->
                  withKnownNat' sn
                    $ gcastWith
                      ( unsafeCoerce (Refl @()) ::
                          LookupWithIndex k dic :~: 'Just '(v, n)
                      )
                    $ let !ml = go off l
                          !mid = f (Proxy @k) (Proxy @v) (Proxy @n)
                          !mlmid = ml <> mid
                          !mr = go (lSize + 1) r
                       in mlmid <> mr

foldMapOrdMap' ::
  forall dic w.
  (Monoid w, Known dic) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    w
  ) ->
  w
{-# INLINE foldMapOrdMap' #-}
foldMapOrdMap' = foldMapOrdMap'_ @_ @_ @dic

foldMapOrdMap'_ ::
  forall key val (dic :: OrdMap key val) w.
  (Monoid w, Known dic) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    w
  ) ->
  w
foldMapOrdMap'_ f = go 0 $ sKnownVal' @dic
  where
    go :: forall (xs :: OrdMap key val). Natural -> SOrdMap xs -> w
    go _ SLeaf = mempty
    go !off (SBranch _ _ _ l (k :: Sing k) (v :: Sing v) r) =
      withKnown' k $
        withKnown' v $
          let lSize = demote (sSize l) + off
           in case promote @Nat lSize of
                MkSomeSing (sn :: SNat n) ->
                  withKnownNat' sn
                    $ gcastWith
                      ( unsafeCoerce (Refl @()) ::
                          LookupWithIndex k dic :~: 'Just '(v, n)
                      )
                    $ let !ml = go off l
                          !mid = f (Proxy @k) (Proxy @v) (Proxy @n)
                          !mlmid = ml <> mid
                          !mr = go (lSize + 1) r
                       in mlmid <> mr

foldrMOrdMap ::
  forall dic m b.
  (Monad m, Known dic) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    b ->
    m b
  ) ->
  b ->
  m b
foldrMOrdMap = \f ->
  appEndoM $
    foldMapOrdMap @dic (\pk pv pn -> EndoM $ f pk pv pn)

foldrMOrdMapC ::
  forall c dic m b.
  (AllOM c dic, Monad m) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    , c k v
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    b ->
    m b
  ) ->
  b ->
  m b
foldrMOrdMapC = \f ->
  appEndoM $
    foldMapOrdMapC @c @dic (\pk pv pn -> EndoM $ f pk pv pn)

foldrOrdMap ::
  forall dic b.
  (Known dic) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    b ->
    b
  ) ->
  b ->
  b
foldrOrdMap = \f ->
  appEndo $
    foldMapOrdMap @dic (\pk pv pn -> Endo $ f pk pv pn)

foldrOrdMapC ::
  forall c dic b.
  (AllOM c dic) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    , c k v
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    b ->
    b
  ) ->
  b ->
  b
foldrOrdMapC = \f ->
  appEndo $
    foldMapOrdMapC @c @dic (\pk pv pn -> Endo $ f pk pv pn)

foldlMOrdMapC' ::
  forall c dic m b.
  (AllOM c dic, Monad m) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    , c k v
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    b ->
    m b
  ) ->
  b ->
  m b
foldlMOrdMapC' f =
  foldrOrdMapC @c @dic
    (\pk pv pn k z -> (k $!) =<< f pk pv pn z)
    return

foldlMOrdMap' ::
  forall dic m b.
  (Known dic, Monad m) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    b ->
    m b
  ) ->
  b ->
  m b
foldlMOrdMap' f =
  foldrOrdMap @dic
    (\pk pv pn k z -> (k $!) =<< f pk pv pn z)
    return

foldlOrdMapC' ::
  forall c dic m b.
  (AllOM c dic, Monad m) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    , c k v
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    b ->
    b
  ) ->
  b ->
  b
foldlOrdMapC' f =
  foldrOrdMapC @c @dic
    (\pk pv pn k z -> k $! f pk pv pn z)
    id

foldlOrdMap' ::
  forall dic m b.
  (Known dic, Monad m) =>
  ( forall k v n.
    ( Known k
    , Known v
    , LookupWithIndex k dic ~ 'Just '(v, n)
    , KnownNat n
    ) =>
    Proxy k ->
    Proxy v ->
    Proxy n ->
    b ->
    b
  ) ->
  b ->
  b
foldlOrdMap' f =
  foldrOrdMap @dic
    (\pk pv pn k z -> k $! f pk pv pn z)
    id

class (c a, d b) => BothC c d a b

instance (c a, d b) => BothC c d a b

omMembership :: forall l dic. (Member l dic) => OMMembership l dic
omMembership = OMMembership $ natVal @(Index l dic) Proxy

{- | A variant of 'omMembership' with all the
   type- and kind-variables are explicitly quantified;
   for use with internal or type-checker plugin issues.
-}
omMembership' ::
  forall key val (l :: key) (dic :: OrdMap key val).
  (Member l dic) =>
  OMMembership l dic
{-# INLINE omMembership' #-}
omMembership' = omMembership

-- | 'omMembership''-analogue of 'allOMDict'.
allOMDict' ::
  forall
    key
    val
    (c :: key -> val -> Constraint)
    (dic :: OrdMap key val)
    (l :: key).
  (AllOM c dic, Member l dic) =>
  CustomDict (c l (Lookup' l dic))
{-# INLINE allOMDict' #-}
allOMDict' =
  withDict (allOMDict @c @dic (omMembership @l @dic)) $
    CDict @(c l (Lookup' l dic))

fromLabelListMember ::
  forall l dic.
  (List.Member l (Labels dic)) =>
  OMMembership l dic
fromLabelListMember =
  unsafeCoerce $
    membership @l @(Labels dic)

class
  (c (Label f) (Entry f)) =>
  FieldC c (f :: Field k v)

instance
  (c k v) =>
  FieldC c (k ::: v)

{-# INLINE elimAllOM #-}
elimAllOM ::
  forall c dic k r.
  (AllOM c dic) =>
  OMMembership k dic ->
  ((c k (Lookup' k dic)) => r) ->
  r
elimAllOM el = withDict (allOMDict @c el)

allOMToAllFieldCDict ::
  forall
    key
    val
    (c :: key -> val -> Constraint)
    (dic :: OrdMap key val).
  (AllOM c dic, KnownTyList (ToList dic)) =>
  CustomDict (All (FieldC c) (ToList dic))
allOMToAllFieldCDict = allOMToListAll @_ @_ @c @dic CDict

allOMToListAll ::
  forall key val (c :: key -> val -> Constraint) dic r.
  ( AllOM c (dic :: OrdMap key val)
  , KnownTyList (ToList dic)
  ) =>
  ((All (FieldC c) (ToList dic)) => r) ->
  r
allOMToListAll = withAllFromMember @(FieldC c) @(ToList dic) $
  \(_ :: Proxy fld) ->
    gcastWith (elimFieldCons @fld) $
      withToListMember @fld @dic $
        elimAllOM @c @dic @(Label fld)
          omMembership
          (Dict :: Dict (FieldC c fld))

elimFieldCons ::
  l :~: (Label l ::: Entry l)
elimFieldCons = unsafeCoerce $ Refl @()

type EntryC :: forall (k :: Type) (v :: Type). (v -> Constraint) -> k -> v -> Constraint

-- | To be used with 'foldMapRecC', 'traverseRecC' etc.
class (c v) => EntryC c l v

instance (c v) => EntryC c l v

-- | To be used with 'foldMapRecC', 'traverseRecC' etc.
class (c l) => LabelC c l v

instance (c l) => LabelC c l v

withAllConstMap ::
  forall k c (xs :: [k]) r.
  (SOrd k, All c xs, Known xs, SortableList xs) =>
  ((AllOM (LabelC c) (ConstMap xs)) => r) ->
  r
withAllConstMap = withDict (sortAllDict @_ @c @xs)

sortAllDict ::
  forall l c xs.
  (SOrd l) =>
  (All c (xs :: [l]), Known xs, SortableList xs) =>
  Dict (AllOM (LabelC c) (ConstMap xs))
sortAllDict =
  let sl = sConstMap $ sKnownVal' @xs
   in go 0 sl
  where
    dicts = V.fromList $ sortedDicts @c @xs
    go :: Int -> SOrdMap dic -> Dict (AllOM (LabelC c) dic)
    go _ SLeaf = Dict
    go !n (SBranch col m rk l (k :: Sing lab) v r) =
      withKnownNat' m $
        withKnown' col $
          withKnown' rk $
            withKnown' l $
              withKnown' r $
                withKnown' k $
                  withKnown' v $
                    let !cur = fromIntegral (demote $ sSize l) + n
                     in case dicts V.! cur of
                          ElemDict _ _ (unsafeCoerce @_ @(Dict (c lab)) -> Dict) ->
                            case (go n l, go (cur + 1) r) of
                              (Dict, Dict) -> Dict

sortedDicts ::
  forall c xs.
  (SortableList xs, All c xs) =>
  [ElemDict c xs]
sortedDicts = unsafeCoerce dicts
  where
    dicts =
      V.toList $
        V.unsafeBackpermute dicts0 $
          V.convert sortPerms
    dicts0 = V.fromList $ genDicts @c @xs
    sortPerms = sortPermutation @(ConstList xs)

allOMIntro ::
  forall c dic r.
  (Known dic) =>
  ( forall l v n.
    ( LookupWithIndex l dic ~ 'Just '(v, n)
    , KnownNat n
    , Known l
    , Known v
    ) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    Dict (c l v)
  ) ->
  ((AllOM c dic) => r) ->
  r
allOMIntro f = withDict (allOMDictIntro @c @dic f)

allOMDictIntro ::
  forall c dic.
  (Known dic) =>
  ( forall l v n.
    ( LookupWithIndex l dic ~ 'Just '(v, n)
    , KnownNat n
    , Known l
    , Known v
    ) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    Dict (c l v)
  ) ->
  Dict (AllOM c dic)
allOMDictIntro iter = go 0 $ sKnownVal' @dic
  where
    go :: Natural -> Sing xs -> Dict (AllOM c xs)
    go _ SLeaf = Dict
    go offset (SBranch col siz rk l (k :: Sing l) (v :: Sing v) r) =
      withKnownNat' siz $
        withKnown' col $
          withKnown' rk $
            withKnown' k $
              withKnown' v $
                withDict (go offset l) $
                  withDict (go (offset + demote (sSize l) + 1) r) $
                    case promote $ offset + demote (sSize l) of
                      MkSomeSing (sn :: SNat n) ->
                        withKnownNat' sn
                          $ gcastWith
                            ( unsafeCoerce $ Refl @() ::
                                LookupWithIndex l dic :~: 'Just '(v, n)
                            )
                          $ withDict
                            (iter (Proxy @l) (Proxy @v) (Proxy @n))
                            Dict

deferAllOMWith ::
  forall c dic r.
  (Known dic) =>
  ( forall l v n.
    ( LookupWithIndex l dic ~ 'Just '(v, n)
    , KnownNat n
    , Known l
    , Known v
    ) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    Either String (Dict (c l v))
  ) ->
  ((AllOM c dic) => r) ->
  Either String r
deferAllOMWith iter act =
  allOMIntro @(DeferrableFor2 c) @dic
    ( \(l :: Proxy l) (v :: Proxy v) n ->
        deferWith @(c l v)
          ( ReifiedDeferrable $ \_ k -> do
              Dict <- iter l v n
              pure k
          )
          Dict
    )
    $ deferEither_
      @(AllOM c dic)
      act

sortAllFieldC ::
  forall key val c dic r.
  ( All (FieldC c) (dic :: [Field key val])
  , SortableLabels dic
  , SOrd key
  , Known dic
  ) =>
  ((AllOM c (FromList dic)) => r) ->
  r
sortAllFieldC = \act ->
  withKnown' (sFromList $ sKnownVal' @dic) $
    allOMIntro @c @(FromList dic) @r
      ( \(_ :: Proxy l) (_ :: Proxy v) (_ :: Proxy n) ->
          unsortMembership @l @v @dic $
            elimByAll @(FieldC c) @(l ::: v) @dic
              (Dict :: Dict (c l v))
      )
      act

type family
  AlignOM
    (dic :: OrdMap key val)
    (dic' :: OrdMap key val') ::
    OrdMap key (These val val')
  where
  AlignOM 'Leaf 'Leaf = 'Leaf
  AlignOM 'Leaf r = Con 'That <$> r
  AlignOM l 'Leaf = Con 'This <$> l
  AlignOM ('Branch c n rk l0 k v r0) r = AlignOMAux (Split k r) l0 k v r0

type family AlignOMAux splt l k v r where
  AlignOMAux '(l1, 'Nothing, r1) l k v r =
    Join (AlignOM l l1) k ('This v) (AlignOM r r1)
  AlignOMAux '(l1, 'Just '(_, v'), r1) l k v r =
    Join (AlignOM l l1) k ('These v v') (AlignOM r r1)

sFMapOM :: (forall x. Sing x -> Sing (f x)) -> SOrdMap dic -> SOrdMap (Con f <$> dic)
sFMapOM _ SLeaf = SLeaf
sFMapOM sf (SBranch c n rk l k v r) =
  SBranch c n rk (sFMapOM sf l) k (sf v) (sFMapOM sf r)

sAlignOM ::
  (SOrd key) =>
  SOrdMap (dic :: OrdMap key val) ->
  SOrdMap (dic' :: OrdMap key val') ->
  SOrdMap (AlignOM dic dic')
sAlignOM SLeaf SLeaf = SLeaf
sAlignOM SLeaf r@SBranch {} = sFMapOM SThat r
sAlignOM l@SBranch {} SLeaf = sFMapOM SThis l
sAlignOM (SBranch _ _ _ l k v r) r'@SBranch {} =
  case sSplit k r' of
    SMkTriple l1 SNothing r1 ->
      sJoin (sAlignOM l l1) k (SThis v) (sAlignOM r r1)
    SMkTriple l1 (SJust (SPair _ v')) r1 ->
      sJoin (sAlignOM l l1) k (SThese v v') (sAlignOM r r1)

elimMaybeCLookup' ::
  forall k v (c :: v -> Constraint) (label :: k) (dic :: OrdMap k v).
  (SOrd k, Known label, AllOM (EntryC c) dic) =>
  CustomDict (MaybeC c (Lookup label dic))
elimMaybeCLookup' =
  case sLookupWithIndex (sKnownVal' @label) (sKnownVal' @dic) of
    SNothing -> CDict
    SJust (SPair _ n) ->
      withKnownNat' n $ elimAllOM @(EntryC c) @dic @label omMembership CDict
