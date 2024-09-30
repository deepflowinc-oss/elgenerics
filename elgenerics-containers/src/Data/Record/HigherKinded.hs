{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-unused-top-binds -dcore-lint #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}

module Data.Record.HigherKinded
  ( Record (MkRecord),
    type (:::),
    WithMembership(..),
    Uncurried (..),
    OnLabel (..),
    OnLabel',
    OnEntry (..),
    OnEntry',
    STagged,
    SConst,
    getSConst,
    IsSubRecordOf,
    HasRecField,
    deferHasRecField,
    type (⊑),
    LabelName,
    Entries,
    Extendible,
    Modifiable,
    Field (..),
    FieldLabel (..),
    EntryAt,
    FieldAt,
    HasLabel,
    Labels,
    Singleton,
    type (<:),
    (:=) (..),
    extends,
    Recordable,
    HRecordable,
    hfieldL',
    RecordRep,
    AllOM,
    FieldC,
    EntryC,
    LabelC,
    OverC,
    castRecord,
    singletonRec,
    singletonRec',
    emptyRec,
    recField,
    (&.),
    (&+),
    (&%~),
    (&|~),
    (&-),
    traverseRec,
    traverseRecC,
    traverseRec_,
    traverseRecC_,
    sequenceRec,
    foldMapRec,
    foldMapRecC,
    foldrRec,
    foldrMRec,
    foldlRec',
    viewField,
    viewField',
    recFieldTraversal,
    projField,
    CouldHaveField,
    CmpLabel,
    Entry,
    Label,
    Entry',
    Label',
    SortFields,
    ToLabel,
    sToLabel,
    Shown (..),
    unzipWithM,
    unzipWith,
    mapRecSame,
    mapMRecSame,
    mergeRec,
    Mergeable,
    alignRec,
    alignRecWith,
    alignRecWithM,
    unalignRec,
    collectRec,
    These(..),
    TheseF(..),
    TheseC,
    zipWithM,
    zipWith,
    zipWithM3,
    zipWith3,
    unzip, -- Merge,
    ShowableRecord,
    EqRecord,
    OrdRecord,
    GenericRecord,
    fieldToLabelMembership,
    entrySortIdentFields,
    labelSortIdentFields,
    field,
    IsRecord (..),
    GIsHRecord (),
    IsHRecord (..),
    fromHRecord',
    -- SerialRec,
    -- SerialiseWith,
    -- resolveGenericRecord,
    projToRecord,
    withLabelsMember,
    withKnownLabels,
    generateRec,
    generateRecM,
    generateRecA,
    elimFieldCons,
    fields,

    -- * フィールドがダミーの場合
    ConstField,
    ConstFields,
    ConstField1,
    ConstFields1,
    elimConstField,

    -- * 要素とフィールドが一致している場合
    IdentField,
    IdentFields,
    memberIdent,
    elimMemberIdent,
    identFieldRefl,

    -- * Re-exports
    FromList,
    FromAscList,
  )
where

import Control.Arrow
import Control.Category.Monoid
import Control.DeepSeq
import qualified Control.Foldl as L
import Control.Lens
  ( Iso',
    Lens',
    Traversal',
    coerced,
    iso,
    ix,
    (%~),
    (&),
    (.~),
    (<&>),
  )
import Data.Bifunctor.Product
import Data.Constraint (Dict (..))
import Data.Constraint.Deferrable
import Data.Constraint.Operators
import Data.DList (DList)
import qualified Data.DList as DL
import Data.Functor.Const
import Data.Functor.Identity
import qualified Data.Functor.Product as F
import Data.HList.HigherKinded hiding (generate, generateM)
import qualified Data.HList.HigherKinded as HL
import Data.HList.Internal
import Data.Kind
import Data.Maybe
import Data.Membership hiding (natVal)
import Data.Monoid (Endo (..))
import qualified Data.Monoid as Mon
import Data.Proxy
import Data.Record.HigherKinded.Internal
import Data.Tagged
import Data.Type.Equality
import Data.TypeLevel.BinTree (BinTree, MkBin, Stop, Val)
import qualified Data.TypeLevel.BinTree as BinTree
import Data.TypeLevel.Function
import Data.TypeLevel.Known
import Data.TypeLevel.List hiding (natVal)
import qualified Data.TypeLevel.List as L
import Data.TypeLevel.Ord hiding (Merge)
import Data.TypeLevel.OrdMap hiding (Member)
import qualified Data.TypeLevel.OrdMap as OrdMap
import Data.TypeLevel.OrdMap.Internal
import Data.TypeLevel.Typeable
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving
import GHC.Exts
import GHC.Generics
import GHC.OverloadedLabels
import GHC.Records
import GHC.TypeLits as TL
import Type.Reflection
import Unsafe.Coerce ( unsafeCoerce )
import qualified VectorBuilder.Builder as VB
import qualified VectorBuilder.Vector as VB
import Prelude hiding (zipWith3, unzip, zipWith)
import qualified Prelude as P hiding (zipWith3)
import Data.These ( These(..) )
import qualified Data.Map.Strict as M
import Data.Align (align,Unalign (unalign))
import Data.Distributive ( Distributive(collect) )

class c (h k v) => OverC h c k v

instance c (h k v) => OverC h c k v

instance Deferrable (c (h k v)) => Deferrable (OverC h c k v) where
  deferEither _ = \act -> deferEither_ @(c (h k v)) act
  {-# INLINE deferEither #-}

infix 4 :=

data IdentField :: k ~> Field k k

type instance Apply IdentField ty = ty ::: ty

type IdentFields xs = MapApply IdentField xs

-- | 曖昧性除去のため、依存しない値部分のカインドを引数に取る 'OnLabel' のシノニム。
type OnLabel' v = (OnLabel :: (k -> Type) -> k -> v -> Type)

-- | 曖昧性除去のため、依存しないラベル部分のカインドを引数に取る 'OnEntry' のシノニム。
type OnEntry' k = (OnEntry :: (v -> Type) -> k -> v -> Type)

instance Deferrable (c k v) => Deferrable (FieldC c (k ::: v)) where
  deferEither _ = \act -> deferEither_ @(c k v) act

class
  ( LookupWithIndex l ys ~ 'Just '(x, OrdMap.Index l ys)
  , HasLabel l ys
  ) =>
  HasRecField (ys :: OrdMap k v) l x

instance
  ( LookupWithIndex l ys ~ 'Just '(x, OrdMap.Index l ys)
  , HasLabel l ys
  ) =>
  HasRecField (ys :: OrdMap k v) l x

instance
  ( Known dic
  , Known (l :: key)
  , Known (x :: val)
  , ShowSing key
  , ShowSing val
  , SOrd key
  , STestEquality val
  ) =>
  Deferrable (HasRecField dic l x)
  where
  deferEither _ =
    deferHasRecField (sKnownVal' @dic) (sKnownVal' @l) (sKnownVal' @x)
  {-# INLINE deferEither #-}

deferHasRecField ::
  forall r key val dic l x.
  ( Known dic
  , Known (l :: key)
  , Known (x :: val)
  , ShowSing key
  , ShowSing val
  , SOrd key
  , STestEquality val
  ) =>
  SOrdMap dic ->
  Sing l ->
  Sing x ->
  (HasRecField dic l x => r) ->
  Either String r
{-# INLINE deferHasRecField #-}
deferHasRecField (dic :: SOrdMap dic) (l :: Sing l) (x :: Sing x) r =
  case sLookupWithIndex l dic of
    SNothing ->
      Left $
        "The key `" ++ show (sKnownVal' @l)
          ++ "' is absent in the given dictionary: "
          ++ show (sKnownVal' @dic)
    SJust (SPair sx idx)
      | Equal <- sTestEquality sx x ->
        withKnownNat' idx $ Right r
      | otherwise ->
        Left $
          "The key `" ++ show (sKnownVal' @l)
            ++ "' is present, but associated with different value; in dictionary: "
            ++ show (sKnownVal' @dic)

class
  ( AllOM (HasRecField ys) xs
  ) =>
  IsSubRecordOf xs ys

instance
  ( AllOM (HasRecField ys) xs
  ) =>
  IsSubRecordOf xs ys

instance
  ( Known (xs :: OrdMap k v)
  , ShowSing k
  , ShowSing v
  , Known ys
  , SOrd k
  , ShowSing k
  , ShowSing v
  , STestEquality v
  ) =>
  Deferrable (IsSubRecordOf xs ys)
  where
  deferEither _ f = go (sKnownVal' @xs) <&> \Dict -> f
    where
      ys = sKnownVal' @ys
      go ::
        SOrdMap (zs :: OrdMap k v) ->
        Either String (Dict (IsSubRecordOf zs ys))
      go SLeaf = Right Dict
      go (SBranch c n rk l (k :: Sing l) (v :: Sing x) r) =
        withKnown' c $
          withKnownNat' n $
            withKnown' rk $
              withKnown' k $
                withKnown' v $ do
                  Dict <- deferHasRecField @(Dict (HasRecField ys l x)) ys k v Dict
                  Dict <- go l
                  Dict <- go r
                  pure Dict

type xs ⊑ ys = IsSubRecordOf xs ys

memberIdent ::
  forall p ps.
  Member p ps =>
  Membership (p ::: p) (MapApply IdentField ps)
memberIdent = unsafeCoerce $ membership @p @ps

elimMemberIdent ::
  forall p ps.
  Member (p ::: p) (MapApply IdentField ps) =>
  Membership p ps
elimMemberIdent = unsafeCoerce $ membership @(p ::: p) @(MapApply IdentField ps)

elemAtIdent ::
  ElemAt k (MapApply IdentField ps)
    :~: (ElemAt k ps ::: ElemAt k ps)
elemAtIdent = unsafeCoerce $ Refl @()

identFieldRefl ::
  Member (l ::: x) (MapApply IdentField ps) =>
  l :~: x
identFieldRefl = unsafeCoerce $ Refl @()

unRecord :: Record h recs -> HList (Uncurried h) (ToList recs)
unRecord (Record l) = l

type LabelName ::
  forall (k :: Type). k -> Symbol
type family LabelName (l :: k) :: Symbol where
  LabelName (l :: Symbol) = l
  LabelName l = ShowTypeRep (TypeRepOf l)

type family TyConName (f :: k -> Type) :: Symbol where
  TyConName (D1 ( 'MetaData l _ _ 'False) _) = l

type ToSel (h :: label -> key -> Type) (l :: label) (k :: key) =
  S1
    ( 'MetaSel
        ( 'Just (LabelName l))
        'NoSourceUnpackedness
        'NoSourceStrictness
        'DecidedLazy
    )
    (Rec0 (h l k))

type RecordRep h xs =
  D1
    ( 'MetaData "Record" "Data.Record.HigherKinded" "elgenerics" 'False)
    ( C1
        ( 'MetaCons "Record" 'PrefixI 'True)
        (ToProds h xs)
    )

newtype Shown (f :: k -> v -> Type) a b = Shown {_runShown :: f a b}

deriving newtype instance
  {-# OVERLAPPABLE #-}
  Show (f a b) =>
  Show (Shown f a b)

instance {-# OVERLAPPING #-} Show a => Show (Shown Const a b) where
  showsPrec d = coerce $ showsPrec @a d

instance {-# OVERLAPPING #-} Show b => Show (Shown Tagged a b) where
  showsPrec d = coerce $ showsPrec @b d

class Typeable a => ToLabel a where
  typeLabel :: TypeRep a -> ShowS

sToLabel :: forall l. ToLabel l => String
sToLabel = typeLabel (typeRep @l) ""

instance {-# OVERLAPPABLE #-} Typeable a => ToLabel a where
  typeLabel = shows

instance {-# OVERLAPPING #-} KnownSymbol s => ToLabel s where
  typeLabel = showString . symbolVal

tyLabels ::
  forall as pxy.
  (AllOM (LabelC ToLabel) as) =>
  pxy as ->
  [ShowS]
tyLabels _ =
  DL.toList $
    foldMapOrdMapC @(LabelC ToLabel) @as $
      \(Proxy :: Proxy l) _ _ ->
        DL.singleton $
          typeLabel (typeRep @l)

type ShowableRecord h (xs :: OrdMap k v) =
  ( AllOM (LabelC ToLabel) xs
  , AllOM (OverC (Shown h) Show) xs
  )

instance
  ( AllOM (OverC h NFData) xs
  ) =>
  NFData (Record h xs)
  where
  rnf =
    foldlRec'
      (\_ _ _ () b -> rnf b `seq` ())
      ()
  {-# INLINE rnf #-}

instance
  (ShowableRecord h (xs :: OrdMap key val)) =>
  Show (Record h xs)
  where
  showsPrec _ (Record HNil) = showString "Record {}"
  showsPrec d r =
    showParen (d > 10) $
      let labs = tyLabels $ Proxy @xs
          vals =
            DL.toList $
              foldMapRecC @(OverC (Shown h) Show)
                ( \_ _ _ hkv ->
                    DL.singleton $ shows $ Shown hkv
                )
                r
       in showString "Record {"
            . foldr1
              (\a b -> a . showString ", " . b)
              ( P.zipWith
                  (\l v -> l . showString " = " . v)
                  labs
                  vals
              )
            . showChar '}'

type GenericRecord h xs = GRec (RecordRep h xs)

instance
  (GenericRecord h xs) =>
  Generic (Record h xs)
  where
  type Rep (Record h xs) = RecordRep h xs
  to = Record . HL . V.fromList . toList . gTo
  from (Record (HL vec)) = gFrom vec

class GRec f where
  gTo :: f x -> DList Any
  gFrom' :: V.Vector Any -> (f x, V.Vector Any)

gFrom :: GRec f => V.Vector Any -> f x
{-# INLINE gFrom #-}
gFrom = fst . gFrom'

instance
  {-# OVERLAPPING #-}
  (Generic (UnwrapNewtype f), GRec (Rep (UnwrapNewtype f))) =>
  GRec (D1 ( 'MetaData a b c 'True) f)
  where
  gTo =
    gTo . from . unsafeCoerce @_ @(UnwrapNewtype f)
  gFrom' =
    first (unsafeCoerce @(UnwrapNewtype f) . to) . gFrom' @(Rep (UnwrapNewtype f))

instance GRec U1 where
  gTo = const $ DL.empty
  gFrom' = (U1,)

instance {-# OVERLAPPABLE #-} GRec f => GRec (M1 i c f) where
  gTo = gTo . unM1
  gFrom' = first M1 . gFrom'

instance (GRec f, GRec g) => GRec (f :*: g) where
  gTo (l :*: g) = gTo l <> gTo g
  gFrom' vec =
    let (lh, leftover) = gFrom' vec
        (rh, lf') = gFrom' leftover
     in (lh :*: rh, lf')

instance {-# OVERLAPPING #-} GRec (K1 i c) where
  gTo (K1 i) = DL.singleton $ unsafeCoerce i
  gFrom' =
    (K1 . unsafeCoerce . V.unsafeHead)
      &&& V.unsafeTail

type family ToProds h xs :: Type -> Type where
  ToProds _ 'Leaf = U1
  ToProds h (Branch _ _ _ Leaf k v Leaf) = ToSel h k v
  ToProds h (Branch _ _ _ Leaf k v r) = ToSel h k v :*: ToProds h r
  ToProds h (Branch _ _ _ l k v Leaf) = ToProds h l :*: ToSel h k v
  ToProds h (Branch _ _ _ l k v r) =
    ToProds h l
      :*: ToSel h k v
      :*: ToProds h r

data (:=) l b = FieldLabel l := b
  deriving (Functor)

deriving instance (KnownSymbol l, Show b) => Show (l := b)

deriving instance (KnownSymbol l, Eq b) => Eq (l := b)

data FieldLabel (l :: label) = FieldLabel
  deriving (Eq, Ord)

instance KnownSymbol l => Show (FieldLabel l) where
  showsPrec d = showsPrec d . symbolVal

-- N.B. 以下の ~~ は heterogeneous equality である。
-- つまり、a priori には カインドが異なるかもしれない @l@ と @l'@ が与えられた
-- 時に、それらが同種のカインドに属し、なおかつ値として等しいことを要求している。
-- これを通常の等値性 @l ~ l'@ で置き換えてしまうと、@l@ が @'Symbol'@ の
-- 場合のインスタンスしか生成されず、たとえば @empRec &+ #foo := 12@ とやっても、
-- @:=@ 左辺の @#foo :: FieldLabel l'@ における @l'@ のカインドが一意に決まらず、
-- インスタンス解決に失敗する。ここでは @~~@ を用いることで、@l'@ が Symbol のとき、
-- その時に限り @FieldLabel l'@ が @IsLabel@ のインスタンスになるように制限している。
instance (KnownSymbol l, l ~~ l') => IsLabel l (FieldLabel l') where
  fromLabel = FieldLabel

emptyRec ::
  Record
    (h :: k -> v -> Type)
    (OrdMap.Empty :: OrdMap k v)
emptyRec = Record HNil

singletonRec ::
  forall h l a. h l a -> Record h (Singleton l a)
singletonRec = Record . HL . V.singleton . unsafeCoerce @(h l a) @Any

singletonRec' ::
  l := h l a ->
  Record h (Singleton l a)
singletonRec' ((:=) _ r) = singletonRec r

infixr 9 <:

type (<:) x xs = Insert (Label x) (Entry x) xs

type InsertedIndex x xs = OrdMap.Index (Label x) (x <: xs)

type Extendible l xs =
  ( Mergeable xs (Singleton (Label l) (Entry l))
  , KnownNat (InsertedIndex l xs)
  )

extends ::
  forall l h x xs.
  (Extendible (l ::: x) xs) =>
  l := h l x ->
  Record h xs ->
  Record h ((l ::: x) <: xs)
extends (_ := x) (Record hl) =
  let (HL lh, HL rh) = hsplitAt (Proxy @(InsertedIndex (l ::: x) xs)) hl
   in Record $ HL $ lh <> (unsafeCoerce (Uncurried @_ @_ @h @(l ::: x) x) `V.cons` rh)

(&+) ::
  Extendible (l ::: x) xs =>
  Record h xs ->
  l := h l x ->
  Record h ((l ::: x) <: xs)
(&+) = flip extends

infixl 1 &+

(&.) ::
  forall l xs h.
  (HasLabel l xs) =>
  Record h xs ->
  l := h l (Lookup' l xs) ->
  Record h xs
Record hl &. (_ := hx) =
  Record $
    hset
      (Proxy @(OrdMap.Index l xs))
      (unsafeCoerce $ Uncurried @_ @_ @h @(l ::: Lookup' l xs) hx)
      hl

infixl 1 &.

type Modifiable l x recs =
  (HasLabel l recs)

(&%~) ::
  forall l xs h a.
  (Modifiable l a xs) =>
  Record h xs ->
  l := (h l (Lookup' l xs) -> h l a) ->
  Record h ((l ::: a) <: xs)
Record (HL hl) &%~ (_ := f) =
  Record $
    HL $
      hl & ix (fromIntegral $ natVal $ Proxy @(OrdMap.Index l xs))
        %~ unsafeCoerce @_ @Any
          . Uncurried @_ @_ @h @(l ::: a)
          . f
          . curried
          . unsafeCoerce @Any @(Uncurried h (l ::: Lookup' l xs))

infixl 1 &%~

(&|~) ::
  forall l xs a h.
  (HasLabel l xs) =>
  Record h xs ->
  l := h l a ->
  Record h ((l ::: a) <: xs)
Record (HL hl) &|~ (_ := ha) =
  Record $
    HL $
      hl & ix (fromIntegral $ natVal $ Proxy @(OrdMap.Index l xs))
        .~ unsafeCoerce @_ @Any (Uncurried @_ @_ @h @(l ::: a) ha)

infixl 1 &|~

(&-) ::
  forall l xs h.
  HasLabel l xs =>
  Record h xs ->
  FieldLabel l ->
  Record h (Delete l xs)
Record (HL vec) &- _ =
  let n = (fromIntegral $ TL.natVal $ Proxy @(OrdMap.Index l xs))
      (lh, rh) = V.splitAt n vec
   in Record $ HL $ lh <> V.unsafeTail rh

infixl 1 &-

type EqRecord h as = (AllOM (OverC h Eq) as)

instance (EqRecord h as) => Eq (Record h as) where
  (==) =
    fmap
      ( Mon.getAll
          . foldMapRec (const $ const $ const $ Mon.All . getConst . runOnEntry)
      )
      . zipWith @h @h @as @(OnEntry (Const Bool))
        (const $ const $ const $ fmap (OnEntry . Const) . (==))
  {-# INLINE (==) #-}

  (/=) =
    fmap
      ( Mon.getAny
          . foldMapRec (const $ const $ const $ Mon.Any . getConst . runOnEntry)
      )
      . zipWith @h @h @as @(OnEntry (Const Bool))
        (const $ const $ const $ fmap (OnEntry . Const) . (/=))
  {-# INLINE (/=) #-}

type OrdRecord h as = (AllOM (OverC h Ord) as, AllOM (OverC h Eq) as)

instance (OrdRecord h as) => Ord (Record h as) where
  compare =
    fmap
      ( foldMapRec (const $ const $ const $ getConst . runOnEntry)
      )
      . zipWith @h @h @as @(OnEntry (Const Ordering))
        (const $ const $ const $ fmap (OnEntry . Const) . compare)
  {-# INLINE compare #-}

type CmpLabel = Comparing2 Compare2 Label'

type SortFields (xs :: [Field k v]) = SortBy Compare2 xs

instance
  {-# INCOHERENT #-}
  (HasLabel l recs, 'Just x ~ Lookup l recs) =>
  HasField
    l
    (Record h (recs :: OrdMap Symbol k))
    (h l x)
  where
  getField = viewField (field @l)

viewField ::
  forall l recs h.
  (HasLabel l recs) =>
  FieldLabel l ->
  Record h recs ->
  h l (Lookup' l recs)
viewField = const $ viewField' @l

elimLabelToList ::
  forall l recs.
  ElemAt (OrdMap.Index l recs) (ToList recs)
    :~: (l ::: Lookup' l recs)
elimLabelToList = unsafeCoerce $ Refl @()

viewField' ::
  forall l recs h.
  (HasLabel l recs) =>
  Record h recs ->
  h l (Lookup' l recs)
viewField' (Record hl) =
  gcastWith (elimLabelToList @l @recs) $
    curried $ hindex (Proxy @(OrdMap.Index l recs)) hl

recField ::
  forall h xs l.
  (HasLabel l xs) =>
  FieldLabel l ->
  Lens'
    (Record h xs)
    (h l (Lookup' l xs))
{-# INLINE recField #-}
recField _ =
    let n = fromIntegral $ TL.natVal' @(OrdMap.Index l xs) proxy#
     in coerced @(Record h xs) @(Record h xs) @(V.Vector Any) @(V.Vector Any)
          . ix' n
          . iso unsafeCoerce unsafeCoerce

ix' :: Int -> Lens' (V.Vector a) a
{-# INLINE ix' #-}
ix' n = \f v -> f (V.unsafeIndex v n) <&> \a -> V.unsafeUpd v [(n, a)]

{- RULES: GHC 8.8 になったら次のように書けるのにね……
"recField/mono" forall k h xs l. forall.
  recField @h @xs @l @(EntryAt h xs) = recField'
  # -}

field :: forall l. FieldLabel l
field = FieldLabel

memberInsert ::
  forall l xs.
  (HasLabel l xs) =>
  xs :~: ((l ::: Lookup' l xs) <: xs)
memberInsert = unsafeCoerce $ Refl @()

type family UnwrapNewtype f where
  UnwrapNewtype (M1 i c f) = UnwrapNewtype f
  UnwrapNewtype (Rec0 a) = a

type Recordable a =
  ( Generic a
  , GRec (Rep a)
  , KnownTyList (GFields (Rep a))
  )

type HRecordable h a =
  ( Generic a
  , GRec (Rep a)
  , SortableLabels (GHFields h (Rep a))
  , KnownTyList (GHFields h (Rep a))
  )

type GFields f = GHFields (Tagged :: Symbol -> Type -> Type) f

type family GHFields (h :: l -> k -> Type) f :: [Field l k] where
  GHFields (h :: l -> k -> Type) f = BinTree.ToList (GHFieldsAux k l h f)

#if __GLASGOW_HASKELL__ >= 810
type GHFieldsAux ::
  forall k -> forall l ->
  (l -> k -> Type) ->
  (Type -> Type) ->
  BinTree (Field l k)
#endif
type family GHFieldsAux k l h f :: BinTree (Field l k) where
  GHFieldsAux Type Symbol (Tagged :: Symbol -> Type -> Type) (S1 ( 'MetaSel ( 'Just l) _ _ _) (Rec0 a)) =
    Val (l ::: a)
  GHFieldsAux () Symbol (OnLabel h) (S1 ( 'MetaSel ( 'Just l) _ _ _) (Rec0 (h l))) =
    Val (l ::: '())
  GHFieldsAux k Symbol (OnLabel f) (S1 ( 'MetaSel ( 'Just l) _ _ _) (Rec0 (g l))) =
    ValIfEqual f g l (Any :: k)
  GHFieldsAux k Symbol (OnEntry g) (S1 ( 'MetaSel ( 'Just l) _ _ _) (Rec0 (f a))) =
    ValIfEqual f g l a
  GHFieldsAux _ Symbol h (S1 ( 'MetaSel ( 'Just l) _ _ _) (Rec0 (h l a))) =
    Val (l ::: a)
  GHFieldsAux _ Symbol h (S1 ( 'MetaSel ( 'Just l) _ _ _) (Rec0 b)) =
    TypeError ( 'Text "Field " ':<>: 'ShowType l ':<>: 'Text " doesn't match the prefix functor " ':<>: 'ShowType h)
  GHFieldsAux Type Type h (K1 i (h a a)) = Val (a ::: a)
  GHFieldsAux k l h (D1 ( 'MetaData _ _ _ 'True) f) =
    BinTree.FromList (ToList (HFields h (UnwrapNewtype f)))
  GHFieldsAux k l h (D1 ( 'MetaData _ _ _ 'False) f) =
    BinTree.FromList (GHFields h f)
  GHFieldsAux k l h (M1 i c f) = GHFieldsAux k l h f
  GHFieldsAux k l h (f :*: g) =
    MkBin (GHFieldsAux k l h f) (GHFieldsAux k l h g)
  GHFieldsAux k l h U1 = Stop

type family ValIfEqual f g l a where
  ValIfEqual f f l a = Val (l ::: a)
  ValIfEqual f g l a =
    TypeError ( 'Text "Field " ':<>: 'ShowType l ':<>: 'Text " doesn't match the prefix functor " ':<>: 'ShowType f)

type family LabelOf a :: Type

type family TrySort f as where
  TrySort (D1 ( 'MetaData _ _ _ 'True) _) as = as
  TrySort (D1 ( 'MetaData _ _ _ 'False) _) as = SortFields as
  TrySort (M1 i c f) as = TrySort f as

castRecord ::
  (Equivalent recs recs') =>
  Record h recs ->
  Record h recs'
castRecord = coerce

class
  ( Generic a
  , GRec (Rep a)
  , KnownTyList (GHFields h (Rep a))
  , SortableLabels (GHFields h (Rep a))
  ) =>
  GIsHRecord (h :: l -> k -> Type) a
  where
  unsafePerms :: Proxy# a -> V.Vector Int
  unsafePerms _ =
    V.convert $ sortPermutation @(GHFields h (Rep a))

instance
  ( Generic a
  , GRec (Rep a)
  , KnownTyList (GHFields h (Rep a))
  , SortableLabels (GHFields h (Rep a))
  ) =>
  GIsHRecord h a

-- | A variant of 'fromHRecord' with record representation fixed.
fromHRecord' ::
  forall h a.
  IsHRecord h a =>
  Record h (HFields h a) ->
  a
fromHRecord' = fromHRecord


class IsHRecord h a where
  type HFields h a :: (OrdMap l k)
  type HFields h a = FromList (GHFields h (Rep a))

  toHRecord :: a -> Record h (HFields h a)
  default toHRecord ::
    (GIsHRecord h a) =>
    a ->
    Record h (HFields h a)
  toHRecord a =
    let perms = unsafePerms @_ @_ @h (proxy# :: Proxy# a)
     in Record $ HL $ V.unsafeBackpermute (L.fold L.vector $ gTo $ from a) perms
  fromHRecord ::
    Equivalent recs (HFields h a) =>
    Record h recs ->
    a
  default fromHRecord ::
    ( GIsHRecord h a
    , Equivalent recs (HFields h a)
    ) =>
    Record h recs ->
    a
  fromHRecord (Record (HL vec)) =
    let perms = unsafePerms @_ @_ @h (proxy# :: Proxy# a)
     in to $ gFrom $ V.update_ vec perms vec
  hrecordL ::
    Iso' a (Record h (HFields h a))
  hrecordL = iso toHRecord fromHRecord

  hfieldL ::
    forall lab.
    (HasLabel lab (HFields h a)) =>
    FieldLabel lab ->
    Lens'
      a
      (h lab (Lookup' lab (HFields h a)))
  hfieldL l =
    hrecordL @h
      . gcastWith
        (memberInsert @lab @(HFields h a))
        (recField l)

hfieldL' ::
  forall lab h a.
  (IsHRecord h a, HasLabel lab (HFields h a)) =>
  Lens'
    a
    (h lab (Lookup' lab (HFields h a)))
hfieldL' = hfieldL (field @lab)

type instance LabelOf (Record h (as :: (OrdMap l _))) = l

instance IsHRecord (h :: l -> k -> Type) (Record h (as :: (OrdMap l k))) where
  type HFields h (Record h as) = as
  toHRecord = id
  fromHRecord = castRecord

type STagged = (Tagged :: Symbol -> Type -> Type)

class IsRecord (a :: Type) where
  type Fields a :: (OrdMap Symbol Type)
  type Fields a = FromList (GFields (Rep a))
  toRecord ::
    a -> Record STagged (Fields a)
  default toRecord ::
    ( GIsHRecord STagged a
    ) =>
    a ->
    Record STagged (Fields a)
  toRecord a =
    let perms = unsafePerms @_ @_ @STagged (proxy# :: Proxy# a)
     in Record $
          HL $
            V.unsafeBackpermute
              (L.fold L.vector $ gTo $ from a)
              perms

  fromRecord ::
    (Equivalent recs (Fields a)) =>
    Record STagged recs ->
    a
  default fromRecord ::
    (Equivalent recs (Fields a), GIsHRecord STagged a) =>
    Record STagged recs ->
    a
  fromRecord (Record (HL vec)) =
    let perms = unsafePerms @_ @_ @STagged (proxy# :: Proxy# a)
     in to $ gFrom $ V.update_ vec perms vec
  recordL ::
    Iso' a (Record STagged (Fields a))
  recordL = iso toRecord fromRecord
  fieldL ::
    forall l.
    (KnownSymbol l, HasLabel l (Fields a)) =>
    FieldLabel l ->
    Lens' a (Lookup' l (Fields a))
  fieldL l =
    recordL
      . gcastWith
        (memberInsert @l @(Fields a))
        ( recField
            @(Tagged :: Symbol -> Type -> Type)
            l
        )
      . iso (unTagged @l) (Tagged @l)

instance IsRecord (Record STagged (a :: (OrdMap Symbol Type))) where
  type Fields (Record STagged a) = a
  toRecord = id
  fromRecord = castRecord
  recordL = id
  fieldL l@(FieldLabel :: FieldLabel l) =
    gcastWith (memberInsert @l @a) (recField l)
      . iso (unTagged @l) (Tagged @l)

projToRecord ::
  forall recs h a.
  ( IsHRecord h a
  , recs ⊑ HFields h a
  ) =>
  a ->
  Record h recs
projToRecord a =
  let perms = VB.build $
        foldMapOrdMapC @(HasRecField (HFields h a)) @recs $
          \(_ :: Proxy k) (_ :: Proxy v) (_ :: Proxy n) ->
            VB.singleton $
              fromIntegral $
                TL.natVal' @(OrdMap.Index k (HFields h a)) proxy#
   in case toHRecord @h a of
        Record (HL hl') -> Record $ HL $ V.unsafeBackpermute hl' perms

traverseRec ::
  forall f h g as.
  Applicative f =>
  ( forall l p n.
    (LookupWithIndex l as ~ 'Just '(p, n), KnownNat n) =>
    Proxy l ->
    Proxy p ->
    Proxy n ->
    h l p ->
    f (g l p)
  ) ->
  Record h as ->
  f (Record g as)
traverseRec f (Record hl) =
  Record
    <$> htraverse @(Uncurried g) @(ToList as)
      ( \(Proxy :: Proxy n)
         (Uncurried hx) ->
            gcastWith (fieldAtToList @n @as) $
              withToListMember @(FieldAt n as) @as $
                gcastWith (unsafeCoerce $ Refl @() :: (n + 1 <=? Size as) :~: 'True) $
                  gcastWith (elimMemberToList @(FieldAt n as) @as) $
                    gcastWith (indexFieldAt @n @as) $
                      Uncurried 
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 810
                      @_ @_
#endif
                        @g @(FieldAt n as)
                        <$> f (Proxy @(LabelAt n as)) (Proxy @(EntryAt n as)) (Proxy @n) hx
      )
      hl

traverseRecC ::
  forall c f h g as.
  (Applicative f, AllOM c as) =>
  ( forall l p n.
    (LookupWithIndex l as ~ 'Just '(p, n), KnownNat n, c l p) =>
    Proxy l ->
    Proxy p ->
    Proxy n ->
    h l p ->
    f (g l p)
  ) ->
  Record h as ->
  f (Record g as)
{-# INLINE traverseRecC #-}
traverseRecC = \f -> traverseRec $ \(l :: Proxy l) p n hlp ->
  f l p n hlp

traverseRec_ ::
  forall f h as.
  Applicative f =>
  ( forall l p n.
    (LookupWithIndex l as ~ 'Just '(p, n), KnownNat n) =>
    Proxy l ->
    Proxy p ->
    Proxy n ->
    h l p ->
    f ()
  ) ->
  Record h as ->
  f ()
traverseRec_ f (Record hl) =
  HL.htraverse_
    ( \(pn :: Proxy n) (Uncurried hx) ->
        withToListMember @(ElemAt n (ToList as)) @as $
          gcastWith (fieldAtToList @n @as) $
            withToListMember @(FieldAt n as) @as $
              gcastWith (unsafeCoerce $ Refl @() :: (n + 1 <=? Size as) :~: 'True) $
                gcastWith (elimMemberToList @(FieldAt n as) @as) $
                  gcastWith (indexFieldAt @n @as) $
                    gcastWith (elimMemberToList @(ElemAt n (ToList as)) @as) $
                      f (Proxy @(LabelAt n as)) (Proxy @(EntryAt n as)) pn hx
    )
    hl

traverseRecC_ ::
  forall c f h as.
  (Applicative f, AllOM c as) =>
  ( forall l p n.
    (LookupWithIndex l as ~ 'Just '(p, n), KnownNat n, c l p) =>
    Proxy l ->
    Proxy p ->
    Proxy n ->
    h l p ->
    f ()
  ) ->
  Record h as ->
  f ()
{-# INLINE traverseRecC_ #-}
traverseRecC_ = \f -> traverseRec_ $ \(l :: Proxy l) p n hlp ->
  withOrdMapMember @l @as $ f l p n hlp

foldrMRec ::
  forall h fs m b.
  Monad m =>
  ( forall l v n.
    (LookupWithIndex l fs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    b ->
    m b
  ) ->
  b ->
  Record h fs ->
  m b
foldrMRec f = \z r ->
  appEndoM (foldMapRec (\p l n hx -> EndoM $ f p l n hx) r) z

foldrRec ::
  forall h fs b.
  ( forall l v n.
    (LookupWithIndex l fs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    b ->
    b
  ) ->
  b ->
  Record h fs ->
  b
foldrRec f = flip $ \r ->
  appEndo (foldMapRec (\p l n hx -> Endo $ f p l n hx) r)

foldlRec' ::
  forall h fs b.
  ( forall l v n.
    (LookupWithIndex l fs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    b ->
    h l v ->
    b
  ) ->
  b ->
  Record h fs ->
  b
foldlRec' f z0 xs = foldrRec (\l v n x k z -> k $! f l v n z x) id xs z0

foldMapRec ::
  forall h fs w.
  Monoid w =>
  ( forall l v n.
    (LookupWithIndex l fs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    w
  ) ->
  Record h fs ->
  w
foldMapRec f (Record v) =
  hfoldMap
    ( \(Proxy :: Proxy k) (Proxy :: Proxy x) ->
        withToListMember @x @fs $
          gcastWith (elimMemberToList @x @fs) $
            gcastWith (unsafeCoerce $ Refl @() :: L.Index x (ToList fs) :~: k) $
              f (Proxy @(Label x)) (Proxy @(Entry x)) (Proxy @k)
                . curried
    )
    v

foldMapRecC ::
  forall c h fs w.
  (Monoid w, AllOM c fs) =>
  ( forall l v n.
    (LookupWithIndex l fs ~ 'Just '(v, n), KnownNat n, c l v) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    w
  ) ->
  Record h fs ->
  w
{-# INLINE foldMapRecC #-}
foldMapRecC = \f -> foldMapRec f

pattern MkRecord :: Record h OrdMap.Empty
pattern MkRecord = Record HNil

elemAtLabelEntry ::
  ElemAt n (Labels recs) ::: ElemAt n (Entries recs)
    :~: ElemAt n (ToList recs)
elemAtLabelEntry = unsafeCoerce $ Refl @()

entryToFieldMembership ::
  forall n recs.
  (KnownNat n, Member (ElemAt n (Entries recs)) (Entries recs)) =>
  Membership
    (ElemAt n (Labels recs) ::: ElemAt n (Entries recs))
    (ToList recs)
entryToFieldMembership =
  gcastWith (elemAtLabelEntry @n @recs) $
    elemAtMembership @n @(ToList recs)

fieldToLabelMembership ::
  forall l recs.
  (HasLabel l recs) =>
  Membership l (Labels recs)
fieldToLabelMembership =
  unsafeCoerce (fromIntegral $ TL.natVal' @(OrdMap.Index l recs) proxy# :: Word)

zipWithM ::
  forall m h g recs k.
  Monad m =>
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    g l v ->
    m (k l v)
  ) ->
  Record h recs ->
  Record g recs ->
  m (Record k recs)
zipWithM f (Record l) (Record r) =
  Record
    <$> hzipWithM
      ( \(Proxy :: Proxy n) (Uncurried hx) (Uncurried gx) ->
          withToListMember @(ElemAt n (ToList recs)) @recs $
            gcastWith (elimMemberToList @(ElemAt n (ToList recs)) @recs) $
              gcastWith
                ( unsafeCoerce $ Refl @() ::
                    LookupWithIndex (Label (ElemAt n (ToList recs))) recs
                      :~: 'Just '(Entry (ElemAt n (ToList recs)), n)
                )
                $ Uncurried
                  <$> f
                    (Proxy @(Label (ElemAt n (ToList recs))))
                    (Proxy @(Entry (ElemAt n (ToList recs))))
                    (Proxy @n)
                    hx
                    gx
      )
      l
      r

zipWithM3 ::
  forall m h g f recs k.
  Monad m =>
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    g l v ->
    f l v ->
    m (k l v)
  ) ->
  Record h recs ->
  Record g recs ->
  Record f recs ->
  m (Record k recs)
zipWithM3 f (Record l) (Record r) (Record s) =
  Record
    <$> hzipWithM3
      ( \(Proxy :: Proxy n) (Uncurried hx) (Uncurried gx) (Uncurried fx) ->
          withToListMember @(ElemAt n (ToList recs)) @recs $
            gcastWith (elimMemberToList @(ElemAt n (ToList recs)) @recs) $
              gcastWith
                ( unsafeCoerce $ Refl @() ::
                    LookupWithIndex (Label (ElemAt n (ToList recs))) recs
                      :~: 'Just '(Entry (ElemAt n (ToList recs)), n)
                )
                $ Uncurried
                  <$> f
                    (Proxy @(Label (ElemAt n (ToList recs))))
                    (Proxy @(Entry (ElemAt n (ToList recs))))
                    (Proxy @n)
                    hx
                    gx
                    fx
      )
      l
      r
      s
zipWith3 ::
  forall h g f recs k.
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    g l v ->
    f l v ->
    k l v
  ) ->
  Record h recs ->
  Record g recs ->
  Record f recs ->
  Record k recs
zipWith3 f (Record l) (Record r) (Record s) =
  Record
    $ hzipWith3
      ( \(Proxy :: Proxy n) (Uncurried hx) (Uncurried gx) (Uncurried fx) ->
          withToListMember @(ElemAt n (ToList recs)) @recs $
            gcastWith (elimMemberToList @(ElemAt n (ToList recs)) @recs) $
              gcastWith
                ( unsafeCoerce $ Refl @() ::
                    LookupWithIndex (Label (ElemAt n (ToList recs))) recs
                      :~: 'Just '(Entry (ElemAt n (ToList recs)), n)
                )
                $ Uncurried
                  $ f
                    (Proxy @(Label (ElemAt n (ToList recs))))
                    (Proxy @(Entry (ElemAt n (ToList recs))))
                    (Proxy @n)
                    hx
                    gx
                    fx
      )
      l
      r
      s

zipWith ::
  forall h g recs k.
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    g l v ->
    k l v
  ) ->
  Record h recs ->
  Record g recs ->
  Record k recs
zipWith f (Record l) (Record r) =
  Record $
    hzipWith
      ( \(Proxy :: Proxy n) (Uncurried hx) (Uncurried gx) ->
          withToListMember @(ElemAt n (ToList recs)) @recs $
            gcastWith (elimMemberToList @(ElemAt n (ToList recs)) @recs) $
              gcastWith
                ( unsafeCoerce $ Refl @() ::
                    LookupWithIndex (Label (ElemAt n (ToList recs))) recs
                      :~: 'Just '(Entry (ElemAt n (ToList recs)), n)
                )
                $ Uncurried $
                  f
                    (Proxy @(Label (ElemAt n (ToList recs))))
                    (Proxy @(Entry (ElemAt n (ToList recs))))
                    (Proxy @n)
                    hx
                    gx
      )
      l
      r

unzip ::
  forall h g as.
  Record (Product h g) as ->
  (Record h as, Record g as)
unzip = (Record *** Record) . hunzip' . castProducts . unRecord

castProducts ::
  HList (Uncurried (Product h g)) xs ->
  HList (F.Product (Uncurried h) (Uncurried g)) xs
castProducts = hmap $
  const $ \(Uncurried (Pair f g)) ->
    F.Pair (Uncurried f) (Uncurried g)

unzipWithM ::
  forall m h recs g k.
  Monad m =>
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    m (g l v, k l v)
  ) ->
  Record h recs ->
  m (Record g recs, Record k recs)
unzipWithM f (Record hl) =
  (Record *** Record)
    <$> hunzipWithM
      ( \pn@(Proxy :: Proxy n) (Uncurried hx) ->
          withToListMember @(ElemAt n (ToList recs)) @recs $
          gcastWith (fieldAtToList @n @recs) $
            withToListMember @(FieldAt n recs) @recs $
              gcastWith (unsafeCoerce $ Refl @() :: (n + 1 <=? Size recs) :~: 'True) $
                gcastWith (elimMemberToList @(FieldAt n recs) @recs) $
                  gcastWith (indexFieldAt @n @recs) $
                    gcastWith (elimMemberToList @(ElemAt n (ToList recs)) @recs) $
              f (Proxy @(Label (ElemAt n (ToList recs)))) (Proxy @(EntryAt n recs)) pn hx <&> \(l, r) ->
                (Uncurried l, Uncurried r)
      )
      hl

unzipWith ::
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v ->
    (g l v, k l v)
  ) ->
  Record h recs ->
  (Record g recs, Record k recs)
{-# INLINE unzipWith #-}
unzipWith f = runIdentity . unzipWithM (fmap (fmap $ fmap Identity) . f)

generateRec ::
  forall recs h.
  (KnownNat (Size recs)) =>
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h l v
  ) ->
  Record h recs
generateRec f =
  Record $
    HL.generate
      ( \(Proxy :: Proxy k) ->
          gcastWith (elimFieldCons @(FieldAt k recs)) $
            gcastWith (fieldAtToList @k @recs) $
              gcastWith
                ( unsafeCoerce $ Refl @() ::
                    L.Index (ElemAt k (ToList recs)) (ToList recs) :~: k
                )
                $ withToListMember @(FieldAt k recs) @recs $
                  Uncurried $
                    f
                      (Proxy @(LabelAt k recs))
                      (Proxy @(EntryAt k recs))
                      (Proxy @k)
      )

mapMRecSame ::
  forall g h recs f.
  (Applicative f) =>
  ( forall l p n.
    (LookupWithIndex l recs ~ 'Just '(p, n), KnownNat n) =>
    Proxy l ->
    Proxy p ->
    Proxy n ->
    h l p ->
    f (g l p)
  ) ->
  Record h recs ->
  f (Record g recs)
{-# INLINE mapMRecSame #-}
mapMRecSame = traverseRec

mapRecSame ::
  forall g h recs.
  ( forall l p n.
    (LookupWithIndex l recs ~ 'Just '(p, n), KnownNat n) =>
    Proxy l ->
    Proxy p ->
    Proxy n ->
    h l p ->
    g l p
  ) ->
  Record h recs ->
  Record g recs
{-# INLINE mapRecSame #-}
mapRecSame f =
  runIdentity
    . mapMRecSame (\l p n hx -> Identity (f l p n hx))

generateRecM ::
  forall recs h m.
  ( KnownNat (Size recs)
  , Monad m
  ) =>
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    m (h l v)
  ) ->
  m (Record h recs)
generateRecM f =
  fmap Record $
    HL.generateM
      ( \(Proxy :: Proxy k) ->
          gcastWith (elimFieldCons @(FieldAt k recs)) $
            gcastWith (fieldAtToList @k @recs) $
              gcastWith
                ( unsafeCoerce $ Refl @() ::
                    L.Index (ElemAt k (ToList recs)) (ToList recs) :~: k
                )
                $ withToListMember @(FieldAt k recs) @recs $
                  Uncurried
                    <$> f
                      (Proxy @(LabelAt k recs))
                      (Proxy @(EntryAt k recs))
                      (Proxy @k)
      )

generateRecA ::
  forall recs h m.
  ( KnownNat (Size recs)
  , Applicative m
  ) =>
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    m (h l v)
  ) ->
  m (Record h recs)
generateRecA f =
  fmap Record $
    HL.generateA
      ( \(Proxy :: Proxy k) ->
          gcastWith (elimFieldCons @(FieldAt k recs)) $
            gcastWith (fieldAtToList @k @recs) $
              gcastWith
                ( unsafeCoerce $ Refl @() ::
                    L.Index (ElemAt k (ToList recs)) (ToList recs) :~: k
                )
                $ withToListMember @(FieldAt k recs) @recs $
                  Uncurried
                    <$> f
                      (Proxy @(LabelAt k recs))
                      (Proxy @(EntryAt k recs))
                      (Proxy @k)
      )

entrySortIdentFields ::
  forall ls.
  Entries (FromList (IdentFields ls))
    :~: SortBy Compare2 ls
entrySortIdentFields = unsafeCoerce $ Refl @()

labelSortIdentFields ::
  forall ls.
  Labels (FromList (IdentFields ls))
    :~: SortBy Compare2 ls
labelSortIdentFields = unsafeCoerce $ Refl @()

type Mergeable ls rs =
  (MergeableAux ls rs (Merge ls rs))

type family MergeableAux ls rs merged :: Constraint where
  MergeableAux ls rs merged =
    ( KnownNat (Size merged)
    , Disjoint ls rs
    , Known (MergePerm ls rs)
    )

-- | Merges two /disjoint/ records into one.
mergeRec ::
  forall h recs recs'.
  Mergeable recs recs' =>
  Record h recs ->
  Record h recs' ->
  Record h (Merge recs recs')
mergeRec (Record (HL l)) (Record (HL r)) =
  Record $
    HL $
      V.map
        ( \case
            Left n -> l V.! fromIntegral n
            Right n -> r V.! fromIntegral n
        )
        $ V.fromList $
          knownVal' @(MergePerm recs recs')

data Succ :: Nat ~> Nat

type instance Apply Succ n = n + 1

data IndexWithValMResult key val
  = NotFound
  | Found Nat
  | ValueMismatched key val val

defineSingletons ''IndexWithValMResult
deriveKnown ''IndexWithValMResult
deriveShowSing ''IndexWithValMResult

type IndexWithValM l a fs = IWVMAux l a (LookupWithIndex l fs)

type family IWVMAux l (a :: val) (mb :: Maybe (val, Nat)) where
  IWVMAux _ _ 'Nothing = 'NotFound
  IWVMAux l a ( 'Just '(b, n)) = IWVMAux' (a == b) l a b n

type family
  IWVMAux' ab (l :: key) (a :: val) b n ::
    IndexWithValMResult key val
  where
  IWVMAux' 'True _ _ _ n = 'Found n
  IWVMAux' 'False l a b _ = 'ValueMismatched l a b

type family ResolveCouldHaveField a where
  ResolveCouldHaveField 'NotFound = 'Nothing
  ResolveCouldHaveField ( 'Found n) = 'Just n
  ResolveCouldHaveField ( 'ValueMismatched l a b) =
    TypeError
      ( 'Text "A label:"
          ':$$: 'Text "\t" ':<>: 'ShowType l
          ':$$: 'Text "must be associated with a type:"
          ':$$: 'Text "\t" ':<>: 'ShowType a ':<>: 'Text ","
          ':$$: 'Text "but got:"
          ':$$: 'Text "\t" ':<>: 'ShowType b
      )

class
  (Known (ResolveCouldHaveField (IndexWithValM l a fs))) =>
  CouldHaveField l a fs

instance
  (Known (ResolveCouldHaveField (IndexWithValM l a fs))) =>
  CouldHaveField l a fs

instance
  ( Known (fs :: OrdMap key v)
  , Known (l :: key)
  , Known (a :: v)
  , SOrd key
  , STestEquality v
  , ShowSing key, ShowSing v
  ) =>
  Deferrable (CouldHaveField l a fs)
  where
  deferEither _ r =
    case sIndexWithValM
      (sKnownVal' @l)
      (sKnownVal' @a)
      (sKnownVal' @fs) of
      SFound n -> withKnown' (SJust n) $ Right r
      SNotFound -> Right r
      SValueMismatched _ _ _ ->
        Left $ "A value for label " <> show (sKnownVal' @l) <> " mismatched!"

recFieldTraversal ::
  forall l a h xs.
  CouldHaveField l a xs =>
  Traversal' (Record h xs) (h l a)
recFieldTraversal =
  case knownVal' @(ResolveCouldHaveField (IndexWithValM l a xs)) of
    Nothing -> const pure
    Just n ->
      coerced
        @(Record h xs)
        @(Record h xs)
        @(V.Vector Any)
        @(V.Vector Any)
        . ix' (fromIntegral n)
        . iso unsafeCoerce unsafeCoerce

sIndexWithValM ::
  (SOrd key, STestEquality val) =>
  Sing (l :: key) ->
  Sing (v :: val) ->
  Sing (map :: OrdMap key val) ->
  Sing (IndexWithValM l v map)
sIndexWithValM l a fs =
  case sLookupWithIndex l fs of
    SNothing -> SNotFound
    SJust (SPair (sv :: Sing x) (sn :: SNat n)) ->
      case sTestEquality a sv of
        Equal -> SFound sn
        NonEqual -> SValueMismatched l a sv

projField ::
  forall l a h fs.
  (CouldHaveField l a fs) =>
  Record h fs ->
  Maybe (h l a)
projField (Record (HL hs)) = do
  i <- knownVal' @(ResolveCouldHaveField (IndexWithValM l a fs))
  return $ unsafeCoerce $ hs V.! fromIntegral i

derivingUnbox
  "Record"
  [t|
    forall h recs.
    ( KnownTyList (ToList recs)
    , All U.Unbox (Map (Uncurried h) (ToList recs))
    ) =>
    Record h recs ->
    HList (Uncurried h) (ToList recs)
    |]
  [|\(Record hl) -> hl|]
  [|Record|]

instance POrd l => POrd (Field l v) where
  type Compare p q = Apply (Apply CmpLabel p) q

type family NotMemberB (xs :: [k]) (x :: k) :: Bool where
  NotMemberB '[] x = 'True
  NotMemberB (x ': xs) x = 'False
  NotMemberB (_ ': xs) x = NotMemberB xs x

class NotMemberB xs x ~ 'True => AbsentIn xs x

instance NotMemberB xs x ~ 'True => AbsentIn xs x

type SConst ty = OnEntry' Symbol (Const ty)

fields ::
  forall a.
  ( IsRecord a
  , KnownNat (Size (Fields a))
  , AllOM (LabelC KnownSymbol) (Fields a)
  ) =>
  Record (SConst String) (Fields a)
fields = generateRec $ \(_ :: Proxy l) _ _ ->
  OnEntry $ Const $ symbolVal @l Proxy

getSConst :: SConst a tag b -> a
getSConst = getConst . runOnEntry

sequenceRec ::
  Applicative f =>
  Record (OnEntry f) rec ->
  f (Record Tagged rec)
{-# INLINE sequenceRec #-}
sequenceRec =
  traverseRec $
    const $
      const $
        const $
          fmap Tagged . runOnEntry

data WithMembership h ks l v where
  WithMembership
    :: (KnownNat n, LookupWithIndex l ks ~ 'Just '(v, n))
    => Proxy l -> Proxy n -> h l v -> WithMembership h ks l v

deriving instance
  Show (h l v) => Show (WithMembership h ks l v)

-- | Higher-kinded version of 'These'.
--
-- /c.f./ 'alignRec', 'alignRecWith', 'alignRecWithM', and 'TheseC'.
data TheseF h g k (these :: These val val') where
  ThisF :: forall h g k v. h k v  -> TheseF h g k ('This v)
  ThatF :: forall h g k v'. g k v' -> TheseF h g k ('That v')
  TheseF :: forall h g k v v'. h k v -> g k v' -> TheseF h g k ('These v v')

-- | Dependent constraint family for 'These'.
--
-- /c.f./ 'alignRec', 'alignRecWith', 'alignRecWithM', and 'TheseC'.
type family TheseC c d (v :: These a b) :: Constraint where
  TheseC c _ ('This x) = c x
  TheseC _ d ('That y) = d y
  TheseC c d ('These x y) = (c x, d y)

deriving instance (TheseC (OverC h Show k) (OverC g Show k) v)
  => Show (TheseF h g k v)

newtype OrdSomeSing k = OrdSomeSing (SomeSing k)
instance SOrd k => Eq (OrdSomeSing k) where
  {-# INLINE (==) #-}
  OrdSomeSing (MkSomeSing a) == OrdSomeSing (MkSomeSing b) =
    case sCompare a b of
      SEQ -> True
      _ -> False
  {-# INLINE (/=) #-}
  OrdSomeSing (MkSomeSing a) /= OrdSomeSing (MkSomeSing b) =
    case sCompare a b of
      SEQ -> False
      _ -> True

instance SOrd k => Ord (OrdSomeSing k) where
  compare (OrdSomeSing (MkSomeSing a)) (OrdSomeSing (MkSomeSing b)) = 
    demote $ sCompare a b
  {-# INLINE compare #-}

type Alignable ks ks' =
  ( Known ks, 
    Known ks'
  )

data SomeEntry h ks where
  MkSomeEntry
    :: (LookupWithIndex k ks ~ 'Just '(v, n), KnownNat n)
    => Proxy k -> Proxy n -> h k v -> SomeEntry h ks

withKnownLabels
  :: forall ks r. Known ks
  => (AllOM (LabelC Known) ks => r)
  -> r
withKnownLabels = allOMIntro @(LabelC Known) @ks  $ \ _ _ _-> Dict

-- | O(n)
toSomeEntryMap
  :: (SOrd key, Known (ks :: OrdMap key val))
  => Record h ks
  -> M.Map (OrdSomeSing key) (SomeEntry h ks)
{-# INLINE [1] toSomeEntryMap #-}
toSomeEntryMap (r :: Record h ks) =
  withKnownLabels @ks $
  M.fromAscList $ DL.toList $
  foldMapRecC @(LabelC Known) 
    (\ pkeyl _ pnn hlv -> 
      DL.singleton 
        (OrdSomeSing $ MkSomeSing $ sKnownVal pkeyl, 
        MkSomeEntry pkeyl pnn hlv)
    )
    r

-- | O(n)
fromSomeEntryMap
  :: (SOrd key, Known (ks :: OrdMap key val))
  => M.Map (OrdSomeSing key) (SomeEntry h ks)
  -> Record h ks
{-# INLINE [1] fromSomeEntryMap #-}
fromSomeEntryMap = 
  Record . HL . L.fold 
    (L.premap (\(MkSomeEntry _ _ hkv) -> unsafeCoerce hkv :: Any) L.vector)

{-# RULES
"fromSomeEntryMap/toSomeEntryMap" forall xs.
  fromSomeEntryMap (toSomeEntryMap xs) = xs
  #-}

trustMeEqual :: forall a b. a :~: b
trustMeEqual = unsafeCoerce $ Refl @()

{- |
Aligns two records into one.

The higher-kinded analogue of 'Data.align.align' for 'M.Map' in @semialign@ package.

c.f. 'alignRecWith', 'alignRecWithM', and 'TheseF'.

>>> import Data.Functor.Const
>>> let rec1 = (emptyRec &+ field @"foo" := Tagged True &+ field @"buz" := Tagged "nux")
>>> let rec2 = (emptyRec &+ field @"foo" := Tagged (42 :: Int) &+ field @"bar" := Tagged 'd')
>>> alignRec rec1 rec2
Record {bar = ThatF (WithMembership Proxy Proxy (Tagged 'd')), buz = ThisF (WithMembership Proxy Proxy (Tagged "nux")), foo = TheseF (WithMembership Proxy Proxy (Tagged True)) (WithMembership Proxy Proxy (Tagged 42))}
-}
alignRec
  :: (Alignable ks ks')
  => SOrd key
  => Record h (ks :: OrdMap key val)
  -> Record g (ks' :: OrdMap key val')
  -> Record (TheseF (WithMembership h ks) (WithMembership g ks')) (AlignOM ks ks')
{-# NOINLINE [1] alignRec #-}
alignRec (l :: Record h ks) (r :: Record g ks') = 
  let l' = toSomeEntryMap l
      r' = toSomeEntryMap r
      lr = M.toList $ align l' r'
  in Record $ HL $ V.fromList
    [ case v of
        This (MkSomeEntry (pkk :: Proxy k') pnn hkv) ->
          unsafeCoerce $ 
          ThisF @(WithMembership h ks) @(WithMembership g ks')  
            (WithMembership pkk pnn hkv)
        That (MkSomeEntry (pkk :: Proxy k') pnn gkv) ->
          unsafeCoerce $
          ThatF @(WithMembership h ks) @(WithMembership g ks')  
            (WithMembership pkk pnn gkv)
        These (MkSomeEntry (pkl :: Proxy k) pnn hkv) 
          (MkSomeEntry (pkr :: Proxy k') pnm gkv) ->
            gcastWith (trustMeEqual @k @k') $
            unsafeCoerce $
            TheseF @(WithMembership h ks) @(WithMembership g ks')  
              (WithMembership pkl pnn hkv)
              (WithMembership pkr pnm gkv)
    | (OrdSomeSing (MkSomeSing _), v)
      <- lr
    ]

{- |
Analogous to 'zipWith', combines two records by taking the union of their fields and combining the elements with the given function.

The higher-kinded analogue of 'Data.align.alignWith' for 'M.Map' in @semialign@ package.

c.f. 'alignRec', 'alignRecWithM', and 'TheseF'.
-}
alignRecWith
  :: (Alignable ks ks')
  => SOrd key
  => (forall l n v.
        ( LookupWithIndex l (AlignOM ks ks') ~ 'Just '(v, n)
        , KnownNat n
        ) =>
        Proxy l
        -> Proxy n
        -> TheseF (WithMembership h ks) (WithMembership g ks') l v
        -> k l v)
  -> Record h (ks :: OrdMap key val)
  -> Record g (ks' :: OrdMap key val')
  -> Record k (AlignOM ks ks')
alignRecWith f (l :: Record h ks) (r :: Record g ks') =
  mapRecSame
    (\ pl _pThese pnn theseF
    -> f pl pnn theseF
    )
  $ alignRec l r


{- |
Analogous to 'zipWithM', combines two records by taking the union of their fields and combining the elements with the given monadic function.

The higher-kinded and monadic analogue of 'Data.align.alignWith' for 'M.Map' in @semialign@ package.

c.f. 'alignRec', 'alignRecWith', and 'TheseF'.
-}
alignRecWithM
  :: (Applicative f, Alignable ks ks')
  => SOrd key
  => (forall l n v.
        ( LookupWithIndex l (AlignOM ks ks') ~ 'Just '(v, n)
        , KnownNat n
        ) =>
        Proxy l
        -> Proxy n
        -> TheseF (WithMembership h ks) (WithMembership g ks') l v
        -> f (k l v))
  -> Record h (ks :: OrdMap key val)
  -> Record g (ks' :: OrdMap key val')
  -> f (Record k (AlignOM ks ks'))
alignRecWithM f (l :: Record h ks) (r :: Record g ks') =
  traverseRec
    (\ pl _pThese pnn theseF
    -> f pl pnn theseF
    )
  $ alignRec l r

{- |
The inverse to 'alignRec'.
-}
unalignRec
  :: (Alignable ks ks')
  => SOrd key
  => Record (TheseF (WithMembership h ks) (WithMembership g ks')) (AlignOM ks ks')
  -> (Record h (ks :: OrdMap key v), Record g ks')
{-# NOINLINE [1] unalignRec #-}
unalignRec (r :: Record (TheseF (WithMembership h ks) (WithMembership g ks')) (AlignOM (ks :: OrdMap key val) ks')) = 
  let ksks' = (sAlignOM (sKnownVal' @ks) (sKnownVal' @ks'))
  in withKnown' ksks' $
  withKnownLabels @(AlignOM ks ks') $
  let thsMap :: M.Map (OrdSomeSing key) (These (SomeEntry h ks) (SomeEntry g ks'))
      thsMap = toSomeEntryMap r <&> \case 
        MkSomeEntry _ _ (ThisF (WithMembership pl pm hkv)) -> 
          This (MkSomeEntry pl pm hkv)
        MkSomeEntry _ _ (ThatF (WithMembership pl pm gkv')) ->
          That (MkSomeEntry pl pm gkv')
        MkSomeEntry _ _ 
          (TheseF (WithMembership pl pm hkv) (WithMembership pl' pk gkv')) ->
          These (MkSomeEntry pl pm hkv) (MkSomeEntry pl' pk gkv')
      (ls, rs) = unalign thsMap
  in (fromSomeEntryMap ls, fromSomeEntryMap rs)

{-# RULES
"unalignRec/alignRec" forall ls rs.
  unalignRec (alignRec ls rs) = (ls, rs)
  #-}

-- >>> collectRec @(Identity :*: Identity) @(SConst Int) @(SConst Int) (\_ _ _ (OnEntry (Const l)) -> Identity (OnEntry (Const (l `div` 2))) :*: Identity (OnEntry (Const $ l `mod` 2))) $ emptyRec &+ field @"foo" := OnEntry (Const (12 :: Int) :: Const Int '()) &+ #bar := OnEntry (Const 42 :: Const Int '()) &+ #duz := OnEntry (Const 59 :: Const Int '())
-- Identity (Record {bar = OnEntry {runOnEntry = Const 21}, duz = OnEntry {runOnEntry = Const 29}, foo = OnEntry {runOnEntry = Const 6}}) :*: Identity (Record {bar = OnEntry {runOnEntry = Const 0}, duz = OnEntry {runOnEntry = Const 1}, foo = OnEntry {runOnEntry = Const 0}})

collectRec
  :: forall g k h recs .
    Distributive g
  => ( forall l p n.
    (LookupWithIndex l recs ~ 'Just '(p, n), KnownNat n) =>
    Proxy l ->
    Proxy p ->
    Proxy n ->
    h l p ->
    g (k l p)
  )
  -> Record h recs 
  -> g (Record k recs)
collectRec f (Record (HL vec)) =
  fmap (Record . HL)
  $ collect
      (\(i, v) ->
        withKnownNat (fromIntegral i) $ \(p :: Proxy n) ->
        gcastWith 
        (trustMeEqual :: 
          'Just '(Entry (ElemAt n (ToList recs)), n) :~:
            LookupWithIndex (Label (ElemAt n (ToList recs))) recs
          ) $
        let hlv = f 
                  (Proxy @(Label (ElemAt n (ToList recs)))) 
                  (Proxy @(Entry (ElemAt n (ToList recs))))
                  p
                  (unsafeCoerce v :: h (Label (ElemAt n (ToList recs))) (Entry (ElemAt n (ToList recs))))
        in fmap
              (unsafeCoerce
                :: k (Label (ElemAt n (ToList recs))) (Entry (ElemAt n (ToList recs))) -> Any
              ) hlv
      )
  $ V.indexed vec
