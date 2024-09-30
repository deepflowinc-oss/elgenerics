{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans -dcore-lint #-}
{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}

module Data.TypeLevel.ListSpec.Cases where

import Data.Constraint (Constraint, Dict (Dict))
import Data.DList qualified as DL
import Data.Foldable (Foldable (toList))
import Data.Functor.Identity
import Data.Kind (Type)
import Data.Proxy
import Data.Type.Equality ((:~:) (..))
import Data.TypeLevel.Function
import Data.TypeLevel.Known
import Data.TypeLevel.List
import Data.TypeLevel.ListSpec.Undeferred (BothTypeable)
import Data.TypeLevel.Maybe (FromMaybe)
import Data.TypeLevel.Ord
import Data.TypeLevel.OrdMap (AllOM, EntryC, (:::))
import Data.TypeLevel.OrdMap qualified as OM
import Data.Typeable (typeRep)
import GHC.TypeLits (KnownSymbol, symbolVal)
import Helpers
import Test.Inspection qualified as IT
import Type.Reflection (SomeTypeRep (..))

mapLen :: forall as proxy. (KnownTyList as) => proxy as -> Natural
mapLen _ = natVal @(Length (Map 'Just as)) Proxy

illegalMapLen :: forall as proxy. (KnownTyList as) => proxy as -> Natural
illegalMapLen _ = natVal @(Length ('Nothing ': (Map 'Just as))) Proxy

trivialSort_def ::
  forall (as :: [Nat]) proxy.
  proxy as ->
  Dict (SortedBy Compare2 (MapApply Id1 (SortBy Compare2 as)))
trivialSort_def _ =
  trivialSorted
    (Proxy @Compare2)
    (Proxy @(MapApply Id1 (SortBy Compare2 as)))

trivialSort_def_inst :: Dict (SortedBy Compare2 (MapApply Id1 (SortBy Compare2 '[1, 2, 3])))
trivialSort_def_inst = trivialSort_def (Proxy @'[1, 2, 3])

trivialSort :: IT.Result
trivialSort = $(withNoTypeError 'trivialSort_def_inst)

data NoCompare :: Nat ~> Nat ~> Ordering

nontrivialSort_def ::
  forall (as :: [Nat]) proxy.
  proxy as ->
  Dict (SortedBy NoCompare (MapApply Id1 (SortBy Compare2 as)))
nontrivialSort_def _ =
  trivialSorted
    (Proxy @NoCompare)
    (Proxy @(MapApply Id1 (SortBy Compare2 as)))

nontrivialSort_def_inst :: Dict (SortedBy Compare2 '[1, 2, 3])
nontrivialSort_def_inst = nontrivialSort_def (Proxy @'[1, 2, 3])

nontrivialSort :: IT.Result
nontrivialSort = $(withNoTypeError 'nontrivialSort_def_inst)

nontrivialSort2_def ::
  forall (as :: [Nat]) proxy.
  proxy as ->
  Dict (SortedBy NoCompare (SortBy Compare2 as))
nontrivialSort2_def _ =
  trivialSorted
    (Proxy @NoCompare)
    (Proxy @(SortBy Compare2 as))

nontrivialSort2_def_inst :: Dict (SortedBy Compare2 '[1, 2, 3])
nontrivialSort2_def_inst = nontrivialSort_def (Proxy @'[1, 2, 3])

nontrivialSort2 :: IT.Result
nontrivialSort2 = $(withNoTypeError 'nontrivialSort2_def_inst)

trivialSorted ::
  forall cmp as proxy proxy'.
  (SortedBy cmp as) =>
  proxy cmp ->
  proxy' as ->
  Dict (SortedBy cmp as)
trivialSorted _ _ = Dict

showOrdMapType ::
  forall dic proxy.
  (Known dic, OM.AllOM BothTypeable dic) =>
  proxy dic ->
  [(SomeTypeRep, SomeTypeRep, Natural)]
showOrdMapType _ =
  toList @DL.DList $
    OM.foldMapOrdMap
      @dic
      ( \pk pl pn ->
          DL.singleton
            ( typeRep pk
            , typeRep pl
            , natVal pn
            )
      )

type ShownDict = OM.FromList '[Int ::: 5, Bool ::: 1, Maybe () ::: 0]

shownOrdMap :: [(SomeTypeRep, SomeTypeRep, Natural)]
shownOrdMap = showOrdMapType (Proxy @ShownDict)

sortLabelTypeable ::
  forall xs proxy.
  ( Known xs
  , All KnownSymbol xs
  , OM.SortableList xs
  ) =>
  proxy xs ->
  [(String, Natural)]
sortLabelTypeable _ = OM.withAllConstMap @_ @KnownSymbol @xs $
  toList @DL.DList $
    OM.foldMapOrdMap @(OM.ConstMap xs) $
      \pk _ pn -> DL.singleton (symbolVal pk, natVal pn)

appAssoc ::
  (xs ++ ys) ++ zs :~: xs ++ (ys ++ zs)
appAssoc = Refl

appFalseAssoc ::
  (xs ++ ys) ++ zs :~: xs ++ (zs ++ ys)
appFalseAssoc = Refl

mapApplyDistrib ::
  proxy xs ->
  proxy' ys ->
  proxy'' x ->
  MapApply Just1 (xs ++ (x ': ys))
    :~: (MapApply Just1 xs ++ ('Just x ': MapApply Just1 ys))
mapApplyDistrib _ _ _ = Refl

mapApplyFalseDistrib ::
  proxy xs ->
  proxy' ys ->
  proxy'' x ->
  MapApply Just1 (xs ++ (x ': ys))
    :~: (MapApply Just1 xs ++ ('Nothing ': MapApply Just1 ys))
mapApplyFalseDistrib _ _ _ = Refl

data Just1 :: k ~> Maybe k

type instance Apply Just1 a = 'Just a

showMap ::
  forall x h xs.
  (KnownTyList xs, All Show (Map h xs), Member x xs) =>
  Proxy xs ->
  h x ->
  String
showMap _ = show

myElimFromAll ::
  forall k (c :: k -> Constraint) (xs :: [k]) (x :: k).
  (KnownTyList (xs :: [k]), All c xs, Member x xs) =>
  Proxy c ->
  Proxy x ->
  Proxy xs ->
  Dict (c x)
myElimFromAll _ _ _ = Dict @(c x)

data Right1 :: k ~> Either () k

type instance Apply Right1 a = 'Right a

splitAtApply ::
  Proxy a ->
  Proxy b ->
  Proxy xs ->
  ( Take
      (Index ('Right b) (MapApply Right1 xs))
      (MapApply Just1 xs)
      ++ (a : Drop (Index ('Right b) (MapApply Right1 xs) + 1) (MapApply Just1 xs))
  )
    :~: ( MapApply Just1 (Take (Index ('Right b) (MapApply Right1 xs)) xs)
            ++ (a : MapApply Just1 (Drop (Index ('Right b) (MapApply Right1 xs) + 1) xs))
        )
splitAtApply _ _ _ = Refl

instance Monotone Identity Compare2 Compare2

sortedSort ::
  forall xs.
  (KnownTyList xs) =>
  Dict (SortedBy Compare2 (Map Identity (SortBy Compare2 xs)))
sortedSort = Dict

trivialOM ::
  (OM.AllOM c dic, OM.Member l dic) =>
  Proxy c ->
  Proxy dic ->
  Proxy l ->
  Dict (c l (OM.Lookup' l dic))
trivialOM _ _ _ = Dict

class C (k :: Type) where
  unC :: Proxy k -> String

instance C Int where
  unC _ = "Int"

instance C Bool where
  unC _ = "Bool"

elimAllOMLookup ::
  forall (om :: OM.OrdMap Bool Type) (def :: Type) (x :: Bool).
  (AllOM (EntryC C) (om :: OM.OrdMap Bool Type), C def, Known x) =>
  Proxy x ->
  Proxy om ->
  Proxy def ->
  String
elimAllOMLookup _ _ _ =
  unC $ Proxy @(FromMaybe def (OM.Lookup x om))
