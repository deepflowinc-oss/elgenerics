{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Non-HKD like record, dependent only on the second field
module Data.Record (
  Record,
  type (:::),
  type (<:),
  HasLabel,
  EntryAt,
  FieldAt,
  Entries,
  Extendible,
  Field (..),
  FieldLabel (..),
  ShowableRecord,
  Shown (..),
  Labels,
  (:=) (..),
  extends,
  EntryC,
  LabelC,
  emptyRec,
  recField,
  (&.),
  (&+),
  (&%~),
  (&|~),
  (&-),
  traverseRec,
  viewField,
  viewField',
  field,
  IsRecord (..),
  SortFields,
  ToLabel,
) where

import Control.Lens (Lens', coerced)
import Data.Coerce
import Data.Proxy
import Data.Record.HigherKinded (
  Entries,
  EntryAt,
  EntryC,
  Extendible,
  Field (..),
  FieldAt,
  FieldLabel (..),
  HasLabel,
  IsRecord (..),
  LabelC,
  Labels,
  ShowableRecord,
  Shown,
  SortFields,
  ToLabel,
  field,
  (:::),
  (:=) (..),
  type (<:),
 )
import Data.Record.HigherKinded qualified as HK
import Data.Tagged
import Data.TypeLevel.OrdMap (Delete, Lookup')
import Data.TypeLevel.OrdMap qualified as OM
import GHC.Records
import GHC.TypeLits

type Record recs = HK.Record HK.STagged recs

extends ::
  forall l x xs.
  (Extendible (l ::: x) xs) =>
  l := x ->
  Record xs ->
  Record ((l ::: x) <: xs)
extends = coerce $ HK.extends @l @HK.STagged @x @xs

(&+) ::
  (Extendible (l ::: x) xs) =>
  Record xs ->
  l := x ->
  Record ((l ::: x) <: xs)
(&+) = flip extends

infixl 1 &+

emptyRec :: Record OM.Empty
emptyRec = HK.emptyRec

(&.) ::
  forall l xs.
  (HasLabel l xs) =>
  Record xs ->
  l := Lookup' l xs ->
  Record xs
(&.) = coerce $ (HK.&.) @l @xs @HK.STagged

infixl 1 &.

viewField ::
  forall l recs.
  (HasLabel l recs) =>
  FieldLabel l ->
  Record recs ->
  OM.Lookup' l recs
viewField = const $ viewField' @l

viewField' ::
  forall l recs.
  (HasLabel l recs) =>
  Record recs ->
  OM.Lookup' l recs
viewField' = unTagged . HK.viewField' @l

instance
  {-# OVERLAPPING #-}
  ( HasLabel (l :: Symbol) recs
  , 'Just x ~ OM.Lookup l recs
  ) =>
  HasField l (Record recs) x
  where
  getField = viewField (FieldLabel @_ @l)

recField ::
  forall xs l.
  (HasLabel l xs) =>
  FieldLabel l ->
  Lens'
    (Record xs)
    (Lookup' l xs)
recField l =
  HK.recField l
    . coerced
      @(Tagged l (Lookup' l xs))
      @(Tagged l (Lookup' l xs))
{-# INLINE recField #-}

(&%~) ::
  forall l xs a.
  (HasLabel l xs) =>
  Record xs ->
  l HK.:= (Lookup' l xs -> a) ->
  Record ((l ::: a) <: xs)
(&%~) = coerce $ (HK.&%~) @l @xs @HK.STagged @a

(&|~) ::
  forall l xs a.
  (HasLabel l xs) =>
  Record xs ->
  l := a ->
  Record ((l ::: a) <: xs)
(&|~) = coerce $ (HK.&|~) @l @xs @a @HK.STagged

(&-) ::
  forall l xs.
  (HasLabel l xs) =>
  Record xs ->
  FieldLabel l ->
  Record (Delete l xs)
(&-) = coerce $ (HK.&-) @l @xs @HK.STagged

traverseRec ::
  forall f as.
  (Applicative f) =>
  ( forall l.
    (HasLabel l as) =>
    Proxy l ->
    Lookup' l as ->
    f (Lookup' l as)
  ) ->
  Record as ->
  f (Record as)
traverseRec = \f -> HK.traverseRec (\p _ _ -> fmap Tagged . f p . unTagged)
