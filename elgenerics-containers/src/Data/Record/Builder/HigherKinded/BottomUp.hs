{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RoleAnnotations #-}

{- | Bottom-up style extensible record builder.

 The construction is bottom-up in a sense that
 the resulting record fields are determined when the
 'build' function is called; if the resulting fields
 are determined before the construction, use a top-down
 builder provided in module "Data.Record.Builder.Highedrinded".
-}
module Data.Record.Builder.HigherKinded.BottomUp (
  RecordBuilder,
  build,
  buildNoDupe,
  empty,
  (&+),
  (&+:),
  (&<>),
) where

import Data.HList.Internal qualified as HL
import Data.Kind
import Data.Record.HigherKinded qualified as Rec
import Data.Record.HigherKinded.Internal qualified as Rec
import Data.TypeLevel.List (Length, type (++))
import Data.TypeLevel.OrdMap qualified as OM
import Data.Vector qualified as V
import GHC.Exts (Any)
import Unsafe.Coerce
import VectorBuilder.Builder qualified as VB
import VectorBuilder.Vector qualified as VB

-- | A generic bottom-up record-builder type.

-- @'Building'' h allFields@ is a builder for a record with type
-- @'Record' h ('OM.FromList' allFields)@.
--
-- Fields can be added with @('&+')@ and @('&+:')@,
-- and a concrete record can be built by 'build'.
--
-- __N.B.__ If the resuliting fields are determined a priori,
-- it is much faster and safer to use the top-down builder
-- provided in "Data.Record.Builder.HigherKinded".
data RecordBuilder (h :: k -> v -> Type) (fields :: [OM.Field k v])
  = RecordBuilder (VB.Builder Any)

{- | /O(n)/ Build a concrete record.

 See also: 'buildNoDupe'.
-}
build ::
  forall h fields.
  (OM.SortableLabels fields) =>
  RecordBuilder h fields ->
  Rec.Record h (OM.FromList fields)
build (RecordBuilder vb) =
  let vec0 = VB.build vb
      perms = V.convert $ OM.sortPermutation @fields
   in Rec.Record $
        HL.HL $
          V.unsafeBackpermute vec0 perms

{- | /O(n)/ Build a concrete record, but checks there is no duplicated labels.

 See also: 'build'.
-}
buildNoDupe ::
  forall h fields.
  ( OM.SortableLabels fields
  , OM.Size (OM.FromList fields) ~ Length fields
  ) =>
  RecordBuilder h fields ->
  Rec.Record h (OM.FromList fields)
buildNoDupe = build

-- | /O(1)/ Record-builder with no fields.
empty :: RecordBuilder h '[]
empty = RecordBuilder VB.empty

{- | /O(1)/ Adds field to a record builder.

 See also: @('&+:')@.
-}
(&+) ::
  forall h fields l a.
  RecordBuilder h fields ->
  l Rec.:= h l a ->
  RecordBuilder h ((l OM.::: a) ': fields)
{-# INLINE (&+) #-}
(&+) = \b (_ Rec.:= hla) -> b &+: hla

{- | /O(1)/ Adds field to a record builder.

 See also: @('&+')@.
-}
(&+:) ::
  forall h fields l a.
  RecordBuilder h fields ->
  h l a ->
  RecordBuilder h ((l OM.::: a) ': fields)
{-# INLINE (&+:) #-}
(&+:) = \(RecordBuilder cur) (hla :: h l a) ->
  RecordBuilder $ VB.singleton (unsafeCoerce hla :: Any) <> cur

infixl 1 &+, &+:

(&<>) ::
  forall h fields fields'.
  RecordBuilder h fields ->
  RecordBuilder h fields' ->
  RecordBuilder h (fields ++ fields')
(&<>) = \(RecordBuilder cur) (RecordBuilder rest) ->
  RecordBuilder $ cur <> rest
