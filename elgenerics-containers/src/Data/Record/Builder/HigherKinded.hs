{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RoleAnnotations #-}

{- | Top-down style extensible record builder.

 The construction is top-down in a sense that
 the resulting record fields are determined before the
 actual construction (i.e. when the user calls 'empty').
 If the resulting fields are not determined a priori, use the bottom-up
 builder provided in module "Data.Record.Builder.Highedrinded.BottomUp".
-}
module Data.Record.Builder.HigherKinded (
  RecordBuilder,
  Building,
  Building' (),
  (&+),
  (&+:),
  singleton,
  singleton',
  build,
  empty,
) where

import Control.Monad.ST.Strict
import Data.HList.Internal qualified as HL
import Data.Record.HigherKinded qualified as Rec
import Data.Record.HigherKinded.Internal qualified as Rec
import Data.TypeLevel.OrdMap qualified as OM
import Data.Vector qualified as V
import Data.Vector.Mutable qualified as MV
import GHC.Exts (Any, proxy#)
import GHC.TypeNats
import Unsafe.Coerce

{- | A Record builder that is ready for building.

  c.f. 'Building' and 'Building''.
-}
type RecordBuilder = Building' OM.Empty

{- | A record buidler with all the fields uninitialised.

   c.f. 'empty'.
-}
type Building h xs = Building' xs h xs

type role Building' nominal representational nominal

-- | A generic record-builder type.

-- @'Building'' remains h allFields@ is a builder for a record with type
-- @'Record' h allFields@ with uninitialised fields @remains@.
--
-- Fields can be added with @('&+')@ and @('&+:')@,
-- and you can build a concrete record with 'build' if @remains@ is 'OM.Empty'.
--
-- __N.B.__ If the resuliting fields are NOT determined a priori,
-- it is much faster and safer to use the bottom-up builder
-- provided in "Data.Record.Builder.HigherKinded.BottomUp".
newtype Building' (remains :: OM.OrdMap k v) h (allFields :: OM.OrdMap k v)
  = RecordBuilder (forall s. MV.MVector s Any -> ST s ())

infixl 1 &+, &+:

{- | /O(1)/ Adds field to a record builder.

 See also: @('&+:')@.
-}
(&+) ::
  forall h fields l remain a.
  (Rec.HasLabel l fields, Rec.HasLabel l remain, OM.Lookup' l fields ~ a) =>
  Building' remain h fields ->
  l Rec.:= h l a ->
  Building' (OM.Delete l remain) h fields
{-# INLINE (&+) #-}
(&+) = \b (_ Rec.:= hla) -> b &+: hla

{- | /O(1)/ Adds field to a record builder.

 See also: @('&+')@.
-}
(&+:) ::
  forall h fields l remain a.
  (Rec.HasLabel l fields, Rec.HasLabel l remain, OM.Lookup' l fields ~ a) =>
  Building' remain h fields ->
  h l a ->
  Building' (OM.Delete l remain) h fields
{-# INLINE (&+:) #-}
(&+:) = \(RecordBuilder cur) (hla :: h l a) ->
  let n = fromIntegral $ natVal' @(OM.Index l fields) proxy#
   in RecordBuilder $
        \mv -> cur mv >> MV.unsafeWrite mv n (unsafeCoerce hla :: Any)

-- | /O(1)/ Record-builder with all fields uninitialised.
empty :: forall h fields. Building h fields
empty = RecordBuilder $ const $ pure ()

-- | /O(1)/ Record-builder with a single field initialised.
singleton ::
  forall l a h fields.
  (Rec.HasLabel l fields, OM.Lookup' l fields ~ a) =>
  l Rec.:= h l a ->
  Building' (OM.Delete l fields) h fields
{-# INLINE singleton #-}
singleton = \(_ Rec.:= hla) -> singleton' hla

-- | /O(1)/ Record-builder with a single field initialised.
singleton' ::
  forall l a h fields.
  (Rec.HasLabel l fields, OM.Lookup' l fields ~ a) =>
  h l a ->
  Building' (OM.Delete l fields) h fields
{-# INLINE singleton' #-}
singleton' =
  let n = fromIntegral $ natVal' @(OM.Index l fields) proxy#
   in \hla -> RecordBuilder $ \mv ->
        MV.unsafeWrite mv n $ unsafeCoerce hla

-- | /O(n)/ Turns fully-initialised builder into a concrete record.
build ::
  forall h fields.
  (KnownNat (OM.Size fields)) =>
  RecordBuilder h fields ->
  Rec.Record h fields
build (RecordBuilder cmd) = Rec.Record $
  HL.HL $
    V.create $ do
      mv <- MV.new $ fromIntegral $ natVal' @(OM.Size fields) proxy#
      cmd mv
      pure mv
