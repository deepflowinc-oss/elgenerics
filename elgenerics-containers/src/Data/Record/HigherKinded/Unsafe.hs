{-# LANGUAGE DataKinds #-}

module Data.Record.HigherKinded.Unsafe (
  unsafeMkRecord,
  unsafeDeconsRecord,
) where

import Data.HList.Internal
import Data.Proxy
import Data.Record.HigherKinded
import Data.Record.HigherKinded.Internal
import Data.TypeLevel.List
import Data.TypeLevel.Ord
import Data.Vector qualified as V
import GHC.Exts

unsafeMkRecord ::
  forall h xs pxy.
  (Sortable Compare2 xs) =>
  pxy xs ->
  V.Vector Any ->
  Record h (FromList (SortFields xs))
unsafeMkRecord _ v =
  let idxs = natListVal @(MapApply Fst1 (SortByWithIndex Compare2 xs)) Proxy
   in Record $ HL $ V.unsafeBackpermute v $ V.fromList $ map fromIntegral idxs

unsafeDeconsRecord ::
  Record h xs -> V.Vector Any
unsafeDeconsRecord (Record (HL hl)) = hl
