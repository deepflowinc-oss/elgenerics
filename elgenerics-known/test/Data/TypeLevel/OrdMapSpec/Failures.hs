{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}

module Data.TypeLevel.OrdMapSpec.Failures where

import Data.Constraint (Dict (Dict))
import Data.TypeLevel.Known
import Data.TypeLevel.OrdMap
import Data.TypeLevel.OrdMap.Internal (MkRankT)
import Helpers (withNoTypeError)
import Test.Inspection

unsortedValidRBTree_def ::
  Dict (ValidRBTree (UnsafeFromAscList '[3 ::: Int, 42 ::: Bool, 5 ::: ()]))
unsortedValidRBTree_def = Dict

unsortedValidRBTree :: Result
unsortedValidRBTree =
  $(withNoTypeError 'unsortedValidRBTree_def)

unsortedFromAscList_def ::
  Sing (FromAscList '[3 ::: Int, 42 ::: Bool, 5 ::: ()])
unsortedFromAscList_def = sKnownVal'

unsortedFromAscList :: Result
unsortedFromAscList =
  $(withNoTypeError 'unsortedFromAscList_def)

redRedInvalid_def ::
  Dict (ValidRBTree (Branch R 2 (MkRankT 1) (Branch R 1 (MkRankT 1) Leaf 0 Int Leaf) 1 Bool Leaf))
redRedInvalid_def = Dict

redRedInvalid :: Result
redRedInvalid = $(withNoTypeError 'redRedInvalid_def)
