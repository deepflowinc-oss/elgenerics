{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}

module Data.Record.Failures where

import Control.Lens
import Data.Record qualified as Simple
import Data.Record.Cases
import Data.Record.HigherKinded qualified as HK
import Data.Tagged (Tagged (..))

typeMismatch :: Maybe Bool
typeMismatch = unTagged <$> HK.projField @"a" ascSimpleRecord1

mismatchUpdate :: Char -> Simple.Record AscFields1 -> Simple.Record AscFields1
mismatchUpdate ch = HK.recFieldTraversal @"a" .~ Tagged ch

unmergeable :: Simple.Record AscFields1
unmergeable =
  Simple.emptyRec
    Simple.&+ #a
    Simple.:= (12 :: Int)
    Simple.&+ #b
    Simple.:= True
    Simple.&+ #c
    Simple.:= ()
    Simple.&+ #a
    Simple.:= (42 :: Int)
