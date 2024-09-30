{-# LANGUAGE DataKinds #-}

module Data.HList.Internal (HList (..)) where

import Data.Kind
import Data.Vector (Vector)
import GHC.Exts

newtype HList (h :: k -> Type) (as :: [k]) = HL (Vector Any)
