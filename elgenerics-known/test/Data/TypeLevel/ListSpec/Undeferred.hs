{-# LANGUAGE DataKinds #-}

module Data.TypeLevel.ListSpec.Undeferred where

import Data.DList qualified as DL
import Data.Proxy (Proxy)
import Data.TypeLevel.List
import Data.Typeable (typeRep)
import Type.Reflection (SomeTypeRep, Typeable)

class (Typeable l, Typeable r) => BothTypeable l r

instance (Typeable l, Typeable r) => BothTypeable l r

typeRepList ::
  (All Typeable xs, KnownTyList xs) =>
  Proxy xs ->
  [SomeTypeRep]
typeRepList = DL.toList . foldMapTyListC @Typeable (DL.singleton . typeRep)
