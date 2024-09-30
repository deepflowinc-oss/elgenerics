{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -dcore-lint -fprint-explicit-foralls -fprint-explicit-kinds #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}

module Main where

import Data.Constraint.Operators (MaybeC)
import Data.Kind (Constraint, Type)
import Data.Proxy
import Data.TypeLevel.Known (Known)
import Data.TypeLevel.Maybe (FromMaybe)
import Data.TypeLevel.OrdMap
import Type.Reflection (Typeable)

data Dict c where
  Dict :: (c) => Dict c

class C (k :: Type) (v :: Type)

trivialOM ::
  (AllOM (c :: k -> Type -> Constraint) dic, Member l (dic :: OrdMap k Type)) =>
  Proxy c ->
  Proxy dic ->
  Proxy l ->
  Dict (c l (Lookup' l dic))
trivialOM _ _ _ = Dict

elimMaybC ::
  (Known may, MaybeC Typeable may) =>
  Proxy may ->
  Dict (Typeable (FromMaybe Int may))
elimMaybC _ = Dict

class D (k :: Type) where
  unC :: Proxy k -> String

instance D Int where
  unC _ = "Int"

instance D Bool where
  unC _ = "Bool"

elimAllOMLookup ::
  forall (om :: OrdMap Bool Type) (def :: Type) (x :: Bool).
  (AllOM (EntryC D) (om :: OrdMap Bool Type), D def, Known x) =>
  Proxy x ->
  Proxy om ->
  Proxy def ->
  String
elimAllOMLookup _ _ _ =
  unC $ Proxy @(FromMaybe @Type def (Lookup @Bool @Type x om))

main :: IO ()
main = return ()
