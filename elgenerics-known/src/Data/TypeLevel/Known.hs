{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.TypeLevel.Known (
  module Data.TypeLevel.Known.Core,
  module Data.TypeLevel.Known.TH,
  (%===),
  triviallyEqual,
  SMaybe (..),
  KnownMaybe,
  maybeVal,
  sMaybeVal,
  toSomeMaybe,
  SThese (..),
  KnownThese,
  theseVal,
  sTheseVal,
  toSomeThese,
  This,
  That,
  MkThese,
  SEither (..),
  KnownEither,
  Left,
  Right,
  eitherVal,
  sEitherVal,
  toSomeEither,
  SBool (..),
  KnownBool,
  boolVal,
  sBoolVal,
  toSomeBool,
  SOrdering (..),
  orderingVal,
  sOrderingVal,
  type EQ,
  type GT,
  type LT,
  toSomeOrdering,
) where

import Data.Constraint.Deferrable
import Data.Proxy
import Data.These
import Data.Type.Equality
import Data.TypeLevel.Known.Core
import Data.TypeLevel.Known.TH
import Unsafe.Coerce (unsafeCoerce)

deriveAllKnown True ''Maybe
deriveAllKnown True ''Either
deriveAllKnown True ''These

type MkThese = Data.TypeLevel.Known.These

triviallyEqual ::
  forall x r. (((x == x) ~ 'True) => r) -> r
triviallyEqual f =
  case unsafeCoerce (Refl @0) :: (x == x) :~: 'True of
    Refl -> f

_suppress_Maybe :: Proxy '(Just, Nothing)
_suppress_Maybe = Proxy

deriveAllKnown True ''Bool

_suppress_Bool :: Proxy '(True, False)
_suppress_Bool = Proxy

deriveAllKnown True ''Ordering

(%===) :: (STestEquality k) => Sing (a :: k) -> Sing b -> SBool (a === b)
a %=== b =
  case sTestEquality a b of
    Equal -> STrue
    NonEqual -> SFalse

infix 4 %===
