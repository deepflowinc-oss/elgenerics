{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deferrable.Solver #-}

module Data.Constraint.Deferrable.SolverSpec.Cases where

import Control.DeepSeq (NFData)
import Data.Constraint.Deferrable (
  Deferrable,
  deferEither_,
 )
import Data.Constraint.Deferrable.SolverSpec.Undeferreds
import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat, Nat, natVal)
import Numeric.Natural (Natural)

data Void
  deriving (Show, Generic)
  deriving anyclass (NFData)

class Inaccessible a where
  inaccessible :: a -> Void

deferInaccessible ::
  Either String Void
deferInaccessible =
  deferEither_ @(Inaccessible Int) $ inaccessible (42 :: Int)

class Ok (n :: Nat) where
  ok :: proxy n -> Int

instance Ok 42 where
  ok = const 42

deferOk ::
  forall n proxy.
  (Deferrable (Ok n)) =>
  proxy n ->
  Either String Int
deferOk pn = deferEither_ @(Ok n) $ ok pn

undeferrableOk :: Either String Int
undeferrableOk = deferOk (Proxy @0)

deferrableOk :: Either String Int
deferrableOk = deferOk (Proxy @42)

theUnit :: Either String ()
theUnit = deferEither_ @(KnownNat 42) ()

deferKnownNatN :: forall n proxy. (KnownNat n) => proxy n -> Either String Natural
deferKnownNatN pxy = deferEither_ @(KnownNat n) $ natVal pxy

deferDummy :: forall n r. (KnownNat n) => ((Foo Dummy n) => r) -> Either String r
deferDummy = deferEither_ @(Foo Dummy n)
