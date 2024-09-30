{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}

module Data.HList.HigherKinded.Builder (
  Builder (),
  empty,
  (%:-),
  (-:%),
  (%++),
  build,
) where

import Data.Coerce (coerce)
import Data.HList.Internal (HList (..))
import Data.Kind (Type)
import Data.TypeLevel.List (type (++))
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)
import VectorBuilder.Builder qualified as VB
import VectorBuilder.Vector qualified as VB

type Builder :: forall {k}. (k -> Type) -> [k] -> Type
newtype Builder h xs = Builder {runBuilder :: VB.Builder Any}

infixr 5 %:-, %++

(%:-) :: h x -> Builder h xs -> Builder h (x ': xs)
hl %:- Builder anys = Builder $ VB.singleton (unsafeCoerce hl) <> anys

infixl 5 -:%

(-:%) :: Builder h xs -> h x -> Builder h (xs ++ '[x])
Builder anys -:% hl = Builder $ anys <> VB.singleton (unsafeCoerce hl)

(%++) :: Builder h xs -> Builder h ys -> Builder h (xs ++ ys)
(%++) = coerce $ (<>) @(VB.Builder Any)

build :: Builder h xs -> HList h xs
build = HL . VB.build . runBuilder

empty :: Builder h xs
empty = Builder mempty
