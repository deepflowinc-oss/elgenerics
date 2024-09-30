{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.TypeLevel.Monoid (
  PSemigroup (..),
  PMonoid (..),
  type (<>),
  Mappend1,
  Mappend2,
) where

import Data.TypeLevel.Function
import Data.TypeLevel.List.Core
import GHC.TypeLits

class PSemigroup a where
  type Mappend (l :: a) (b :: a) :: a

data Mappend2 :: k ~> k ~> k

data Mappend1 (a :: k) :: k ~> k

type instance Apply Mappend2 a = Mappend1 a

type instance Apply (Mappend1 a) b = Mappend a b

type a <> b = Mappend a b

infixr 6 <>

class (PSemigroup a) => PMonoid a where
  type Mempty :: a

instance PSemigroup [k] where
  type Mappend l r = l ++ r

instance PMonoid [k] where
  type Mempty = '[]

instance PSemigroup Symbol where
  type Mappend l r = AppendSymbol l r

instance PMonoid Symbol where
  type Mempty = ""

instance PSemigroup ErrorMessage where
  type Mappend l r = l ':<>: r

instance PMonoid ErrorMessage where
  type Mempty = 'Text ""
