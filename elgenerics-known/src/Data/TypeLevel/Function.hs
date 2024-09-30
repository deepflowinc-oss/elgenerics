{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TypeLevel.Function (
  type (~>),
  type (.:),
  type Con,
  Con1,
  BiCon,
  BiCon1,
  Apply,
  Applied (..),
  Id1,
  Const2,
  Const1,
  Dom,
  Cod,
) where

import Control.DeepSeq
import Data.Kind
import GHC.Generics

infixr 0 ~>

type k ~> k' = k -> k' -> Type

type family Apply (n :: k ~> k') (a :: k) :: k'

data (.:) (a :: k' ~> k'') (b :: k ~> k') :: k ~> k''

type instance
  Apply (f .: g) b =
    Apply f (Apply g b)

data Con (c :: k -> k') :: k ~> k'

type instance Apply (Con c) a = c a

data Con1 :: (k -> k') ~> k ~> k'

type instance Apply Con1 f = Con f

data BiCon (c :: k -> k' -> k'') :: k ~> k' ~> k''

type instance Apply (BiCon f) x = BiCon1 f x

data BiCon1 (c :: k -> k' -> k'') (x :: k) :: k' ~> k''

type instance Apply (BiCon1 f x) y = f x y

newtype Applied n a = Applied {runApplied :: Apply n a}
  deriving (Generic)

deriving newtype instance (Show (Apply n a)) => Show (Applied n a)

deriving newtype instance (Eq (Apply n a)) => Eq (Applied n a)

deriving newtype instance (Ord (Apply n a)) => Ord (Applied n a)

deriving newtype instance (NFData (Apply n a)) => NFData (Applied n a)

data Id1 :: k ~> k

type instance Apply Id1 a = a

type family Dom p where
  Dom (a ~> b) = a

-- Dom (a -> b) = a
type family Cod p where
  Cod (a ~> b) = b

-- Cod (a -> b) = b

data Const2 :: a ~> b ~> a

data Const1 (x :: a) :: b ~> a

type instance Apply Const2 a = Const1 a

type instance Apply (Const1 a) _ = a
