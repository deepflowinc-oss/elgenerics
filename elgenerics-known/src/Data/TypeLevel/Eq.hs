{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TypeLevel.Eq where

import Data.Type.Equality qualified as GHC
import GHC.TypeLits

class PEq k where
  type (==) (a :: k) (b :: k) :: Bool

type EqNat l r = OrderingToEq (CmpNat l r)

type family OrderingToEq cmp where
  OrderingToEq 'LT = 'False
  OrderingToEq 'EQ = 'True
  OrderingToEq 'GT = 'False

instance PEq Natural where
  type l == r = l GHC.== r

instance PEq Symbol where
  type l == r = l GHC.== r
