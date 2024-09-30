{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}

module Data.Inhabited (
  Inhabited (..),
  defaultInhabitant,
) where

import Data.Functor.Identity
import Data.Proxy
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as U
import GHC.Generics
import Linear as Lin
import Linear.V

{- | 何でも良いので要素を（\(\perp\)以外に）一つ以上持つ型のクラス。
   @Default@ のように何らかの意味は要求せず、とにかく何かあれば良い。
-}
class Inhabited a where
  inhabitant :: a
  default inhabitant ::
    (Generic a, GInhabited (Rep a)) =>
    a
  inhabitant = defaultInhabitant

defaultInhabitant ::
  (Generic a, GInhabited (Rep a)) =>
  a
defaultInhabitant = to ginhabitant

instance Inhabited Bool where
  inhabitant = True

instance
  (Inhabited a, Inhabited b) =>
  Inhabited (a, b)

instance
  (Inhabited a, Inhabited b, Inhabited c) =>
  Inhabited (a, b, c)

instance
  (Inhabited a, Inhabited b, Inhabited c, Inhabited d) =>
  Inhabited (a, b, c, d)

instance
  (Inhabited a, Inhabited b, Inhabited c, Inhabited d, Inhabited e) =>
  Inhabited (a, b, c, d, e)

instance Inhabited (Maybe a) where
  inhabitant = Nothing

instance Inhabited [a]

instance Inhabited (V.Vector a) where
  inhabitant = V.empty

instance (U.Unbox a) => Inhabited (U.Vector a) where
  inhabitant = U.empty

instance Inhabited Int where
  inhabitant = 0

instance Inhabited Integer where
  inhabitant = 0

instance Inhabited Double where
  inhabitant = 0

instance (Inhabited t) => Inhabited (Identity t) where
  inhabitant = Identity inhabitant

instance Inhabited () where
  inhabitant = ()

deriving anyclass instance (Inhabited a) => Inhabited (V3 a)

deriving anyclass instance (Inhabited a) => Inhabited (V0 a)

deriving anyclass instance (Inhabited a) => Inhabited (Lin.V1 a)

deriving anyclass instance (Inhabited a) => Inhabited (V2 a)

deriving anyclass instance (Inhabited a) => Inhabited (V4 a)

instance (Dim n, Inhabited a) => Inhabited (V n a) where
  inhabitant = V $ V.replicate (reflectDim $ Proxy @n) inhabitant

class GInhabited f where
  ginhabitant :: f ()

instance GInhabited U1 where
  ginhabitant = U1

instance (GInhabited f, GInhabited g) => GInhabited (f :*: g) where
  ginhabitant = ginhabitant :*: ginhabitant

{- | 本当は @f@ と @g@ __どちらか一方__で十分だが、
   Haskell は現状で型クラス制約に OR を許さないので左だけになっている
-}
instance (GInhabited f) => GInhabited (f :+: g) where
  ginhabitant = L1 ginhabitant

instance (GInhabited f) => GInhabited (M1 i c f) where
  ginhabitant = M1 ginhabitant

instance (Inhabited a) => GInhabited (K1 i a) where
  ginhabitant = K1 inhabitant
