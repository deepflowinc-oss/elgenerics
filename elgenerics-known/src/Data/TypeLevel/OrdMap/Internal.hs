{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

module Data.TypeLevel.OrdMap.Internal where

import Data.Type.Equality
import Data.TypeLevel.Known
import Data.TypeLevel.Ord
import GHC.Generics
import GHC.TypeLits
import Type.Reflection
import Unsafe.Coerce

data Color = R | B deriving (Read, Show, Eq, Ord, Typeable)

deriveAllKnown True ''Color

type SizeT = Nat

newtype RankT = MkRankT Nat

data SRankT (n :: RankT) where
  SMkRankT :: SNat n -> SRankT (MkRankT n)

type family CmpRankT2 a b where
  CmpRankT2 ('MkRankT l) ('MkRankT r) = Compare l r

instance POrd RankT where
  type Compare a b = CmpRankT2 a b

instance SOrd RankT where
  sCompare (SMkRankT l) (SMkRankT r) = sCompare l r

type instance Sing = SRankT

deriving instance Show (SRankT n)

type MkRankT = 'MkRankT

deriveSingTypeable ''RankT

instance (KnownNat n) => Known (MkRankT n) where
  sKnownVal' =
    case unsafeCoerce (Equal @0 @0) :: Equality n n of
      Equal -> SMkRankT $ sKnownVal' @n

deriving via WrapSing instance TestEquality SRankT

instance STestEquality RankT where
  sTestEquality = \(SMkRankT l) (SMkRankT r) ->
    case sTestEquality l r of
      Equal -> Equal
      NonEqual -> unsafeCoerce $ NonEqual @0 @1

-- | （型レベル）平衡二分探索木。赤黒木として実装している。
data OrdMap k v = Leaf | Branch Color SizeT RankT (OrdMap k v) k v (OrdMap k v)
  deriving (Typeable, Generic)

defineSingletons ''OrdMap
deriveKnown ''OrdMap
deriveSTestEquality ''OrdMap
deriveSingTypeable ''OrdMap

newtype OMMembership k dic = OMMembership Natural
