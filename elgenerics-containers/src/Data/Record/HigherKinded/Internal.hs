{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

#if __GLASGOW_HASKELL__ >= 810
#endif

module Data.Record.HigherKinded.Internal (module Data.Record.HigherKinded.Internal) where

import Control.DeepSeq
import Data.HList.HigherKinded
import Data.Kind
import Data.TypeLevel.OrdMap as OrdMap
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Deriving
import GHC.Generics
import Type.Reflection

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 810
type Uncurried
  :: forall k k'. (k -> k' -> Type) -> Field k k' -> Type
#endif

newtype Uncurried (h :: k -> k' -> Type) fld = Uncurried {curried :: h (Label fld) (Entry fld)}
  deriving (Generic, Typeable)

deriving newtype instance
  (NFData (h l a)) => NFData (Uncurried h (l ::: a))

deriving newtype instance
  (Eq (h l a)) => Eq (Uncurried h (l ::: a))

deriving newtype instance
  (Ord (h l a)) => Ord (Uncurried h (l ::: a))

deriving newtype instance
  (Show (h l a)) => Show (Uncurried h (l ::: a))

derivingUnbox
  "Uncurried"
  [t|forall h l a. (U.Unbox (h l a)) => Uncurried h (l ::: a) -> h l a|]
  [|curried|]
  [|Uncurried|]

newtype OnLabel (h :: k -> Type) (l :: k) (a :: k') = OnLabel {runOnLabel :: h l}
  deriving (Read, Show, Eq, Ord, Generic, Typeable)
  deriving newtype (NFData)

derivingUnbox
  "OnLabel"
  [t|forall h l a. (U.Unbox (h l)) => OnLabel h l a -> h l|]
  [|runOnLabel|]
  [|OnLabel|]

newtype OnEntry (h :: k' -> Type) (l :: k) (a :: k') = OnEntry {runOnEntry :: h a}
  deriving (Read, Show, Eq, Ord, Generic, Typeable)
  deriving newtype (NFData)

derivingUnbox
  "OnEntry"
  [t|forall h l a. (U.Unbox (h a)) => OnEntry h l a -> h a|]
  [|runOnEntry|]
  [|OnEntry|]

newtype Record h recs = Record (HList (Uncurried h) (ToList recs))

type HasLabel (l :: k) (xs :: OrdMap k v) = OrdMap.Member l xs
