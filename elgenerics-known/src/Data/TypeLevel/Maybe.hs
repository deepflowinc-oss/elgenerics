{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeFamilies #-}

module Data.TypeLevel.Maybe (
  type FromJust,
  type FromMaybe,
  type FromNothing,
  type MaybeApply,
  MaybeApply3,
  MaybeApply2,
  MaybeApply1,
  type ElimMaybe,
  ElimMaybe3,
  ElimMaybe2,
  ElimMaybe1,
  type (<|>),
  type (<$>),
  type Just,
  type Nothing,
  JoinMaybe,
  DeconsMaybe (..),
  PMaybe (..),
  withDeconsMaybe,
) where

import Data.Constraint.Deferrable
import Data.TypeLevel.Function
import Data.TypeLevel.Known
import GHC.Base (proxy#)
import GHC.Exts (Proxy#)
import GHC.TypeLits

type family (<$>) (f :: a -> b) (m :: Maybe a) :: Maybe b where
  _ <$> 'Nothing = 'Nothing
  f <$> 'Just a = 'Just (f a)

type family (<|>) (l :: Maybe a) (r :: Maybe a) :: Maybe a where
  'Nothing <|> b = b
  'Just a <|> _ = 'Just a

type family FromJust msg (ma :: Maybe a) :: a where
  FromJust _ ('Just a) = a
  FromJust m _ = TypeError m

type Just = 'Just

type Nothing = 'Nothing

type family FromNothing msg (v :: b) (ma :: Maybe a) :: b where
  FromNothing _ v 'Nothing = v
  FromNothing m _ ('Just _) = TypeError m

type family FromMaybe (x :: a) (ma :: Maybe a) :: a where
  FromMaybe x 'Nothing = x
  FromMaybe _ ('Just a) = a

type family MaybeApply (z :: b) (f :: a ~> b) (ma :: Maybe a) :: b where
  MaybeApply z _ 'Nothing = z
  MaybeApply _ f ('Just a) = Apply f a

data MaybeApply3 :: b ~> (a ~> b) ~> Maybe a ~> b

data MaybeApply2 (z :: b) :: (a ~> b) ~> Maybe a ~> b

data MaybeApply1 (z :: b) (f :: a ~> b) :: Maybe a ~> b

type instance Apply MaybeApply3 z = MaybeApply2 z

type instance Apply (MaybeApply2 z) f = MaybeApply1 z f

type instance Apply (MaybeApply1 z f) ma = MaybeApply z f ma

type family ElimMaybe (z :: b) (f :: a -> b) (ma :: Maybe a) :: b where
  ElimMaybe z _ 'Nothing = z
  ElimMaybe _ f ('Just a) = f a

data ElimMaybe3 :: b ~> (a -> b) ~> Maybe a ~> b

data ElimMaybe2 (z :: b) :: (a -> b) ~> Maybe a ~> b

data ElimMaybe1 (z :: b) (f :: a -> b) :: Maybe a ~> b

type instance Apply ElimMaybe3 z = ElimMaybe2 z

type instance Apply (ElimMaybe2 z) f = ElimMaybe1 z f

type instance Apply (ElimMaybe1 z f) ma = ElimMaybe z f ma

type family JoinMaybe mma where
  JoinMaybe 'Nothing = 'Nothing
  JoinMaybe ('Just ma) = ma

data PMaybe (m :: Maybe a) where
  PNothing :: PMaybe 'Nothing
  PJust :: Proxy# x -> PMaybe ('Just x)

class DeconsMaybe m where
  sDeconsMaybe' :: PMaybe m

instance DeconsMaybe ('Just x) where
  sDeconsMaybe' = PJust proxy#

instance DeconsMaybe 'Nothing where
  sDeconsMaybe' = PNothing

instance Deferrable (DeconsMaybe ('Just x)) where
  deferEither _ = \act -> Right act
  {-# INLINE deferEither #-}

instance Deferrable (DeconsMaybe 'Nothing) where
  deferEither _ = \act -> Right act
  {-# INLINE deferEither #-}

withDeconsMaybe ::
  SMaybe m -> ((DeconsMaybe m) => r) -> r
withDeconsMaybe SNothing {} act = act
withDeconsMaybe SJust {} act = act
