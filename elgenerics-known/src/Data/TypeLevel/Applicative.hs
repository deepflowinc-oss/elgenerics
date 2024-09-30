{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TypeLevel.Applicative (
  PFunctor (..),
  PApplicative (..),
  PAlternative (..),
  FMap1,
  FMap2,
  sFMapMaybe,
  sFMapMaybe',
) where

import Data.TypeLevel.Function
import Data.TypeLevel.Known
import Data.TypeLevel.List qualified as L
import Data.TypeLevel.Maybe qualified as M
import GHC.Exts (Proxy#)

data FMap1 (f :: k ~> k') :: h k ~> h k'

type instance Apply (FMap1 f) fx = f <$> fx

data FMap2 :: (k ~> k') ~> h k ~> h k'

type instance Apply FMap2 f = FMap1 f

class PFunctor f where
  type (<$>) (fun :: a ~> b) (fa :: f a) :: f b

class (PFunctor f) => PApplicative f where
  type Pure (x :: a) :: f a
  type (<*>) (fun :: f (a ~> b)) (fa :: f a) :: f b

class (PApplicative f) => PAlternative f where
  type (<|>) (l :: f a) (r :: f a) :: f a
  type Empty :: f a

type MapMaybe :: forall a b. (a ~> b) -> Maybe a -> Maybe b
type family MapMaybe (f :: a ~> b) (ma :: Maybe a) :: Maybe b where
  MapMaybe f 'Nothing = 'Nothing
  MapMaybe f ('Just a) = 'Just (Apply f a)

type family AppMaybe (mf :: Maybe (a ~> b)) (ma :: Maybe a) :: Maybe b where
  AppMaybe ('Just f) ('Just a) = 'Just (Apply f a)
  AppMaybe _ _ = 'Nothing

instance PFunctor Maybe where
  type (<$>) f a = MapMaybe f a

instance PApplicative Maybe where
  type Pure a = 'Just a
  type (<*>) f a = AppMaybe f a

instance PAlternative Maybe where
  type Empty = 'Nothing
  type (<|>) fa fb = (M.<|>) fa fb

instance PFunctor [] where
  type (<$>) f a = L.MapApply f a

type family AppList (fs :: [a ~> b]) (as :: [a]) :: [b] where
  AppList '[] _ = '[]
  AppList (f ': fs) as = (L.++) (L.MapApply f as) (AppList fs as)

instance PApplicative [] where
  type Pure a = '[a]
  type (<*>) fs as = AppList fs as

instance PAlternative [] where
  type Empty = '[]
  type (<|>) as bs = (L.++) as bs

sFMapMaybe :: (SApply f) => Proxy# (f :: k ~> k') -> SMaybe (a :: Maybe k) -> SMaybe (f <$> a)
sFMapMaybe _ SNothing = SNothing
sFMapMaybe sf (SJust a) = SJust $ sApply sf a

sFMapMaybe' ::
  forall k k' (f :: k ~> k') (a :: Maybe k).
  (SApply f) =>
  Proxy# f ->
  Sing a ->
  Sing (MapMaybe f a)
sFMapMaybe' = sFMapMaybe
