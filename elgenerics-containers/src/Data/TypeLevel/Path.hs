{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TypeLevel.Path (
  Path' (..),
  Path,
  PathSpec (..),
  PathType,
  SOP,
  ProdOnly,
  SumOnly,
  SumPath,
  ProdPath,
  FactorsOf,
  FactorOfF,
  KnownPath (..),
  PositionOf,
  PositionsOf,
  PositionOfF,
  PositionOf',
  module GHC.Generics,
) where

import Data.Kind
import Data.Proxy
import Data.TypeLevel.Applicative
import Data.TypeLevel.Function
import GHC.Generics hiding (S)
import GHC.TypeLits

data PathSpec = PathType Bool Bool
  deriving (Read, Show, Eq, Ord)

type PathType = 'PathType

type SOP = 'PathType 'True 'True

type ProdOnly = 'PathType 'False 'True

type SumOnly = 'PathType 'True 'False

type SumPath = Path' SumOnly

type ProdPath = Path' ProdOnly

type Path = Path' SOP

data Path' (t :: PathSpec) c (f :: Type -> Type) where
  K :: Path' t c (K1 i c)
  M :: Path' t c f -> Path' t c (M1 i x f)
  InL :: Path' (PathType 'True b) c f -> Path' (PathType 'True b) c (f :+: g)
  InR :: Path' (PathType 'True b) c g -> Path' (PathType 'True b) c (f :+: g)
  GoL :: Path' (PathType b 'True) c f -> Path' (PathType b 'True) c (f :*: g)
  GoR :: Path' (PathType b 'True) c g -> Path' (PathType b 'True) c (f :*: g)

deriving instance Show (Path' t c f)

type family PositionOf' t a f :: Maybe (Path' t a f) where
  PositionOf' t a f = PositionOfF Maybe t a f

type family PositionsOf t a f :: [Path' t a f] where
  PositionsOf t a f = PositionOfF [] t a f

type PositionOfF ::
  forall (p :: Type -> Type) ->
  forall (t :: PathSpec) ->
  forall (a :: Type) ->
  forall (f :: Type -> Type) ->
  p (Path' t a f)
type family PositionOfF p t (a :: Type) (f :: Type -> Type) :: p (Path' t a f) where
  PositionOfF p _ a (K1 i a) = Pure 'K
  PositionOfF p t a (M1 i c f) = Con 'M <$> PositionOfF p t a f
  PositionOfF p (PathType 'True b) a (l :+: r) =
    (Con 'InL <$> PositionOfF p (PathType 'True b) a l)
      <|> (Con 'InR <$> PositionOfF p (PathType 'True b) a r)
  PositionOfF p (PathType b 'True) a (l :*: r) =
    (Con 'GoL <$> PositionOfF p (PathType b 'True) a l)
      <|> (Con 'GoR <$> PositionOfF p (PathType b 'True) a r)
  PositionOfF _ _ _ _ = Empty

class KnownPath t c f (p :: Path' t c f) where
  pathVal :: proxy p -> Path' t c f

instance KnownPath t c (K1 i c) 'K where
  pathVal _ = K

instance (KnownPath t a f p) => KnownPath t a (M1 i c f) ('M p) where
  pathVal _ = M $ pathVal (Proxy :: Proxy p)

instance
  {-# OVERLAPPING #-}
  (KnownPath (PathType 'True b) a l p) =>
  KnownPath (PathType 'True b) a (l :+: r) ('InL p)
  where
  pathVal _ = InL $ pathVal @(PathType 'True b) (Proxy :: Proxy p)

instance
  {-# OVERLAPPING #-}
  (KnownPath (PathType 'True b) a r p) =>
  KnownPath (PathType 'True b) a (l :+: r) ('InR p)
  where
  pathVal _ = InR $ pathVal @(PathType 'True b) (Proxy :: Proxy p)

instance
  (KnownPath (PathType b 'True) a l p) =>
  KnownPath (PathType b 'True) a (l :*: r) ('GoL p)
  where
  pathVal _ = GoL $ pathVal @(PathType b 'True) (Proxy :: Proxy p)

instance
  (KnownPath (PathType b 'True) a r p) =>
  KnownPath (PathType b 'True) a (l :*: r) ('GoR p)
  where
  pathVal _ = GoR $ pathVal @(PathType b 'True) (Proxy :: Proxy p)

type PositionOf ::
  forall (t :: PathSpec) ->
  forall (a :: Type) ->
  forall (b :: Type) ->
  Maybe (Path' t a (Rep b))
type family PositionOf t a b :: Maybe (Path' t a (Rep b)) where
  PositionOf t a b = PositionOf' t a (Rep b)

type FactorsOf a = FactorOfF [] (Rep a)

type family FactorOfF p a :: p Type where
  FactorOfF p (K1 i c) = Pure c
  FactorOfF p U1 = Empty
  FactorOfF p (M1 i c f) = FactorOfF p f
  FactorOfF p (f :*: g) = FactorOfF p f <|> FactorOfF p g
  FactorOfF p (f :+: g) =
    TypeError ('Text "Cannot define a factor of sum types")
