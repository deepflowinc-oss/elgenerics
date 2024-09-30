{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TypeLevel.Foldable where

import Data.TypeLevel.Applicative
import Data.TypeLevel.Function
import Data.TypeLevel.Monoid

class PFoldable f where
  type FoldMap (fun :: a ~> w) (c :: f a) :: w
  type Fold (ws :: f w) :: w
  type Fold ws = FoldMap Id1 ws

class (PFunctor t, PFoldable t) => PTraversable t where
  type Traverse (fun :: a ~> f b) (arg :: t a) :: f (t b)

instance PFoldable [] where
  type FoldMap fun c = FoldMapList fun c

type family FoldMapList (f :: k ~> w) (as :: [k]) where
  FoldMapList _ '[] = Mempty
  FoldMapList f (x ': xs) = Apply f x <> FoldMapList f xs
